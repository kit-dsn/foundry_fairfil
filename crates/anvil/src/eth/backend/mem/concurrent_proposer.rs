use std::{collections::HashMap, ops::Rem, sync::Arc};

use crate::eth::{
    backend::{
        db::StateDb,
        env::Env,
        executor::TransactionExecutionOutcome,
        mem::{
            Backend, TransactionAccessSimulationResult, batching::SimulationExecutionState,
            inspector::AnvilInspector, storage::MinedBlockOutcome,
        },
        validate::TransactionValidator,
    },
    error::BlockchainError,
    pool::transactions::PoolTransaction,
};
use alloy_evm::Evm;
use alloy_primitives::{
    FixedBytes, U256,
    map::foldhash::{HashSet, HashSetExt},
};
use anvil_core::eth::transaction::{PendingTransaction, TypedTransaction};
use revm::{
    DatabaseCommit,
    context::{Transaction, result::EVMError},
    database::CacheDB,
    primitives::hardfork::SpecId,
};
use serde::Serialize;

#[derive(Debug, Serialize)]
pub struct CommonAggregationOutput {
    /// The block (number) that was mined
    pub block_number: u64,
    /// the mined block
    pub block: MinedBlockOutcome,
    /// simulation of all included transactions
    pub block_sim: Vec<TransactionAccessSimulationResult>,
    /// transaction (hashes) that failed and were not included into the block
    pub failed_transactions: Vec<(FixedBytes<32>, TransactionExecutionOutcome)>,
    /// distribution of gas usage per batch (proposer)
    pub priority_fees_per_proposer: Vec<U256>,
}

#[derive(Debug, Serialize)]
pub struct CyclingHighestOutput {
    /// The block (number) that was mined
    pub block_number: u64,
    /// the mined block
    pub block: MinedBlockOutcome,
    /// simulation of all included transactions
    pub block_sim: Vec<TransactionAccessSimulationResult>,
    /// transaction (hashes) that failed and were not included into the block
    pub failed_transactions: Vec<(FixedBytes<32>, TransactionExecutionOutcome)>,
    /// distribution of gas usage per batch (proposer)
    pub gas_usage_per_batch: HashMap<usize, u128>,
}

impl Backend {
    pub async fn concurrent_proposers_strict_cycling(
        &self,
        mut batches: Vec<Vec<PendingTransaction>>,
    ) -> Result<CommonAggregationOutput, BlockchainError> {
        // create a SimulationExecutionState with disabled priority fee transfers
        let mut exec_state =
            SimulationExecutionState::new(&self).await?.disable_priority_fee_transfer();

        // ensure that all batches are valid, i.e., executable
        for (batch_idx, batch) in batches.iter().enumerate() {
            // Simulate the batch
            let (res, e) = {
                let block_gas_limit = exec_state.gas_limit();
                exec_state
                    .simulate_transactions_with_limit(
                        batch.clone(),
                        block_gas_limit / (batches.len() as u64) * 5,
                    )
                    .await
            };

            if let Ok(batch_sim) = res {
                // reject if batch is invalid
                if batch_sim.iter().any(|s| s.errors.len() > 0) {
                    return Err(BlockchainError::Message(format!("batch {} invalid", batch_idx)));
                }
            }

            exec_state = e; // simulate_transaction takes ownership and returns exec state
        }

        // contains the transactions of the superblock
        let mut block: Vec<Arc<PoolTransaction>> = vec![];
        // map of all seen transactions and the amount of gas used
        let mut seen_txs: HashSet<FixedBytes<32>> = HashSet::new();
        let mut priority_fees_per_batch = vec![U256::ZERO; batches.len()];
        let mut failing_transactions: Vec<(FixedBytes<32>, TransactionExecutionOutcome)> = vec![];

        // the batch index which will include the next transaction
        let mut next_batch_index = 0;
        loop {
            // in all batches, remove all transactions that are already included into the block
            batches.iter_mut().for_each(|batch| {
                let mut split_idx = batch.len();
                for (idx, tx) in batch.iter().enumerate() {
                    if !seen_txs.contains(tx.hash()) {
                        // the transaction at position idx is not already included
                        // remove the previous transactions from the batch
                        split_idx = idx;
                        break;
                    }
                }
                if split_idx == batch.len() {
                    *batch = vec![];
                } else {
                    *batch = batch.split_off(split_idx);
                }
            });

            // grap the transaction from currentBatchIndex and increment the index
            let (winner, winner_batch_index) = {
                let mut selected_index = next_batch_index;
                let mut tx = batches.get(next_batch_index).unwrap().get(0);
                next_batch_index = (next_batch_index + 1) % batches.len();

                while tx.is_none() && batches.iter().any(|b| b.len() > 0) {
                    selected_index = next_batch_index;
                    tx = batches.get(next_batch_index).unwrap().get(0);
                    next_batch_index = (next_batch_index + 1) % batches.len();
                }
                (tx, selected_index)
            };

            match winner {
                None => {
                    // no more transactions left, break out of the loop
                    break;
                }
                Some(tx) => {
                    // try to execute the transaction
                    let tx_hash: FixedBytes<32> = *tx.hash();
                    let tx_arc = Arc::new(tx.clone());

                    let mut errors = exec_state.check_includability(tx_arc.clone());
                    if errors.len() == 0 {
                        // transaction is includable!
                        let (_, tx_reward) =
                            exec_state.execute_transaction(Arc::new(tx.clone())).unwrap();

                        block.push(Arc::new(PoolTransaction::new(tx.clone())));
                        seen_txs.insert(tx_hash);

                        // strict rewarding:
                        // if the batch proposer whose batch index matches the transaction hash has
                        // inserted the transaction, they will receive the rewards.
                        // otherwise, the other batch proposer will only receive the rewards if the
                        // responsible batch proposer did not include the transaction
                        let attributed_batch_index = {
                            let hash_as_number: U256 = tx_hash.into();
                            let responsible_batch_index: U256 =
                                hash_as_number.rem(U256::from(batches.len()));

                            if batches[responsible_batch_index.to::<usize>()]
                                .iter()
                                .any(|t| *t.hash() == tx_hash)
                            {
                                // the transaction appears in the batch responsible for it.
                                // we don't need to reference the original input batch
                                // as if the tx was already removed from a batch, it has
                                // already been processed and we only process each tx once (at most)
                                responsible_batch_index.to::<usize>()
                            } else {
                                winner_batch_index
                            }
                        };

                        priority_fees_per_batch[attributed_batch_index] += tx_reward;
                    } else {
                        // transaction is not includable
                        // shortcut: mark as 'seen' with gas usage 0
                        seen_txs.insert(tx_hash);
                        failing_transactions.push((
                            tx_hash,
                            errors
                                .remove(0)
                                .into_outcome(Arc::new(PoolTransaction::new(tx.clone()))),
                        ));
                    }
                }
            }
        }

        // run a simulation of the block
        let block_simulation = self
            .simulate_transaction_state_access(
                block
                    .iter()
                    .map(|t| t.pending_transaction.transaction.transaction.clone())
                    .collect(),
            )
            .await?;

        // actually build the new block
        let mined_block_outcome = self.do_mine_block(block).await;

        Ok(CommonAggregationOutput {
            block_number: mined_block_outcome.block_number,
            block: mined_block_outcome,
            block_sim: block_simulation,
            failed_transactions: failing_transactions,
            priority_fees_per_proposer: priority_fees_per_batch,
        })
    }

    pub async fn concurrent_proposers_cycling(
        &self,
        mut batches: Vec<Vec<PendingTransaction>>,
    ) -> Result<CommonAggregationOutput, BlockchainError> {
        // create a SimulationExecutionState with disabled priority fee transfers
        let mut exec_state =
            SimulationExecutionState::new(&self).await?.disable_priority_fee_transfer();

        // ensure that all batches are valid, i.e., executable
        for (batch_idx, batch) in batches.iter().enumerate() {
            // Simulate the batch
            let (res, e) = {
                let block_gas_limit = exec_state.gas_limit();
                exec_state
                    .simulate_transactions_with_limit(
                        batch.clone(),
                        block_gas_limit / (batches.len() as u64) * 5,
                    )
                    .await
            };

            if let Ok(batch_sim) = res {
                // reject if batch is invalid
                if batch_sim.iter().any(|s| s.errors.len() > 0) {
                    return Err(BlockchainError::Message(format!("batch {} invalid", batch_idx)));
                }
            }

            exec_state = e; // simulate_transaction takes ownership and returns exec state
        }

        // contains the transactions of the superblock
        let mut block: Vec<Arc<PoolTransaction>> = vec![];
        // map of all seen transactions and the amount of gas used
        let mut seen_txs: HashSet<FixedBytes<32>> = HashSet::new();
        let mut priority_fees_per_batch = vec![U256::ZERO; batches.len()];
        let mut failing_transactions: Vec<(FixedBytes<32>, TransactionExecutionOutcome)> = vec![];

        // the batch index which will include the next transaction
        let mut next_batch_index = 0;
        loop {
            // in all batches, remove all transactions that are already included into the block
            batches.iter_mut().for_each(|batch| {
                let mut split_idx = batch.len();
                for (idx, tx) in batch.iter().enumerate() {
                    if !seen_txs.contains(tx.hash()) {
                        // the transaction at position idx is not already included
                        // remove the previous transactions from the batch
                        split_idx = idx;
                        break;
                    }
                }
                if split_idx == batch.len() {
                    *batch = vec![];
                } else {
                    *batch = batch.split_off(split_idx);
                }
            });

            // grap the transaction from currentBatchIndex and increment the index
            let (winner, winner_batch_index) = {
                let mut selected_index = next_batch_index;
                let mut tx = batches.get(next_batch_index).unwrap().get(0);
                next_batch_index = (next_batch_index + 1) % batches.len();

                while tx.is_none() && batches.iter().any(|b| b.len() > 0) {
                    selected_index = next_batch_index;
                    tx = batches.get(next_batch_index).unwrap().get(0);
                    next_batch_index = (next_batch_index + 1) % batches.len();
                }
                (tx, selected_index)
            };

            match winner {
                None => {
                    // no more transactions left, break out of the loop
                    break;
                }
                Some(tx) => {
                    // try to execute the transaction
                    let tx_hash = *tx.hash();
                    let tx_arc = Arc::new(tx.clone());

                    let mut errors = exec_state.check_includability(tx_arc.clone());
                    if errors.len() == 0 {
                        // transaction is includable!
                        let (_, tx_reward) =
                            exec_state.execute_transaction(Arc::new(tx.clone())).unwrap();

                        block.push(Arc::new(PoolTransaction::new(tx.clone())));
                        seen_txs.insert(tx_hash);

                        // the winning batch receives the rewards
                        priority_fees_per_batch[winner_batch_index] += tx_reward;
                    } else {
                        // transaction is not includable
                        // shortcut: mark as 'seen' with gas usage 0
                        seen_txs.insert(tx_hash);
                        failing_transactions.push((
                            tx_hash,
                            errors
                                .remove(0)
                                .into_outcome(Arc::new(PoolTransaction::new(tx.clone()))),
                        ));
                    }
                }
            }
        }

        // run a simulation of the block
        let block_simulation = self
            .simulate_transaction_state_access(
                block
                    .iter()
                    .map(|t| t.pending_transaction.transaction.transaction.clone())
                    .collect(),
            )
            .await?;

        // actually build the new block
        let mined_block_outcome = self.do_mine_block(block).await;

        Ok(CommonAggregationOutput {
            block_number: mined_block_outcome.block_number,
            block: mined_block_outcome,
            block_sim: block_simulation,
            failed_transactions: failing_transactions,
            priority_fees_per_proposer: priority_fees_per_batch,
        })
    }

    pub async fn concurrent_proposers_common_cycling_highest(
        &self,
        mut batches: Vec<Vec<PendingTransaction>>,
    ) -> Result<CommonAggregationOutput, BlockchainError> {
        // create a SimulationExecutionState with disabled priority fee transfers
        let mut exec_state =
            SimulationExecutionState::new(&self).await?.disable_priority_fee_transfer();

        // ensure that all batches are valid, i.e., executable
        for (batch_idx, batch) in batches.iter().enumerate() {
            // Simulate the batch
            let (res, e) = {
                let block_gas_limit = exec_state.gas_limit();
                exec_state
                    .simulate_transactions_with_limit(
                        batch.clone(),
                        block_gas_limit / (batches.len() as u64) * 5,
                    )
                    .await
            };

            if let Ok(batch_sim) = res {
                // reject if batch is invalid
                if batch_sim.iter().any(|s| s.errors.len() > 0) {
                    return Err(BlockchainError::Message(format!("batch {} invalid", batch_idx)));
                }
            }

            exec_state = e; // simulate_transaction takes ownership and returns exec state
        }

        // contains the transactions of the superblock
        let mut block: Vec<Arc<PoolTransaction>> = vec![];
        // map of all seen transactions and the amount of gas used
        let mut seen_txs: HashMap<FixedBytes<32>, u64> = HashMap::new();
        let mut gas_contributed = vec![0 as u64; batches.len()];

        let mut failing_transactions: Vec<(FixedBytes<32>, TransactionExecutionOutcome)> = vec![];

        loop {
            // in all batches, remove all transactions that are already included into the block
            batches.iter_mut().enumerate().for_each(|(batch_idx, batch)| {
                let mut split_idx = batch.len();
                for (idx, tx) in batch.iter().enumerate() {
                    if !seen_txs.contains_key(tx.hash()) {
                        // the transaction at position idx is not already included
                        // remove the previous transactions from the batch
                        split_idx = idx;
                        break;
                    } else {
                        // the transaction is alredy included, batch proposer gets the gas used attributed
                        gas_contributed[batch_idx] = gas_contributed[batch_idx]
                            .saturating_add(*seen_txs.get(tx.hash()).unwrap());
                    }
                }
                if split_idx == batch.len() {
                    *batch = vec![];
                } else {
                    *batch = batch.split_off(split_idx);
                }
            });

            // grap the transaction with the highest gas price
            let winner = batches.iter().map(|x| x.get(0)).filter_map(|x| x).max_by_key(|t| {
                t.to_revm_tx_env().effective_gas_price(exec_state.base_fee() as u128)
            });

            match winner {
                None => {
                    // no more transactions left, break out of the loop
                    break;
                }
                Some(tx) => {
                    // try to execute the transaction
                    let tx_hash = *tx.hash();
                    let tx_arc = Arc::new(tx.clone());

                    let mut errors = exec_state.check_includability(tx_arc.clone());
                    if errors.len() == 0 {
                        // transaction is includable!
                        let (r, _) = exec_state.execute_transaction(Arc::new(tx.clone())).unwrap();

                        let tx_gas_used = r.result.gas_used();
                        block.push(Arc::new(PoolTransaction::new(tx.clone())));
                        seen_txs.insert(tx_hash, tx_gas_used);

                        // attribute all proposers whose head transaction is the executed transaction
                        // with the amount of gas contibuted
                        batches
                            .iter()
                            .enumerate()
                            .map(|(batch_idx, batch)| (batch_idx, batch.get(0)))
                            .filter(|(_, opt_head)| {
                                if let Some(head) = opt_head {
                                    *head.hash() == tx_hash
                                } else {
                                    false
                                }
                            })
                            .for_each(|(batch_idx, _)| {
                                gas_contributed[batch_idx] =
                                    gas_contributed[batch_idx].saturating_add(tx_gas_used);
                            });
                    } else {
                        // transaction is not includable
                        // shortcut: mark as 'seen' with gas usage 0
                        seen_txs.insert(tx_hash, 0);
                        failing_transactions.push((
                            tx_hash,
                            errors
                                .remove(0)
                                .into_outcome(Arc::new(PoolTransaction::new(tx.clone()))),
                        ));
                    }

                    // remove the transaction from the head of all stacks
                    batches.iter_mut().for_each(|batch| {
                        if let Some(head) = batch.get(0)
                            && *head.hash() == tx_hash
                        {
                            batch.remove(0);
                        }
                    });
                }
            }
        }

        // run a simulation of the block
        let block_simulation = self
            .simulate_transaction_state_access(
                block
                    .iter()
                    .map(|t| t.pending_transaction.transaction.transaction.clone())
                    .collect(),
            )
            .await?;

        // actually build the new block
        let mined_block_outcome = self.do_mine_block(block).await;

        // build hashmap of gas_usage
        let mut gas_usage_per_batch = HashMap::new();
        gas_contributed.iter().enumerate().for_each(|(batch_idx, gas)| {
            gas_usage_per_batch.insert(batch_idx, *gas as u128);
        });

        let prio_fee_per_batch: Vec<U256> = {
            // calculate total priority fees
            let total_prio_fees = block_simulation
                .iter()
                .map(|sim| sim.priority_fee)
                .fold(U256::ZERO, |acc, v| acc.saturating_add(v));

            // let gas_contributed_cap = (2 * exec_state.gas_limit()) / (batches.len() as u64);
            // let contrib: Vec<u64> =
            //     gas_contributed.iter().map(|gas| (*gas).min(gas_contributed_cap)).collect();

            let contrib = gas_contributed;

            let contrib_sum: u64 = contrib.iter().sum();

            contrib
                .iter()
                .map(|contributed| {
                    total_prio_fees
                        .checked_mul(U256::from(*contributed))
                        .unwrap()
                        .wrapping_div(U256::from(contrib_sum))
                })
                .collect()
        };

        Ok(CommonAggregationOutput {
            block_number: mined_block_outcome.block_number,
            block: mined_block_outcome,
            block_sim: block_simulation,
            failed_transactions: failing_transactions,
            priority_fees_per_proposer: prio_fee_per_batch,
        })
    }

    pub async fn concurrent_proposers_cycling_highest(
        &self,
        mut batches: Vec<Vec<TypedTransaction>>,
    ) -> Result<CyclingHighestOutput, BlockchainError> {
        // ensure that all batches are valid, i.e., executable
        for (batch_idx, batch) in batches.iter().enumerate() {
            if !self.test_batch(batch.to_vec()).await? {
                // there is one invalid batch
                return Err(BlockchainError::Message(format!("batch {} invalid", batch_idx)));
            }
        }

        let number_batches = batches.len() as u64; // number of batches = batch proposers

        // let's build the block!

        // contains the transactions of the superblock
        let mut block: Vec<TypedTransaction> = vec![];
        // map of all included transactions and the amount of gas used
        let mut included_txs: HashMap<FixedBytes<32>, u64> = HashMap::new();
        // maps each batch proposer to the amount of gas it has 'contributed' to (actual gas usage, not gas limit)!
        let mut gas_usage_per_proposer: HashMap<usize, u128> = HashMap::new();
        // running value for block gas usage
        let mut gas_used = 0 as u64;
        // running value for block blob gas usage
        let mut blob_gas_used = 0 as u64;

        // list of failing transactions with reason
        let mut failing_tx: Vec<(FixedBytes<32>, TransactionExecutionOutcome)> = vec![];

        let (evm_env, mut evm_db) = self.build_evm_environment().await?;

        loop {
            batches = cleanup_batches_for_inclusion(batches, &included_txs);

            let heads = get_heads(
                &batches,
                &gas_usage_per_proposer,
                (evm_env.evm_env.block_env.gas_limit / 4 / number_batches) as u128,
            );
            if heads.is_empty() {
                break;
            }

            // the next transaction is the transaction with the highest effective gas price
            // if multiple transactions fullfil this criteria, `max_by_key` takes the last one
            // i.e., from the highest batch proposer
            let winner = heads.iter().max_by_key(|(_, t)| {
                // get the effective gas price of transactions
                PendingTransaction::new((*t).clone())
                    .unwrap()
                    .to_revm_tx_env()
                    .effective_gas_price(evm_env.evm_env.block_env.basefee as u128)
            });

            match winner {
                None => {
                    // no more transactions left, break out of the loop
                    break;
                }
                Some((batch, tx)) => {
                    // let's try to run that transaction!

                    let pending_tx = PendingTransaction::new(tx.clone()).unwrap();

                    // check includability
                    let max_block_gas = gas_used.saturating_add(pending_tx.transaction.gas_limit());
                    if max_block_gas > evm_env.evm_env.block_env.gas_limit {
                        // transaction cannot be included because of block gas limit

                        // insert the transaction to `included_txs` so that it gets cleaned up
                        // in all batches in the next loop
                        included_txs.insert(*pending_tx.hash(), 0);
                        failing_tx.push((
                            *pending_tx.hash(),
                            TransactionExecutionOutcome::BlockGasExhausted(Arc::new(
                                PoolTransaction::new(pending_tx),
                            )),
                        ));
                        continue;
                    }

                    let max_blob_gas = blob_gas_used
                        .saturating_add(pending_tx.transaction.blob_gas().unwrap_or(0));
                    if max_blob_gas > self.blob_params().max_blob_gas_per_block() {
                        // transaction cannot be included because of blob gas limit

                        // insert the transaction to `included_txs` so that it gets cleaned up
                        // in all batches in the next loop
                        included_txs.insert(*pending_tx.hash(), 0);
                        failing_tx.push((
                            *pending_tx.hash(),
                            TransactionExecutionOutcome::BlobGasExhausted(Arc::new(
                                PoolTransaction::new(pending_tx),
                            )),
                        ));
                        continue;
                    }

                    // perform validity checks
                    let sender_acc =
                        evm_db.load_account(*pending_tx.sender()).expect("could not load account");
                    let valid =
                        self.validate_pool_transaction_for(&pending_tx, &sender_acc.info, &evm_env);
                    if let Err(e) = valid {
                        // transaction is not includable (anymore)

                        // insert the transaction to `included_txs` so that it gets cleaned up
                        // in all batches in the next loop
                        included_txs.insert(*pending_tx.hash(), 0);
                        failing_tx.push((
                            *pending_tx.hash(),
                            TransactionExecutionOutcome::Invalid(
                                Arc::new(PoolTransaction::new(pending_tx)),
                                e,
                            ),
                        ));
                        continue;
                    }

                    // execute transaction
                    let mut inspector = AnvilInspector::default();
                    let mut evm =
                        self.new_evm_with_inspector_ref(&evm_db, &evm_env, &mut inspector);
                    let transact_res = evm.transact(pending_tx.to_revm_tx_env());
                    match transact_res {
                        Err(e) => {
                            // failed!
                            included_txs.insert(*pending_tx.hash(), 0);

                            match e {
                                EVMError::Database(err) => {
                                    failing_tx.push((
                                        *pending_tx.hash(),
                                        TransactionExecutionOutcome::DatabaseError(
                                            Arc::new(PoolTransaction::new(pending_tx)),
                                            err,
                                        ),
                                    ));
                                }
                                EVMError::Transaction(err) => {
                                    failing_tx.push((
                                        *pending_tx.hash(),
                                        TransactionExecutionOutcome::Invalid(
                                            Arc::new(PoolTransaction::new(pending_tx)),
                                            err.into(),
                                        ),
                                    ));
                                }
                                // This will correspond to prevrandao not set, and it should never happen.
                                // If it does, it's a bug.
                                e => panic!("failed to execute transaction: {e}"),
                            }
                        }
                        Ok(result_state) => {
                            // we executed the transaction successfully!

                            // commit transaction
                            block.push(tx.clone());
                            evm_db.commit(result_state.state);

                            // include it into set of included txs with gas used
                            included_txs.insert(*pending_tx.hash(), result_state.result.gas_used());

                            // update block variables
                            gas_used = gas_used.saturating_add(result_state.result.gas_used());
                            blob_gas_used = blob_gas_used
                                .saturating_add(pending_tx.transaction.blob_gas().unwrap_or(0));

                            // for the winning batch increase their gas usage
                            let batch_gas_entry = gas_usage_per_proposer.entry(*batch).or_insert(0);
                            *batch_gas_entry = batch_gas_entry
                                .saturating_add(result_state.result.gas_used() as u128);
                        }
                    }
                }
            }
        }

        let pool_transactions: Vec<Arc<PoolTransaction>> = block
            .iter()
            .map(|t| Arc::new(PoolTransaction::new(PendingTransaction::new(t.clone()).unwrap())))
            .collect();

        // run a simulation of the block
        let block_simulation = self.simulate_transaction_state_access(block).await?;

        // actually build the new block
        let mined_block_outcome = self.do_mine_block(pool_transactions).await;

        Ok(CyclingHighestOutput {
            block_number: mined_block_outcome.block_number,
            block: mined_block_outcome,
            block_sim: block_simulation,
            failed_transactions: failing_tx,
            gas_usage_per_batch: gas_usage_per_proposer,
        })
    }

    async fn test_batch(&self, batch: Vec<TypedTransaction>) -> Result<bool, BlockchainError> {
        let batch_result = self.simulate_transaction_state_access(batch).await?;

        for tx_result in batch_result {
            if !tx_result.errors.is_empty() {
                return Ok(false);
            }
        }

        Ok(true)
    }

    pub async fn build_evm_environment(&self) -> Result<(Env, CacheDB<StateDb>), BlockchainError> {
        let db = self.db.read().await;
        let mut cache_db = CacheDB::new(db.current_state());

        let mut env = self.env.read().clone();

        env.evm_env.block_env.basefee = self.base_fee();
        env.evm_env.block_env.blob_excess_gas_and_price = self.excess_blob_gas_and_price();
        env.evm_env.block_env.number = env.evm_env.block_env.number.saturating_add(U256::from(1));

        // disable nonce checks
        // env.evm_env.cfg_env.disable_nonce_check = false;

        // disable balance checks
        // env.evm_env.cfg_env.disable_balance_check = false;

        if self.fetch_mix_hash {
            env.evm_env.block_env.prevrandao = self
                .get_fork()
                .unwrap()
                .block_by_number(self.best_number() + 1)
                .await
                .unwrap()
                .unwrap()
                .header
                .mix_hash;
        }

        if self.fetch_block_gas_limit {
            env.evm_env.block_env.gas_limit = self
                .get_fork()
                .unwrap()
                .block_by_number(self.best_number() + 1)
                .await
                .unwrap()
                .unwrap()
                .header
                .gas_limit;
        }

        if self.fetch_block_coinbase {
            env.evm_env.block_env.beneficiary = self
                .get_fork()
                .unwrap()
                .block_by_number(self.best_number() + 1)
                .await
                .unwrap()
                .unwrap()
                .header
                .beneficiary;
        }

        let parent_beacon_root = if self.fetch_parent_beacon_root {
            let parent_beacon_root = self
                .get_fork()
                .unwrap()
                .block_by_number(self.best_number() + 1)
                .await
                .unwrap()
                .unwrap()
                .header
                .parent_beacon_block_root;
            parent_beacon_root
        } else {
            None
        };

        if self.exact_block_timestamps {
            // Ensure that the mined block is exactly 12s after the previous one
            let prev_block = self.block_by_hash(self.best_hash()).await.unwrap().unwrap();
            env.evm_env.block_env.timestamp = U256::from(prev_block.header.timestamp + 12);
        } else if self.fetch_block_timestamps {
            env.evm_env.block_env.timestamp = U256::from(
                self.get_fork()
                    .unwrap()
                    .block_by_number(self.best_number() + 1)
                    .await
                    .unwrap()
                    .unwrap()
                    .header
                    .timestamp,
            );
        } else {
            // finally set the next block timestamp, this is done just before execution, because
            // there can be concurrent requests that can delay acquiring the db lock and we want
            // to ensure the timestamp is as close as possible to the actual execution.
            env.evm_env.block_env.timestamp = U256::from(self.time.next_timestamp());
        }

        let mut inspector = self.build_inspector();
        let mut evm = self.new_evm_with_inspector_ref(&cache_db, &env, &mut inspector);

        // Do EIP-4788
        if env.evm_env.cfg_env.spec >= SpecId::CANCUN && parent_beacon_root.is_some() {
            let eip4788_result = evm.transact_system_call(
                alloy_eips::eip4788::SYSTEM_ADDRESS,
                alloy_eips::eip4788::BEACON_ROOTS_ADDRESS,
                parent_beacon_root.unwrap().into(),
            )?;

            cache_db.commit(eip4788_result.state);
        }

        Ok((env, cache_db))
    }
}

// Given a set of (remaining) transactions for each batch, get a vector of the current 'heads' (i.e., front transactions of each batch)
// Additionally, if a proposer has already reached the `batch_limit`, their head is not considered anymore, except if all proposers reached the `batch_limit` or are otherwise empty
fn get_heads(
    batches: &Vec<Vec<TypedTransaction>>,
    gas_usage: &HashMap<usize, u128>,
    batch_limit: u128,
) -> Vec<(usize, TypedTransaction)> {
    let mut primary = vec![]; // contains heads of batches not reaching the gas limit
    let mut secondary = vec![]; // contains heads of all batches

    for (batch_idx, batch) in batches.iter().enumerate() {
        if !batch.is_empty() {
            // only if the batch proposer has not yet reached their gas limit,
            // include it to the primary result
            if *gas_usage.get(&batch_idx).unwrap_or(&(0 as u128)) < batch_limit {
                primary.push((batch_idx, batch[0].clone()));
            }
            secondary.push((batch_idx, batch[0].clone()))
        }
    }

    if !primary.is_empty() { primary } else { secondary }
}

/// Iterate over the batches and remove those transactions at the beginning which are contained in the hashset.
/// Additionally, it increments the `gas_usage` hash map for those proposers who included that transaction
fn cleanup_batches_for_inclusion(
    batches: Vec<Vec<TypedTransaction>>,
    included: &HashMap<FixedBytes<32>, u64>,
) -> Vec<Vec<TypedTransaction>> {
    let mut res = vec![];
    for batch in batches.iter() {
        let mut has_remaining_transactions = false;
        for (idx, tx) in batch.iter().enumerate() {
            if !included.contains_key(&tx.hash()) {
                // this transaction is not already included
                res.push(batch.clone().split_off(idx));
                has_remaining_transactions = true;
                break;
            }
        }

        // all transactions are already included into aggregated block
        if !has_remaining_transactions {
            res.push(vec![]);
        }
    }

    res
}
