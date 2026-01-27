use std::collections::{HashMap, HashSet};
use std::sync::Arc;

use alloy_evm::Evm;
use alloy_primitives::aliases::I512;
use alloy_primitives::{Address, FixedBytes, TxHash, U256};
use anvil_core::eth::transaction::PendingTransaction;
use itertools::Itertools;
use revm::DatabaseCommit;
use revm::{context::result::EVMError, database::CacheDB};
use revm_inspectors::tracing::types::StorageChange;

use crate::eth::backend::mem::transaction_register::TransactionRegister;
use crate::eth::backend::mem::{DatabaseRef, TransactionAccessSimulationResult};
use crate::eth::error::InvalidTransactionError;
use crate::eth::{
    backend::{
        db::StateDb,
        env::Env,
        executor::{TransactionExecutionOutcome, new_evm_with_inspector_ref},
        mem::{
            Backend, SimulationError, inspector::AnvilInspector, validate_transation_includability,
        },
    },
    error::BlockchainError,
    pool::transactions::PoolTransaction,
};

pub async fn build_batch(
    register: &TransactionRegister,
    backend: &Backend,
    bucket: Vec<TxHash>,
    sim_state: Box<SimulationExecutionState>,
) -> (Vec<TxHash>, Box<SimulationExecutionState>) {
    inner_build_batch(register, backend, bucket, sim_state, &Vec::new()).await
}

pub async fn build_extended_batch(
    register: &TransactionRegister,
    backend: &Backend,
    bucket: Vec<TxHash>,
    sim_state: Box<SimulationExecutionState>,
    primary_batch: &Vec<TxHash>,
) -> (Vec<TxHash>, Box<SimulationExecutionState>) {
    inner_build_batch(register, backend, bucket, sim_state, primary_batch).await
}

async fn inner_build_batch(
    register: &TransactionRegister,
    backend: &Backend,
    bucket: Vec<TxHash>,
    mut sim_state: Box<SimulationExecutionState>,
    already_included: &Vec<TxHash>,
) -> (Vec<TxHash>, Box<SimulationExecutionState>) {
    let mut includable = vec![];
    let mut tx_map = HashMap::new();

    // filter out transactions which are not registered
    let restricted_bucket: Vec<TxHash> = bucket.into_iter().filter(|x| register.has(x)).collect();

    // Test if the transactions in the bucket are includable
    for tx_hash in restricted_bucket {
        let sim = {
            if already_included.len() == 0 {
                register.get_simulation(tx_hash, backend).unwrap()
            } else {
                let (s, _sim_state) =
                    sim_state.simulate_transaction(register.get_pending_tx(&tx_hash)).await;
                sim_state = Box::new(_sim_state);
                Arc::new(s.unwrap())
            }
        };

        if sim.errors.len() == 0 {
            // transaction is (i.G.) includable
            includable.push(tx_hash)
        } else {
            // this transaction has dependencies that we need to find!
            let (dep_repl, dep_map, s) = Box::pin(find_transaction_depencencies(
                tx_hash,
                register,
                backend,
                sim_state,
                HashSet::from_iter(already_included.iter().cloned()),
            ))
            .await;

            includable
                .append(&mut dep_repl.into_iter().filter(|x| !includable.contains(x)).collect());
            tx_map = merge_tx_maps(tx_map, dep_map);

            sim_state = s;
        }
    }

    let mut batch = Vec::new();

    while includable.len() > 0 {
        let winning_tx = includable
            .iter()
            // get tuples of (hash, effective gas price)
            .map(|t| (*t, register.get_simulation(*t, backend).unwrap().effective_gas_price))
            // sort decending by effective gas price
            .sorted_by(|a, b| Ord::cmp(&a.1, &b.1))
            .rev()
            .next()
            .unwrap()
            .0;

        let pending_tx = Arc::new(register.get_pending_tx(&winning_tx));

        // check includability as transactions in the includable set can
        // be in conflict with each other or the block/blob gas limit can run out
        if sim_state.check_includability(pending_tx.clone()).await.len() == 0 {
            // transaction is includable!
            batch.push(winning_tx);
            includable.retain(|x| *x != winning_tx);

            // execute the transaction
            sim_state.execute_transaction(pending_tx.clone()).unwrap();

            // check transaction map to now include transaction that have become includable
            for other_hash in tx_map.get(&winning_tx).unwrap_or(&Vec::new()).clone() {
                if batch.contains(&other_hash) || includable.contains(&other_hash) {
                    // transaction is already included into includable or batch
                    continue;
                }

                if tx_map
                    .iter()
                    .filter(|(x, _)| **x != winning_tx)
                    .any(|(_, list)| list.contains(&other_hash))
                {
                    // there is another transaction map that references other_hash
                    // so other_hash requires that the another transaction is included into here
                    // too.
                    continue;
                }

                // simulate the new transaction again
                let (other_sim_res, s) =
                    sim_state.simulate_transaction(register.get_pending_tx(&other_hash)).await;

                let other_sim = other_sim_res.unwrap();

                if other_sim.errors.len() == 0 {
                    // tx is now includable!
                    includable.push(other_hash);
                    sim_state = Box::new(s);
                } else {
                    // try finding dependencies again
                    let (dep_repl, dep_map, s) = find_transaction_depencencies(
                        other_hash,
                        register,
                        backend,
                        Box::new(s),
                        HashSet::from_iter(
                            already_included.iter().cloned().chain(batch.iter().cloned()),
                        ),
                    )
                    .await;

                    includable.append(
                        &mut dep_repl.into_iter().filter(|x| !includable.contains(x)).collect(),
                    );
                    tx_map = merge_tx_maps(tx_map, dep_map);

                    sim_state = s;
                }
            }

            // remove the transaction from the transaction dependency map
            tx_map.remove(&winning_tx);
        } else {
            // transaction is no longer includable
            // remove it from includable, but do not append to block
            includable.retain(|x| *x != winning_tx);
        }
    }

    (batch, sim_state)
}

fn merge_tx_maps(
    mut a: HashMap<TxHash, Vec<TxHash>>,
    b: HashMap<TxHash, Vec<TxHash>>,
) -> HashMap<TxHash, Vec<TxHash>> {
    for (k, v) in b.into_iter() {
        let map_entry: &mut Vec<TxHash> = a.entry(k).or_default();
        map_entry.append(&mut v.into_iter().filter(|x| !map_entry.contains(x)).collect());
    }

    a
}

async fn find_transaction_depencencies(
    tx: TxHash,
    register: &TransactionRegister,
    backend: &Backend,
    sim_state: Box<SimulationExecutionState>,
    used: HashSet<TxHash>,
) -> (Vec<TxHash>, HashMap<TxHash, Vec<TxHash>>, Box<SimulationExecutionState>) {
    let (sim_res, mut sim_state) =
        sim_state.simulate_transaction(register.get_pending_tx(&tx)).await;
    let mut sim = sim_res.unwrap();

    if sim.errors.len() == 0 {
        // transaction is includable!
        return (vec![tx], HashMap::new(), Box::new(sim_state));
    } else {
        // transaction is (currently) not includable
        let sim_error = sim.errors.pop().unwrap();

        match sim_error {
            SimulationError::InvalidTransaction(invalid_error) => {
                let mut used_with_tx = used.clone();
                used_with_tx.insert(tx.clone());

                if let InvalidTransactionError::NonceTooHigh = invalid_error {
                    // look for transactions with lower nonces

                    if let Some(other) = register.find_transaction_with_nonce(
                        &sim.sender,
                        sim.nonces_required[0].1 - 1,
                        &used_with_tx,
                    ) {
                        let (o_repl, mut o_map, sim_state) =
                            Box::pin(find_transaction_depencencies(
                                other,
                                register,
                                backend,
                                Box::new(sim_state),
                                used_with_tx,
                            ))
                            .await;

                        o_map.entry(other).or_insert(Vec::new()).push(tx.clone());
                        return (o_repl, o_map, sim_state);
                    } else {
                        // no transaction found
                        return (Vec::new(), HashMap::new(), Box::new(sim_state));
                    }
                } else if let InvalidTransactionError::InsufficientFunds = invalid_error {
                    // look for transactions with transfers to sender

                    let missing_funds = {
                        let balance = sim_state.get_account_balance(&sim.sender);
                        let value = register.get_pending_tx(&tx).transaction.value();
                        let required_funds = U256::from(sim.max_gas_cost) + value;
                        required_funds.checked_sub(balance).unwrap()
                    };

                    let mut found_funds = U256::ZERO;
                    let mut repl = Vec::new();
                    let mut tx_map = HashMap::new();

                    for other in register.find_transaction_paying(&sim.sender, &used_with_tx) {
                        let (other_sim_res, s) =
                            sim_state.simulate_transaction(register.get_pending_tx(&other)).await;

                        let other_sim = other_sim_res.unwrap();

                        if other_sim.transfer_diffs.contains_key(&sim.sender) {
                            let transfer_diff = other_sim.transfer_diffs.get(&sim.sender).unwrap();
                            found_funds = found_funds
                                .saturating_add(U256::from(transfer_diff.unsigned_abs()));

                            let (o_repl, mut o_map, s) = Box::pin(find_transaction_depencencies(
                                other,
                                register,
                                backend,
                                Box::new(s),
                                used_with_tx.clone(),
                            ))
                            .await;

                            repl.append(
                                &mut o_repl.into_iter().filter(|x| !repl.contains(x)).collect(),
                            );

                            o_map.entry(other).or_insert(Vec::new()).push(tx.clone());

                            // merge transaction dependency map
                            tx_map = merge_tx_maps(tx_map, o_map);

                            sim_state = *s;
                        } else {
                            sim_state = s;
                        }

                        if found_funds >= missing_funds {
                            break;
                        }
                    }

                    if found_funds >= missing_funds {
                        return (repl, tx_map, Box::new(sim_state));
                    } else {
                        // did not find enough funds
                        return (Vec::new(), HashMap::new(), Box::new(sim_state));
                    }
                }

                return (Vec::new(), HashMap::new(), Box::new(sim_state));
            }
            SimulationError::BlockGasExhausted | SimulationError::BlockBlobGasExhausted => {
                // at this state, the transaction definetely is no longer includable.
                return (Vec::new(), HashMap::new(), Box::new(sim_state));
            }
        }
    }
}

/// holds an evm environmant to execute and simulate transactions
/// more easily
pub struct SimulationExecutionState {
    env: Env,
    cache_db: CacheDB<StateDb>,
    blob_gas_used: u64,
    blob_gas_limit: u64,
    gas_used: u64,
}

impl SimulationExecutionState {
    /// Build an SimulationExecutionState from the
    /// current state of the backend. The state is ready
    /// to execute transactions as if they were included into a block.
    pub async fn new(backend: &Backend) -> Result<SimulationExecutionState, BlockchainError> {
        let (env, cache_db) = backend.build_evm_environment().await?;

        Ok(SimulationExecutionState {
            env,
            cache_db,
            gas_used: 0,
            blob_gas_used: 0,
            blob_gas_limit: backend.blob_params().max_blob_gas_per_block(),
        })
    }

    /// Returns the gas limit of the block being simulated
    fn gas_limit(&self) -> u64 {
        self.env.evm_env.block_env.gas_limit
    }

    /// Returns the blob gas limit of the block being simulated
    fn blob_gas_limit(&self) -> u64 {
        self.blob_gas_limit
    }

    fn get_account_balance(&mut self, account: &Address) -> U256 {
        self.cache_db.load_account(*account).unwrap().info.balance
    }

    /// Checks transaction includability
    async fn check_includability(&mut self, tx: Arc<PendingTransaction>) -> Vec<SimulationError> {
        let max_blob_gas = self.blob_gas_limit();
        let max_block_gas = self.gas_limit();
        Self::check_includability_inner(
            tx,
            &self.env,
            &mut self.cache_db,
            self.blob_gas_used,
            max_blob_gas,
            self.gas_used,
            max_block_gas,
        )
        .await
    }

    async fn check_includability_inner<ExtDB: DatabaseRef>(
        tx: Arc<PendingTransaction>,
        env: &Env,
        cache_db: &mut CacheDB<ExtDB>,
        blob_gas_used: u64,
        blob_gas_limit: u64,
        gas_used: u64,
        gas_limit: u64,
    ) -> Vec<SimulationError> {
        let sender = cache_db.load_account(*tx.sender()).unwrap();
        let mut errors = validate_transation_includability(&tx, &sender.info, env);

        let max_block_gas = gas_used.saturating_add(tx.transaction.gas_limit());
        if max_block_gas > gas_limit {
            // transaction exceeds block gas limit
            errors.push(SimulationError::BlockGasExhausted);
        }

        let max_blob_gas = blob_gas_used.saturating_add(tx.transaction.blob_gas().unwrap_or(0));
        if max_blob_gas > blob_gas_limit {
            // transaction exceeds block blob gas limit
            errors.push(SimulationError::BlockBlobGasExhausted)
        }

        errors
    }

    pub fn execute_transaction(
        &mut self,
        tx: Arc<PendingTransaction>,
    ) -> Result<(), TransactionExecutionOutcome> {
        let mut inspector = AnvilInspector::default();

        let mut evm = new_evm_with_inspector_ref(&self.cache_db, &self.env, &mut inspector);
        self.env.networks.inject_precompiles(evm.precompiles_mut());

        let transact_res = evm.transact(tx.to_revm_tx_env());

        match transact_res {
            Err(e) => {
                match e {
                    EVMError::Database(err) => {
                        return Err(TransactionExecutionOutcome::DatabaseError(
                            Arc::new(PoolTransaction::new((*tx).clone())),
                            err,
                        ));
                    }
                    EVMError::Transaction(err) => {
                        return Err(TransactionExecutionOutcome::Invalid(
                            Arc::new(PoolTransaction::new((*tx).clone())),
                            err.into(),
                        ));
                    }
                    // This will correspond to prevrandao not set, and it should never happen. If it does, it's a bug.
                    e => panic!("failed to execute transaction: {e}"),
                }
            }
            Ok(result_state) => {
                self.cache_db.commit(result_state.state);

                self.gas_used = self.gas_used.saturating_add(result_state.result.gas_used());
                self.blob_gas_used =
                    self.blob_gas_used.saturating_add(tx.transaction.blob_gas().unwrap_or(0));

                return Ok(());
            }
        }
    }

    pub async fn simulate_transaction(
        self,
        tx: PendingTransaction,
    ) -> (Result<TransactionAccessSimulationResult, BlockchainError>, Self) {
        let (res, s) = self.simulate_transactions(vec![tx]).await;
        match res {
            Ok(mut v) => return (Ok(v.pop().unwrap()), s),
            Err(e) => return (Err(e), s),
        }
    }

    pub async fn simulate_transactions(
        mut self,
        txs: Vec<PendingTransaction>,
    ) -> (Result<Vec<TransactionAccessSimulationResult>, BlockchainError>, Self) {
        let mut env = self.env.clone();

        // running value for block gas usage
        let mut gas_used = 0 as u64;
        let gas_limit = self.gas_limit();
        // running value for block blob gas usage
        let mut blob_gas_used = 0 as u64;

        let mut nested_db = self.cache_db.nest();
        let mut out = vec![];

        // iterate over all transactions and execute them in order
        for tx in txs {
            let tx_hash = tx.hash();

            // perform validity checks
            let errors = Self::check_includability_inner(
                Arc::new(tx.clone()),
                &env,
                &mut nested_db,
                blob_gas_used,
                self.blob_gas_limit,
                gas_used,
                gas_limit,
            )
            .await;

            env.tx = tx.to_revm_tx_env();

            // disable nonce checks
            env.evm_env.cfg_env.disable_nonce_check = true;

            // disable balance checks
            env.evm_env.cfg_env.disable_balance_check = true;

            // disable gas fee checks
            env.evm_env.cfg_env.disable_base_fee = true;
            env.evm_env.cfg_env.disable_block_gas_limit = true;

            let mut inspector = AnvilInspector::default()
                .with_access_list_inspector()
                .with_steps_tracing()
                .with_transfers();

            let mut evm = new_evm_with_inspector_ref(&nested_db, &env, &mut inspector);
            env.networks.inject_precompiles(evm.precompiles_mut());

            let eth_res_res = evm.transact(tx.to_revm_tx_env());
            if eth_res_res.is_err() {
                println!("evm.transact errored: {:?}", eth_res_res);

                self.cache_db = nested_db.discard_outer();
                return (Err(eth_res_res.err().unwrap().into()), self);
            }

            let eth_res = eth_res_res.unwrap();
            nested_db.commit(eth_res.state);

            // fetch the access set
            let mut accessed = HashMap::new();
            inspector.access_list.unwrap().touched_slots().iter().for_each(|(a, b)| {
                b.iter().for_each(|key| {
                    accessed
                        .entry(*a)
                        .or_insert(Vec::<U256>::new())
                        .push((*key as FixedBytes<32>).into())
                });
            });

            let state_diffs: Vec<(Address, Box<StorageChange>)> = inspector
                .tracer
                .unwrap()
                .traces()
                .nodes()
                .iter()
                .map(|n| {
                    n.trace
                        .steps
                        .iter()
                        .map(|s| {
                            if s.storage_change.is_none() {
                                None
                            } else {
                                Some((n.execution_address(), s.storage_change.clone()))
                            }
                        })
                        .collect::<Vec<_>>()
                })
                .flatten()
                .flatten()
                .flat_map(|i| if i.1.is_none() { None } else { Some((i.0, i.1.unwrap())) })
                .collect();

            // fetch the write set
            let mut writes = HashMap::new();
            for (address, change) in state_diffs {
                if let Some(prev_value) = change.had_value {
                    if prev_value != change.value {
                        let entry = writes.entry(address).or_insert(Vec::<U256>::new());
                        if !entry.contains(&change.key) {
                            entry.push(change.key);
                        }
                    }
                }
            }

            // fetch ETH value diffs
            let mut eth_diffs = HashMap::new();
            for transfer_operation in inspector.transfer.unwrap().into_transfers() {
                // deduce from
                let diff_from = eth_diffs.entry(transfer_operation.from).or_insert(I512::ZERO);
                *diff_from = diff_from.checked_sub(I512::from(transfer_operation.value)).unwrap();

                // increment to
                let diff_to = eth_diffs.entry(transfer_operation.to).or_insert(I512::ZERO);
                *diff_to = diff_to.checked_add(I512::from(transfer_operation.value)).unwrap();
            }

            let gas_fees = inspector.gas_fees.unwrap_or_default();

            let prio_fees = gas_fees.proposer_reward;
            let burned_fees = gas_fees.caller_gas_spending - gas_fees.caller_gas_refund - prio_fees;

            let tx_res = TransactionAccessSimulationResult {
                hash: *tx_hash,
                accesses: accessed,
                writes,
                transfer_diffs: eth_diffs,
                success: errors.len() == 0 && eth_res.result.is_success(),
                errors,
                gas_used: eth_res.result.gas_used(),
                blob_gas_used: tx.transaction.blob_gas().unwrap_or(0),
                burned_ether: burned_fees,
                priority_fee: prio_fees,
                sender: *tx.sender(),
                coinbase: env.evm_env.block_env.beneficiary,
                effective_gas_price: gas_fees.effective_gas_price,
                max_gas_cost: tx.transaction.max_cost(),
                nonces_required: inspector.nonces.required_nonces,
                nonces_possible: inspector.nonces.possible_nonces,
            };

            out.push(tx_res);

            // update running (blob) gas values
            gas_used = gas_used.saturating_add(eth_res.result.gas_used());
            blob_gas_used = blob_gas_used.saturating_add(tx.transaction.blob_gas().unwrap_or(0));
        }

        self.cache_db = nested_db.discard_outer();
        return (Ok(out), self);
    }

    pub async fn simulate_transaction_individually(
        self,
        txs: Vec<PendingTransaction>,
    ) -> (HashMap<TxHash, TransactionAccessSimulationResult>, Self) {
        let mut out = HashMap::new();
        let mut sim_state = self;
        for tx in txs {
            let hash = tx.hash().clone();
            let (res, s) = sim_state.simulate_transactions(vec![tx]).await;
            out.insert(hash, res.unwrap().pop().unwrap());
            sim_state = s
        }

        (out, sim_state)
    }
}
