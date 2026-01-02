use std::collections::HashSet;

use alloy_primitives::{FixedBytes, U256};
use alloy_evm::Evm;
use anvil_core::eth::transaction::{PendingTransaction, TypedTransaction};
use revm::{context::Transaction, database::CacheDB, primitives::hardfork::SpecId, DatabaseCommit};
use crate::eth::{backend::{db::StateDb, env::Env, mem::Backend}, error::BlockchainError};

impl Backend {
    pub async fn concurrent_proposers_cycling_highest(
        &self,
        mut batches: Vec<Vec<TypedTransaction>>,
    ) -> Result<(), BlockchainError> {
        
        // ensure that all batches are valid, i.e., executable
        for (batch_idx, batch) in batches.iter().enumerate() {
            if !self.test_batch(batch.to_vec()).await? {
                // there is one invalid batch
                return Err(BlockchainError::Message(format!("batch {} invalid", batch_idx)))
            }
        }
        
        // let's build the super-block!
        let mut block: Vec<TypedTransaction> = vec![];
        let mut included_txs: HashSet<FixedBytes<32>> = HashSet::new();

        let (evm_env, mut evm_db) = self.build_evm_environment().await?;

        loop {
            batches = cleanup_batches_for_inclusion(batches, &included_txs);

            let heads = get_heads(&batches);
            if heads.is_empty() {
                break
            }

            let mut inspector = self.build_inspector();
            let mut evm = self.new_evm_with_inspector_ref(
                &evm_db,
                &evm_env,
                &mut inspector,
            );
            
            let winning_tx = heads.iter().max_by_key(|t| {
                // get the effective gas price of transactions
                PendingTransaction::new((*t).clone()).unwrap().to_revm_tx_env().effective_gas_price(evm_env.evm_env.block_env.basefee as u128);
            });

            match winning_tx {
                None => {
                    break
                }
                Some(tx) => {
                    // let's try to include that transaction!
                    println!("winning tx: {}", tx.hash());

                    let pending_tx = PendingTransaction::new(tx.clone()).unwrap();
                    included_txs.insert(*pending_tx.hash());

                    let transact_res  = evm.transact(pending_tx.to_revm_tx_env());
                    match transact_res {
                        Err(_) => {
                            // failed!
                            println!("transaction failed.");
                        }
                        Ok(result_state) => {
                            // we executed the transaction successfully!
                            block.push(tx.clone());
                            evm_db.commit(result_state.state);

                            println!("succeeded");
                        }
                    }
                }
            }
        }

        Ok(())
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

    async fn build_evm_environment(&self) -> Result<(Env, CacheDB<StateDb>), BlockchainError> {
        let db = self.db.read().await;
        let mut cache_db = CacheDB::new(db.current_state());
        
        let mut env = self.env.read().clone();

        env.evm_env.block_env.basefee = self.base_fee();
        env.evm_env.block_env.blob_excess_gas_and_price = self.excess_blob_gas_and_price();

        // disable nonce checks
        env.evm_env.cfg_env.disable_nonce_check = true;

        // disable balance checks
        env.evm_env.cfg_env.disable_balance_check = true;

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
        let mut evm = self.new_evm_with_inspector_ref(
            &cache_db,
            &env,
            &mut inspector,
        );

        // Do EIP-4788
        if env.evm_env.cfg_env.spec >= SpecId::CANCUN && parent_beacon_root.is_some() {
            let eip4788_result= evm.transact_system_call(
                alloy_eips::eip4788::SYSTEM_ADDRESS, 
                alloy_eips::eip4788::BEACON_ROOTS_ADDRESS, 
                parent_beacon_root.unwrap().into()
            )?;

            cache_db.commit(eip4788_result.state);
        }

        Ok((env, cache_db))
    }
}

fn get_heads(batches: &Vec<Vec<TypedTransaction>>) -> Vec<TypedTransaction> {
    let mut res = vec![];
    for batch in batches {
        if !batch.is_empty() {
            res.push(batch[0].clone());
        }
    }
    res
}

/// Iterate over the batches and remove those transactions at the beginning which are contained in the hashset
fn cleanup_batches_for_inclusion(batches: Vec<Vec<TypedTransaction>>, included: &HashSet<FixedBytes<32>>) -> Vec<Vec<TypedTransaction>> {
    let mut res = vec![];
    for batch in batches {
        for (idx, tx) in batch.iter().enumerate() {
            if !included.contains(&tx.hash()) { 
                res.push(batch.clone().split_off(idx));
                break
            }
        }
    }
    
    res
}