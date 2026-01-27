use crate::eth::backend::mem::{Backend, TransactionAccessSimulationResult};
use crate::eth::error::BlockchainError;
use alloy_primitives::aliases::I512;
use alloy_primitives::{Address, TxHash};
use anvil_core::eth::transaction::{PendingTransaction, TypedTransaction};
use parking_lot::RwLock;
use std::collections::{HashMap, HashSet};
use std::sync::Arc;

#[derive(Default)]
pub struct TransactionRegister {
    /// holds transactions and simulations
    inner: RwLock<TransactionRegisterInner>,
    /// block number of preceding block,
    /// i.e., the block number before the
    /// registered transactions are included.
    prev_block_number: RwLock<u64>,
}

impl TransactionRegister {
    pub async fn register_transaction(
        &self,
        tx: TypedTransaction,
        backend: &Backend,
    ) -> Result<(TxHash, Arc<TransactionAccessSimulationResult>), BlockchainError> {
        let hash = tx.clone().hash();

        let sim = {
            let mut results = backend.simulate_transaction_state_access(vec![tx.clone()]).await?;

            if results.len() != 1 {
                return Err(BlockchainError::Message("no simulation result found".to_string()));
            }

            Ok::<TransactionAccessSimulationResult, BlockchainError>(results.pop().unwrap())
        }?;

        self.ensure_current_block(backend.best_number());
        {
            let inner = self.inner.write();
            inner.add_transaction(hash, tx, sim);
        }

        Ok((hash, self.inner.read().get_simulation(&hash).unwrap()))
    }

    pub fn get_simulation(
        &self,
        hash: TxHash,
        backend: &Backend,
    ) -> Option<Arc<TransactionAccessSimulationResult>> {
        self.ensure_current_block(backend.best_number());
        self.inner.read().get_simulation(&hash)
    }

    pub fn get_raw_transaction(&self, hash: TxHash, backend: &Backend) -> Option<TypedTransaction> {
        self.ensure_current_block(backend.best_number());
        self.inner.read().get_raw_transaction(&hash)
    }

    pub fn get_raw_transactions(
        &self,
        hashes: &Vec<TxHash>,
        backend: &Backend,
    ) -> Option<Vec<TypedTransaction>> {
        self.ensure_current_block(backend.best_number());
        hashes.iter().map(|hash| self.inner.read().get_raw_transaction(hash)).collect()
    }

    pub fn get_pending_tx(&self, hash: &TxHash) -> PendingTransaction {
        PendingTransaction::new(self.inner.read().get_raw_transaction(hash).unwrap()).unwrap()
    }

    pub fn get_pending_txs(&self, hashes: &Vec<TxHash>) -> Vec<PendingTransaction> {
        hashes
            .iter()
            .map(|hash| {
                PendingTransaction::new(self.inner.read().get_raw_transaction(hash).unwrap())
                    .unwrap()
            })
            .collect()
    }

    pub fn find_transaction_with_nonce(
        &self,
        sender: &Address,
        nonce: u64,
        used: &HashSet<TxHash>,
    ) -> Option<TxHash> {
        self.inner
            .read()
            .simulations
            .read()
            // iterate over all simulations
            .iter()
            .filter(|(hash, s)| {
                if used.contains(*hash) {
                    return false;
                }

                if s.sender == *sender && s.nonces_required[0].0 == *sender {
                    // transaction sender is the account in question
                    s.nonces_required[0].1 == nonce
                } else {
                    // even if the sender is not the account in question,
                    // due to EIP-7702 (set code transactions) a transaction of
                    // another account can change the nonce of the account via an authorization
                    s.nonces_possible.iter().any(|(a, v)| *a == *sender && *v == nonce)
                }
            })
            .map(|(hash, _)| *hash)
            .next() // take one transaction hash
    }

    pub fn find_transaction_paying(
        &self,
        recipient: &Address,
        used: &HashSet<TxHash>,
    ) -> Vec<TxHash> {
        self.inner
            .read()
            .simulations
            .read()
            // iterate over all simulations
            .iter()
            .filter(|(hash, s)| {
                if used.contains(*hash) {
                    return false;
                }

                s.transfer_diffs.iter().any(|(acc, diff)| *acc == *recipient && *diff > I512::ZERO)
            })
            .map(|(hash, _)| *hash)
            .collect()
    }

    fn ensure_current_block(&self, cur_block_number: u64) {
        if *self.prev_block_number.read() != cur_block_number {
            let mut inner = self.inner.write();
            *inner = TransactionRegisterInner::default();
            *self.prev_block_number.write() = cur_block_number
        }
    }

    pub fn restrict_mempool(
        &self,
        restricted: &Vec<TxHash>,
    ) -> Result<TransactionRegister, BlockchainError> {
        let restricted_register = TransactionRegister::default();
        *restricted_register.prev_block_number.write() = *self.prev_block_number.read();

        restricted.iter().try_for_each(|hash| {
            let raw_tx = self
                .inner
                .read()
                .get_raw_transaction(hash)
                .ok_or(BlockchainError::TransactionNotFound)?;
            let sim = self
                .inner
                .read()
                .get_simulation(hash)
                .ok_or(BlockchainError::TransactionNotFound)?;

            {
                let inner = restricted_register.inner.write();
                inner.transactions.write().insert(*hash, raw_tx.clone());
                inner.simulations.write().insert(*hash, sim);
            }

            Ok::<(), BlockchainError>(())
        })?;

        Ok(restricted_register)
    }

    pub fn has(&self, tx: &TxHash) -> bool {
        self.inner.read().transactions.read().contains_key(tx)
            && self.inner.read().simulations.read().contains_key(tx)
    }
}

#[derive(Debug, Default)]
struct TransactionRegisterInner {
    transactions: Arc<RwLock<HashMap<TxHash, TypedTransaction>>>,
    simulations: Arc<RwLock<HashMap<TxHash, Arc<TransactionAccessSimulationResult>>>>,
}

impl TransactionRegisterInner {
    pub fn add_transaction(
        &self,
        hash: TxHash,
        tx: TypedTransaction,
        sim: TransactionAccessSimulationResult,
    ) {
        self.transactions.write().insert(hash, tx);
        self.simulations.write().insert(hash, Arc::new(sim));
    }

    pub fn get_raw_transaction(&self, hash: &TxHash) -> Option<TypedTransaction> {
        let txs = self.transactions.read();
        return txs.get(hash).map(|x| x.clone());
    }

    pub fn get_simulation(&self, hash: &TxHash) -> Option<Arc<TransactionAccessSimulationResult>> {
        let sims = self.simulations.read();
        return sims.get(hash).map(|x| x.clone());
    }
}
