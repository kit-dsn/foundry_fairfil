use crate::eth::backend::mem::{Backend, TransactionAccessSimulationResult};
use crate::eth::error::BlockchainError;
use alloy_primitives::TxHash;
use anvil_core::eth::transaction::TypedTransaction;
use parking_lot::RwLock;
use std::collections::HashMap;
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

    pub fn get_raw_transaction(&self, hash: TxHash, backend: &Backend) -> Option<TypedTransaction> {
        self.ensure_current_block(backend.best_number());
        self.inner.read().get_raw_transaction(&hash)
    }

    fn ensure_current_block(&self, cur_block_number: u64) {
        if *self.prev_block_number.read() != cur_block_number {
            let mut inner = self.inner.write();
            *inner = TransactionRegisterInner::default();
            *self.prev_block_number.write() = cur_block_number
        }
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
