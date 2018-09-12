// Copyright 2017 Parity Technologies (UK) Ltd.
// This file is part of Substrate.

// Substrate is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Substrate is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Substrate.  If not, see <http://www.gnu.org/licenses/>.

//! Light client components.

pub mod backend;
pub mod blockchain;
pub mod call_executor;
pub mod fetcher;

use std::sync::Arc;

use primitives::{KeccakHasher, RlpCodec};
use runtime_primitives::BuildStorage;
use runtime_primitives::traits::{Block as BlockT, Justification as JustificationT};
use state_machine::{CodeExecutor, ExecutionStrategy};

use client::Client;
use error::Result as ClientResult;
use light::backend::Backend;
use light::blockchain::{Blockchain, Storage as BlockchainStorage};
use light::call_executor::RemoteCallExecutor;
use light::fetcher::{Fetcher, LightDataChecker};
use hashdb::Hasher;
use patricia_trie::NodeCodec;

/// Create an instance of light client blockchain backend.
pub fn new_light_blockchain<B: BlockT, S: BlockchainStorage<B, J>, F, J: JustificationT>(storage: S) -> Arc<Blockchain<S, F>> {
	Arc::new(Blockchain::new(storage))
}

/// Create an instance of light client backend.
pub fn new_light_backend<B: BlockT, S: BlockchainStorage<B, J>, F: Fetcher<B>, J: JustificationT>(blockchain: Arc<Blockchain<S, F>>, fetcher: Arc<F>) -> Arc<Backend<S, F>> {
	blockchain.set_fetcher(Arc::downgrade(&fetcher));
	Arc::new(Backend::new(blockchain))
}

/// Create an instance of light client.
pub fn new_light<B, S, F, GS, J>(
	backend: Arc<Backend<S, F>>,
	fetcher: Arc<F>,
	genesis_storage: GS,
) -> ClientResult<Client<Backend<S, F>, RemoteCallExecutor<Blockchain<S, F>, F, KeccakHasher, RlpCodec, J>, B, J>>
	where
		B: BlockT,
		S: BlockchainStorage<B, J>,
		F: Fetcher<B>,
		GS: BuildStorage,
		J: JustificationT
{
	let executor = RemoteCallExecutor::new(backend.blockchain().clone(), fetcher);
	Client::new(backend, executor, genesis_storage, ExecutionStrategy::NativeWhenPossible)
}

/// Create an instance of fetch data checker.
pub fn new_fetch_checker<E, H, C>(
	executor: E,
) -> LightDataChecker<E, H, C>
	where
		E: CodeExecutor<H>,
		H: Hasher,
		C: NodeCodec<H>,
{
	LightDataChecker::new(executor)
}
