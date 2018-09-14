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

//! Light client blockchin backend. Only stores headers and justifications of recent
//! blocks. CHT roots are stored for headers of ancient blocks.

use std::sync::Weak;
use futures::{Future, IntoFuture};
use parking_lot::Mutex;

use primitives::AuthorityId;
use runtime_primitives::generic::BlockId;
use runtime_primitives::traits::{Block as BlockT, Justification as JustificationT, Header as HeaderT, NumberFor, Zero};

use blockchain::{Backend as BlockchainBackend, BlockStatus, Cache as BlockchainCache,
	HeaderBackend as BlockchainHeaderBackend, Info as BlockchainInfo};
use cht;
use error::{ErrorKind as ClientErrorKind, Result as ClientResult};
use light::fetcher::{Fetcher, RemoteHeaderRequest};

/// Light client blockchain storage.
pub trait Storage<J: JustificationT>: BlockchainHeaderBackend<J> {
	/// Store new header.
	fn import_header(
		&self,
		is_new_best: bool,
		header: <<J as JustificationT>::Block as BlockT>::Header,
		authorities: Option<Vec<AuthorityId>>
	) -> ClientResult<()>;

	/// Get CHT root for given block. Fails if the block is not pruned (not a part of any CHT).
	fn cht_root(&self, cht_size: u64, block: NumberFor<J::Block>)
		-> ClientResult<<J::Block as BlockT>::Hash>;

	/// Get storage cache.
	fn cache(&self) -> Option<&BlockchainCache<J::Block>>;
}

/// Light client blockchain.
pub struct Blockchain<S, F> {
	fetcher: Mutex<Weak<F>>,
	storage: S,
}

impl<S, F> Blockchain<S, F> {
	/// Create new light blockchain backed with given storage.
	pub fn new(storage: S) -> Self {
		Self {
			fetcher: Mutex::new(Default::default()),
			storage,
		}
	}

	/// Sets fetcher reference.
	pub fn set_fetcher(&self, fetcher: Weak<F>) {
		*self.fetcher.lock() = fetcher;
	}

	/// Get fetcher weak reference.
	pub fn fetcher(&self) -> Weak<F> {
		self.fetcher.lock().clone()
	}

	/// Get storage reference.
	pub fn storage(&self) -> &S {
		&self.storage
	}
}

impl<S, F, J> BlockchainHeaderBackend<J> for Blockchain<S, F>
where
	S: Storage<J>,
	F: Fetcher<J::Block>,
	J: JustificationT,
{
	fn header(&self, id: BlockId<J::Block>) -> ClientResult<Option<<J::Block as BlockT>::Header>> {
		match self.storage.header(id)? {
			Some(header) => Ok(Some(header)),
			None => {
				let number = match id {
					BlockId::Hash(hash) => match self.storage.number(hash)? {
						Some(number) => number,
						None => return Ok(None),
					},
					BlockId::Number(number) => number,
				};

				// if the header is from future or genesis (we never prune genesis) => return
				if number.is_zero() || self.storage.status(BlockId::Number(number))? != BlockStatus::InChain {
					return Ok(None);
				}

				self.fetcher().upgrade().ok_or(ClientErrorKind::NotAvailableOnLightClient)?
					.remote_header(RemoteHeaderRequest {
						cht_root: self.storage.cht_root(cht::SIZE, number)?,
						block: number,
						retry_count: None,
					})
					.into_future().wait()
					.map(Some)
			}
		}
	}

	fn info(&self) -> ClientResult<BlockchainInfo<J::Block>> {
		self.storage.info()
	}

	fn status(&self, id: BlockId<J::Block>) -> ClientResult<BlockStatus> {
		self.storage.status(id)
	}

	fn number(&self, hash: <J::Block as BlockT>::Hash) -> ClientResult<Option<NumberFor<J::Block>>> {
		self.storage.number(hash)
	}

	fn hash(&self, number: <<J::Block as BlockT>::Header as HeaderT>::Number) -> ClientResult<Option<<<J as JustificationT>::Block as BlockT>::Hash>> {
		self.storage.hash(number)
	}
}

impl<S, F, J> BlockchainBackend<J> for Blockchain<S, F>
where
	S: Storage<J>,
	F: Fetcher<J::Block>,
	J: JustificationT,
{
	fn body(&self, _id: BlockId<J::Block>) -> ClientResult<Option<Vec<<J::Block as BlockT>::Extrinsic>>> {
		// TODO [light]: fetch from remote node
		Ok(None)
	}

	fn justification(&self, _id: BlockId<J::Block>) -> ClientResult<Option<J>> {
		Ok(None)
	}

	fn cache(&self) -> Option<&BlockchainCache<J::Block>> {
		self.storage.cache()
	}
}
