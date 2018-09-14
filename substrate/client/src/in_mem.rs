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

//! In memory client backend

use std::collections::HashMap;
use std::sync::Arc;
use parking_lot::RwLock;
use error;
use backend;
use light;
use primitives::AuthorityId;
use runtime_primitives::generic::BlockId;
use runtime_primitives::traits::{Block as BlockT, Justification as JustificationT, Header as HeaderT, Zero, NumberFor, As};
use blockchain::{self, BlockStatus};
use state_machine::backend::{Backend as StateBackend, InMemory};
use patricia_trie::NodeCodec;
use hashdb::Hasher;
use heapsize::HeapSizeOf;

struct PendingBlock<J: JustificationT> {
	block: StoredBlock<J>,
	is_best: bool,
}

#[derive(PartialEq, Eq, Clone)]
enum StoredBlock<J: JustificationT> {
	Header(<J::Block as BlockT>::Header, Option<J>),
	Full(J::Block, Option<J>),
}

impl<J: JustificationT> StoredBlock<J> {
	fn new(header: <J::Block as BlockT>::Header, body: Option<Vec<<J::Block as BlockT>::Extrinsic>>, just: Option<J>) -> Self {
		match body {
			Some(body) => StoredBlock::Full(<J::Block as BlockT>::new(header, body), just),
			None => StoredBlock::Header(header, just),
		}
	}

	fn header(&self) -> &<J::Block as BlockT>::Header {
		match *self {
			StoredBlock::Header(ref h, _) => h,
			StoredBlock::Full(ref b, _) => b.header(),
		}
	}

	fn justification(&self) -> Option<&J> {
		match *self {
			StoredBlock::Header(_, ref j) | StoredBlock::Full(_, ref j) => j.as_ref()
		}
	}

	fn extrinsics(&self) -> Option<&[<J::Block as BlockT>::Extrinsic]> {
		match *self {
			StoredBlock::Header(_, _) => None,
			StoredBlock::Full(ref b, _) => Some(b.extrinsics())
		}
	}

	fn into_inner(self) -> (<J::Block as BlockT>::Header, Option<Vec<<J::Block as BlockT>::Extrinsic>>, Option<J>) {
		match self {
			StoredBlock::Header(header, just) => (header, None, just),
			StoredBlock::Full(block, just) => {
				let (header, body) = block.deconstruct();
				(header, Some(body), just)
			}
		}
	}
}

#[derive(Clone)]
struct BlockchainStorage<J: JustificationT> {
	blocks: HashMap<<J::Block as BlockT>::Hash, StoredBlock<J>>,
	hashes: HashMap<<<J::Block as BlockT>::Header as HeaderT>::Number, <J::Block as BlockT>::Hash>,
	best_hash: <J::Block as BlockT>::Hash,
	best_number: <<J::Block as BlockT>::Header as HeaderT>::Number,
	genesis_hash: <J::Block as BlockT>::Hash,
	cht_roots: HashMap<NumberFor<J::Block>, <J::Block as BlockT>::Hash>,
}

/// In-memory blockchain. Supports concurrent reads.
pub struct Blockchain<J: JustificationT> {
	storage: Arc<RwLock<BlockchainStorage<J>>>,
	cache: Cache<J>,
}

struct Cache<J: JustificationT> {
	storage: Arc<RwLock<BlockchainStorage<J>>>,
	authorities_at: RwLock<HashMap<<J::Block as BlockT>::Hash, Option<Vec<AuthorityId>>>>,
}

impl<J: JustificationT> Clone for Blockchain<J> {
	fn clone(&self) -> Self {
		let storage = Arc::new(RwLock::new(self.storage.read().clone()));
		Blockchain {
			storage: storage.clone(),
			cache: Cache {
				storage,
				authorities_at: RwLock::new(self.cache.authorities_at.read().clone()),
			},
		}
	}
}

impl<J: JustificationT> Blockchain<J> {
	/// Get header hash of given block.
	pub fn id(&self, id: BlockId<J::Block>) -> Option<<J::Block as BlockT>::Hash> {
		match id {
			BlockId::Hash(h) => Some(h),
			BlockId::Number(n) => self.storage.read().hashes.get(&n).cloned(),
		}
	}

	/// Create new in-memory blockchain storage.
	pub fn new() -> Blockchain<J> {
		let storage = Arc::new(RwLock::new(
			BlockchainStorage {
				blocks: HashMap::new(),
				hashes: HashMap::new(),
				best_hash: Default::default(),
				best_number: Zero::zero(),
				genesis_hash: Default::default(),
				cht_roots: HashMap::new(),
			}));
		Blockchain {
			storage: storage.clone(),
			cache: Cache {
				storage: storage,
				authorities_at: Default::default(),
			},
		}
	}

	/// Insert a block header and associated data.
	pub fn insert(
		&self,
		hash: <J::Block as BlockT>::Hash,
		header: <J::Block as BlockT>::Header,
		justification: Option<J>,
		body: Option<Vec<<J::Block as BlockT>::Extrinsic>>,
		is_new_best: bool
	) {
		let number = header.number().clone();
		let mut storage = self.storage.write();
		storage.blocks.insert(hash.clone(), StoredBlock::new(header, body, justification));
		storage.hashes.insert(number, hash.clone());
		if is_new_best {
			storage.best_hash = hash.clone();
			storage.best_number = number.clone();
		}
		if number == Zero::zero() {
			storage.genesis_hash = hash;
		}
	}

	/// Compare this blockchain with another in-mem blockchain
	pub fn equals_to(&self, other: &Self) -> bool {
		self.canon_equals_to(other) && self.storage.read().blocks == other.storage.read().blocks
	}

	/// Compare canonical chain to other canonical chain.
	pub fn canon_equals_to(&self, other: &Self) -> bool {
		let this = self.storage.read();
		let other = other.storage.read();
			this.hashes == other.hashes
			&& this.best_hash == other.best_hash
			&& this.best_number == other.best_number
			&& this.genesis_hash == other.genesis_hash
	}

	/// Insert CHT root.
	pub fn insert_cht_root(&self, block: NumberFor<J::Block>, cht_root: <J::Block as BlockT>::Hash) {
		self.storage.write().cht_roots.insert(block, cht_root);
	}
}

impl<J: JustificationT> blockchain::HeaderBackend<J> for Blockchain<J> {
	fn header(&self, id: BlockId<J::Block>) -> error::Result<Option<<J::Block as BlockT>::Header>> {
		Ok(self.id(id).and_then(|hash| {
			self.storage.read().blocks.get(&hash).map(|b| b.header().clone())
		}))
	}

	fn info(&self) -> error::Result<blockchain::Info<J::Block>> {
		let storage = self.storage.read();
		Ok(blockchain::Info {
			best_hash: storage.best_hash,
			best_number: storage.best_number,
			genesis_hash: storage.genesis_hash,
		})
	}

	fn status(&self, id: BlockId<J::Block>) -> error::Result<BlockStatus> {
		match self.id(id).map_or(false, |hash| self.storage.read().blocks.contains_key(&hash)) {
			true => Ok(BlockStatus::InChain),
			false => Ok(BlockStatus::Unknown),
		}
	}

	fn number(&self, hash: <J::Block as BlockT>::Hash) -> error::Result<Option<NumberFor<J::Block>>> {
		Ok(self.storage.read().blocks.get(&hash).map(|b| *b.header().number()))
	}

	fn hash(&self, number: <<J::Block as BlockT>::Header as HeaderT>::Number) -> error::Result<Option<<J::Block as BlockT>::Hash>> {
		Ok(self.id(BlockId::Number(number)))
	}
}


impl<J: JustificationT> blockchain::Backend<J> for Blockchain<J> {
	fn body(&self, id: BlockId<J::Block>) -> error::Result<Option<Vec<<J::Block as BlockT>::Extrinsic>>> {
		Ok(self.id(id).and_then(|hash| {
			self.storage.read().blocks.get(&hash)
				.and_then(|b| b.extrinsics().map(|x| x.to_vec()))
		}))
	}

	fn justification(&self, id: BlockId<J::Block>) -> error::Result<Option<J>> {
		Ok(self.id(id).and_then(|hash| self.storage.read().blocks.get(&hash).and_then(|b|
			b.justification().map(|x| x.clone()))
		))
	}

	fn cache(&self) -> Option<&blockchain::Cache<J::Block>> {
		Some(&self.cache)
	}
}

impl<J: JustificationT> light::blockchain::Storage<J> for Blockchain<J>
	where
		<J::Block as BlockT>::Hash: From<[u8; 32]>,
{
	fn import_header(
		&self,
		is_new_best: bool,
		header: <J::Block as BlockT>::Header,
		authorities: Option<Vec<AuthorityId>>
	) -> error::Result<()> {
		let hash = header.hash();
		let parent_hash = *header.parent_hash();
		self.insert(hash, header, None, None, is_new_best);
		if is_new_best {
			self.cache.insert(parent_hash, authorities);
		}
		Ok(())
	}

	fn cht_root(&self, _cht_size: u64, block: NumberFor<J::Block>) -> error::Result<<J::Block as BlockT>::Hash> {
		self.storage.read().cht_roots.get(&block).cloned()
			.ok_or_else(|| error::ErrorKind::Backend(format!("CHT for block {} not exists", block)).into())
	}

	fn cache(&self) -> Option<&blockchain::Cache<J::Block>> {
		Some(&self.cache)
	}
}

/// In-memory operation.
pub struct BlockImportOperation<H: Hasher, C: NodeCodec<H>, J: JustificationT> {
	pending_block: Option<PendingBlock<J>>,
	pending_authorities: Option<Vec<AuthorityId>>,
	old_state: InMemory<H, C>,
	new_state: Option<InMemory<H, C>>,
}

impl<H, C, J> backend::BlockImportOperation<H, C, J> for BlockImportOperation<H, C, J>
where
	H: Hasher,
	C: NodeCodec<H>,
	H::Out: HeapSizeOf,
	J: JustificationT,
{
	type State = InMemory<H, C>;

	fn state(&self) -> error::Result<Option<&Self::State>> {
		Ok(Some(&self.old_state))
	}

	fn set_block_data(
		&mut self,
		header: <J::Block as BlockT>::Header,
		body: Option<Vec<<J::Block as BlockT>::Extrinsic>>,
		justification: Option<J>,
		is_new_best: bool
	) -> error::Result<()> {
		assert!(self.pending_block.is_none(), "Only one block per operation is allowed");
		self.pending_block = Some(PendingBlock {
			block: StoredBlock::new(header, body, justification),
			is_best: is_new_best,
		});
		Ok(())
	}

	fn update_authorities(&mut self, authorities: Vec<AuthorityId>) {
		self.pending_authorities = Some(authorities);
	}

	fn update_storage(&mut self, update: <InMemory<H, C> as StateBackend<H, C>>::Transaction) -> error::Result<()> {
		self.new_state = Some(self.old_state.update(update));
		Ok(())
	}

	fn reset_storage<I: Iterator<Item=(Vec<u8>, Vec<u8>)>>(&mut self, iter: I) -> error::Result<()> {
		self.new_state = Some(InMemory::from(iter.collect::<HashMap<_, _>>()));
		Ok(())
	}
}

/// In-memory backend. Keeps all states and blocks in memory. Useful for testing.
pub struct Backend<H, C, J>
where
	H: Hasher,
	C: NodeCodec<H>,
	J: JustificationT
{
	states: RwLock<HashMap<<J::Block as BlockT>::Hash, InMemory<H, C>>>,
	blockchain: Blockchain<J>,
}

impl<H, C, J> Backend<H, C, J>
where
	H: Hasher,
	C: NodeCodec<H>,
	J: JustificationT
{
	/// Create a new instance of in-mem backend.
	pub fn new() -> Backend<H, C, J> {
		Backend {
			states: RwLock::new(HashMap::new()),
			blockchain: Blockchain::new(),
		}
	}
}

impl<H, C, J> backend::Backend<H, C, J> for Backend<H, C, J>
where
	H: Hasher,
	H::Out: HeapSizeOf,
	C: NodeCodec<H> + Send + Sync,
	J: JustificationT
{
	type BlockImportOperation = BlockImportOperation<H, C, J>;
	type Blockchain = Blockchain<J>;
	type State = InMemory<H, C>;

	fn begin_operation(&self, block: BlockId<J::Block>) -> error::Result<Self::BlockImportOperation> {
		let state = match block {
			BlockId::Hash(ref h) if h.clone() == Default::default() => Self::State::default(),
			_ => self.state_at(block)?,
		};

		Ok(BlockImportOperation {
			pending_block: None,
			pending_authorities: None,
			old_state: state,
			new_state: None,
		})
	}

	fn commit_operation(&self, operation: Self::BlockImportOperation) -> error::Result<()> {
		if let Some(pending_block) = operation.pending_block {
			let old_state = &operation.old_state;
			let (header, body, justification) = pending_block.block.into_inner();
			let hash = header.hash();
			let parent_hash = *header.parent_hash();

			self.states.write().insert(hash, operation.new_state.unwrap_or_else(|| old_state.clone()));
			self.blockchain.insert(hash, header, justification, body, pending_block.is_best);
			// dumb implementation - store value for each block
			if pending_block.is_best {
				self.blockchain.cache.insert(parent_hash, operation.pending_authorities);
			}
		}
		Ok(())
	}

	fn blockchain(&self) -> &Self::Blockchain {
		&self.blockchain
	}

	fn state_at(&self, block: BlockId<J::Block>) -> error::Result<Self::State> {
		match self.blockchain.id(block).and_then(|id| self.states.read().get(&id).cloned()) {
			Some(state) => Ok(state),
			None => Err(error::ErrorKind::UnknownBlock(format!("{}", block)).into()),
		}
	}

	fn revert(&self, _n: NumberFor<J::Block>) -> error::Result<NumberFor<J::Block>> {
		Ok(As::sa(0))
	}
}

impl<H, C, J> backend::LocalBackend<H, C, J> for Backend<H, C, J>
where
	H: Hasher,
	H::Out: HeapSizeOf,
	C: NodeCodec<H> + Send + Sync,
	J: JustificationT
{}

impl<J: JustificationT> Cache<J> {
	fn insert(&self, at: <J::Block as BlockT>::Hash, authorities: Option<Vec<AuthorityId>>) {
		self.authorities_at.write().insert(at, authorities);
	}
}

impl<J: JustificationT> blockchain::Cache<J::Block> for Cache<J> {
	fn authorities_at(&self, block: BlockId<J::Block>) -> Option<Vec<AuthorityId>> {
		let hash = match block {
			BlockId::Hash(hash) => hash,
			BlockId::Number(number) => self.storage.read().hashes.get(&number).cloned()?,
		};

		self.authorities_at.read().get(&hash).cloned().unwrap_or(None)
	}
}

/// Insert authorities entry into in-memory blockchain cache. Extracted as a separate function to use it in tests.
pub fn cache_authorities_at<J: JustificationT>(
	blockchain: &Blockchain<J>,
	at: <J::Block as BlockT>::Hash,
	authorities: Option<Vec<AuthorityId>>
) {
	blockchain.cache.insert(at, authorities);
}
