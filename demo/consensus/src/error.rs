// Copyright 2018 Parity Technologies (UK) Ltd.
// This file is part of Substrate Demo.

// Substrate Demo is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Substrate Demo is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Substrate Demo.  If not, see <http://www.gnu.org/licenses/>.

//! Errors that can occur during the consensus process.

use primitives::AuthorityId;

error_chain! {
	links {
		Api(::demo_api::Error, ::demo_api::ErrorKind);
		Bft(::rhd::Error, ::rhd::ErrorKind);
	}

	errors {
		NotValidator(id: AuthorityId) {
			description("Local account ID not a validator at this block."),
			display("Local account ID ({:?}) not a validator at this block.", id),
		}
		PrematureDestruction {
			description("Proposer destroyed before finishing proposing or evaluating"),
			display("Proposer destroyed before finishing proposing or evaluating"),
		}
		Timer(e: ::tokio::timer::Error) {
			description("Failed to register or resolve async timer."),
			display("Timer failed: {}", e),
		}
		Executor(e: ::futures::future::ExecuteErrorKind) {
			description("Unable to dispatch agreement future"),
			display("Unable to dispatch agreement future: {:?}", e),
		}
	}
}

impl From<::rhd::InputStreamConcluded> for Error {
	fn from(err: ::rhd::InputStreamConcluded) -> Self {
		::rhd::Error::from(err).into()
	}
}
