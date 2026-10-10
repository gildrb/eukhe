//! The Session kernel (`src/session/*.ts`): one mutation line over one
//! Storage, transactions, the document tracker cache, and committed
//! observation.

mod error;
mod forks;
mod guarded;
mod observation;
mod plans;
#[expect(
    clippy::module_inception,
    reason = "one TS file, one Rust module of the same name"
)]
mod session;
#[cfg(test)]
pub(crate) mod tests;
mod transaction;

pub use error::{SessionError, SessionResult};
pub(crate) use observation::CommittedStateSource;
pub use observation::{
    CommittedWatch, DocumentWatch, ObservedDocumentValue, ObservedValue, Ops, WatchEnd,
    WatchListener, WatchListenerError,
};
pub use session::{
    create_session, system_now, CloseListener, CommitListener, DocumentState,
    InternalCommitListener, NoSessionHooks, OnLineDocument, Session, SessionClock, SessionEnd,
    SessionHooks, SessionOptions, Unsubscribe,
};
#[allow(unused_imports, reason = "used by the harness, ported separately")]
pub(crate) use transaction::{erase, Definition};
pub use transaction::{TaskDefinitionRef, TransactionScope, Tx, TxFuture};
