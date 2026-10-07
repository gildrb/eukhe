//! Committed document reads and watches as object-safe values (TS
//! `DocumentReader` and `DocumentObserver` of `types.ts`).
//!
//! TS passes a Session, a task runtime, or a tool API wherever a
//! `DocumentReader` is expected. Rust needs object-safe traits for that, so
//! the core methods take an erased definition and a resolved address; the
//! blanket `*Ext` traits add the typed token methods every implementation
//! shares.

use std::sync::Arc;

use eukhe_chord::context::Context;
use futures::future::BoxFuture;

use crate::documents::ResolvedAddress;
use crate::documents::{resolve_token_address, AnyDocDefinition, DocToken, RewindableDocToken};
use crate::session::{erase, DocumentWatch, Session, SessionResult};
use crate::types::{EntryId, JsonObject};

/// Committed document reads (TS `Pick<Session, "snapshot" | "snapshotAsOf">`).
///
/// Implementations answer from committed state only, never create a
/// document, and reject once the object they read through has ended (a closed
/// Session, an ended invocation).
pub trait DocumentReader: Send + Sync {
    /// Committed immutable value of the document `definition` at `resolved`;
    /// `None` when absent.
    fn snapshot_definition(
        &self,
        definition: Arc<dyn AnyDocDefinition>,
        resolved: ResolvedAddress,
        cx: &Context,
    ) -> BoxFuture<'static, SessionResult<Option<Arc<JsonObject>>>>;

    /// Value of a rewindable conversation document as of the visible entry
    /// `at`; `None` when it did not exist then.
    fn snapshot_as_of_definition(
        &self,
        definition: Arc<dyn AnyDocDefinition>,
        resolved: ResolvedAddress,
        at: EntryId,
        cx: &Context,
    ) -> BoxFuture<'static, SessionResult<Option<Arc<JsonObject>>>>;
}

/// Typed token reads of every [`DocumentReader`].
pub trait DocumentReaderExt: DocumentReader {
    /// Committed immutable value of a document; `None` when absent.
    fn snapshot<D: DocToken>(
        &self,
        token: &D,
        locator: D::Locator<'_>,
        cx: &Context,
    ) -> BoxFuture<'static, SessionResult<Option<Arc<JsonObject>>>> {
        let resolved = resolve_token_address(token, locator);
        self.snapshot_definition(erase(token), resolved, cx)
    }

    /// Value of a rewindable conversation document as of the visible entry
    /// `at`; `None` when it did not exist then.
    fn snapshot_as_of<D: RewindableDocToken>(
        &self,
        token: &D,
        locator: D::Locator<'_>,
        at: EntryId,
        cx: &Context,
    ) -> BoxFuture<'static, SessionResult<Option<Arc<JsonObject>>>> {
        let resolved = resolve_token_address(token, locator);
        self.snapshot_as_of_definition(erase(token), resolved, at, cx)
    }
}

impl<T: DocumentReader + ?Sized> DocumentReaderExt for T {}

/// Non-creating document watch acquisition shared by Session and invocation
/// APIs (TS `DocumentObserver`).
///
/// Implementations return `None` for an absent document; cancelling `cx`
/// cancels the watch, and invocation-bound implementations stop it when the
/// invocation ends.
pub trait DocumentObserver: Send + Sync {
    /// Serialized exact-frame watch of the document `definition` at
    /// `resolved`.
    fn watch_doc_definition(
        &self,
        definition: Arc<dyn AnyDocDefinition>,
        resolved: ResolvedAddress,
        cx: &Context,
    ) -> BoxFuture<'static, SessionResult<Option<DocumentWatch>>>;
}

/// Typed token watches of every [`DocumentObserver`].
pub trait DocumentObserverExt: DocumentObserver {
    /// Serialized exact-frame watch of the document's current committed
    /// incarnation; `None` when absent.
    fn watch_doc<D: DocToken>(
        &self,
        token: &D,
        locator: D::Locator<'_>,
        cx: &Context,
    ) -> BoxFuture<'static, SessionResult<Option<DocumentWatch>>> {
        let resolved = resolve_token_address(token, locator);
        self.watch_doc_definition(erase(token), resolved, cx)
    }
}

impl<T: DocumentObserver + ?Sized> DocumentObserverExt for T {}

impl DocumentReader for Session {
    fn snapshot_definition(
        &self,
        definition: Arc<dyn AnyDocDefinition>,
        resolved: ResolvedAddress,
        cx: &Context,
    ) -> BoxFuture<'static, SessionResult<Option<Arc<JsonObject>>>> {
        self.snapshot_at(&definition, resolved, cx)
    }

    fn snapshot_as_of_definition(
        &self,
        definition: Arc<dyn AnyDocDefinition>,
        resolved: ResolvedAddress,
        at: EntryId,
        cx: &Context,
    ) -> BoxFuture<'static, SessionResult<Option<Arc<JsonObject>>>> {
        self.snapshot_as_of_at(&definition, resolved, at, cx)
    }
}

impl DocumentObserver for Session {
    fn watch_doc_definition(
        &self,
        definition: Arc<dyn AnyDocDefinition>,
        resolved: ResolvedAddress,
        cx: &Context,
    ) -> BoxFuture<'static, SessionResult<Option<DocumentWatch>>> {
        self.watch_doc_at(&definition, resolved, cx)
    }
}
