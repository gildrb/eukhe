//! Document definitions, typed tokens, address resolution, and typed
//! materialization (`documents.ts`, spec §3.1, §3.6).
//!
//! TS `defineDoc`/`defineDocFamily` overloads pick a token type from the
//! definition's `scope`, `history`, and `fork` literals. Rust has one token
//! type per overload, each built by a `const fn define`, so tokens can be
//! statics:
//!
//! ```
//! use eukhe_durable::documents::{ConversationDoc, DocDefinition};
//! use eukhe_durable::types::LatestFork;
//! use serde::{Deserialize, Serialize};
//!
//! #[derive(Default, Serialize, Deserialize)]
//! struct Counter { value: u64 }
//!
//! static COUNTER: ConversationDoc<Counter> = match ConversationDoc::define(
//!     DocDefinition { kind: "app.counter", version: 1, initial: Counter::default, migrate: None, checkpoint_when: None },
//!     LatestFork::Current,
//! ) {
//!     Ok(token) => token,
//!     Err(_) => panic!("invalid document definition"),
//! };
//! assert_eq!(COUNTER.definition().kind, "app.counter");
//! ```
//!
//! The [`DocToken`] trait carries each token's owner/key argument
//! ([`DocToken::Locator`]) and creation seed ([`DocToken::Seed`]), so the TS
//! overloads of `tx.doc(token, owner..., key, seed)` resolve at compile time.
//! The Session works with the erased [`AnyDocDefinition`] after resolution.

use std::error::Error;
use std::fmt;
use std::sync::Arc;

use eukhe_chord::delta::Op;
use eukhe_chord::json::{from_json, to_json, JsonError, JsonObject, JsonValue};
use serde::de::DeserializeOwned;
use serde::Serialize;

use crate::types::{
    CheckpointInfo, ConversationId, ConversationSemantics, DocumentAddress, DocumentCreate,
    DocumentId, DocumentIdentity, DocumentRecordScope, DocumentScope, DocumentSemantics,
    LatestFork, RewindableFork, StoredDocument, TaskId,
};

/// Error returned by a user document callback (`migrate`).
pub type CallbackError = Box<dyn Error + Send + Sync + 'static>;

/// Largest version a definition may declare (`Number.MAX_SAFE_INTEGER`).
const MAX_VERSION: u64 = (1 << 53) - 1;

/// Converts a value stored at an older version (`migrate?(value, fromVersion)`).
pub type MigrateFn<T> = fn(&JsonObject, u64) -> Result<T, CallbackError>;

/// Returns true to store an ordinary change as a complete base instead of a
/// delta (`checkpointWhen?(value, ops, info)`). Receives the untyped value,
/// so a predicate never pays for decoding the typed one.
pub type CheckpointWhenFn = fn(&JsonObject, &[Op], CheckpointInfo) -> bool;

/// Singleton definition fields (TS `CommonDocDefinition<T>`).
pub struct DocDefinition<T> {
    /// Stable persisted kind; part of the public protocol.
    pub kind: &'static str,
    /// Positive integer version of the stored value shape.
    pub version: u64,
    /// The value of a newly created document; must serialize to a JSON object.
    pub initial: fn() -> T,
    /// Converts a value stored by any older supported version.
    pub migrate: Option<MigrateFn<T>>,
    /// Selects complete storage bases to bound replay.
    pub checkpoint_when: Option<CheckpointWhenFn>,
}

/// Keyed family definition fields (TS `DocFamilyDefinition<T, I>` without
/// semantics); `initial(seed)` runs only when a member is absent.
pub struct DocFamilyDefinition<T, I> {
    /// Stable persisted kind; part of the public protocol.
    pub kind: &'static str,
    /// Positive integer version of the stored value shape.
    pub version: u64,
    /// The value of a newly created member; must serialize to a JSON object.
    pub initial: fn(I) -> T,
    /// Converts a value stored by any older supported version.
    pub migrate: Option<MigrateFn<T>>,
    /// Selects complete storage bases to bound replay.
    pub checkpoint_when: Option<CheckpointWhenFn>,
}

impl<T> Clone for DocDefinition<T> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<T> Copy for DocDefinition<T> {}

impl<T, I> Clone for DocFamilyDefinition<T, I> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<T, I> Copy for DocFamilyDefinition<T, I> {}

impl<T> fmt::Debug for DocDefinition<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("DocDefinition")
            .field("kind", &self.kind)
            .field("version", &self.version)
            .finish_non_exhaustive()
    }
}

impl<T, I> fmt::Debug for DocFamilyDefinition<T, I> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("DocFamilyDefinition")
            .field("kind", &self.kind)
            .field("version", &self.version)
            .finish_non_exhaustive()
    }
}

/// A definition whose version is not a positive safe integer (TS `TypeError`).
#[derive(Debug, Clone, Copy, PartialEq, Eq, thiserror::Error)]
#[error("Document {kind} version must be a positive integer")]
pub struct DefinitionError {
    /// The definition's kind.
    pub kind: &'static str,
}

const fn validate_version(kind: &'static str, version: u64) -> Result<(), DefinitionError> {
    if version == 0 || version > MAX_VERSION {
        return Err(DefinitionError { kind });
    }
    Ok(())
}

/// Failure of typed document access.
#[derive(Debug, Clone, thiserror::Error)]
pub enum DocumentError {
    /// An erased owner argument was missing or not a safe integer (TS `TypeError`).
    #[error("Document {kind} requires a {scope} ID")]
    MissingOwner {
        /// The definition's kind.
        kind: String,
        /// `"conversation"` or `"task"`.
        scope: &'static str,
    },
    /// The token's scope, history, or fork disagrees with the persisted
    /// incarnation (TS `TypeError`).
    #[error("Document {id} ({kind}) does not match the supplied definition semantics")]
    SemanticsMismatch {
        /// The incarnation.
        id: DocumentId,
        /// Its kind.
        kind: String,
    },
    /// The stored version is newer than the definition.
    #[error("Document {id} ({kind}) has newer version {version} than {supported}")]
    NewerVersion {
        /// The incarnation.
        id: DocumentId,
        /// Its kind.
        kind: String,
        /// The stored version.
        version: u64,
        /// The definition's version.
        supported: u64,
    },
    /// The stored version is older and the definition has no `migrate`.
    #[error("Document {id} ({kind}) requires migration from version {version}")]
    MigrationRequired {
        /// The incarnation.
        id: DocumentId,
        /// Its kind.
        kind: String,
        /// The stored version.
        version: u64,
    },
    /// `migrate` failed.
    #[error(transparent)]
    Migrate(Arc<dyn Error + Send + Sync + 'static>),
    /// A typed value did not serialize to a JSON object (enforced by the TS
    /// type `T extends JsonObject`).
    #[error("Document {kind} value is not a JSON object")]
    NotAnObject {
        /// The definition's kind.
        kind: String,
    },
    /// A typed value or seed failed to convert to or from JSON.
    #[error(transparent)]
    Json(Arc<JsonError>),
}

impl From<JsonError> for DocumentError {
    fn from(error: JsonError) -> Self {
        Self::Json(Arc::new(error))
    }
}

/// The erased definition the Session uses after overload resolution (TS
/// `AnyDocDefinition`). Implemented by every token type; object-safe, so the
/// Session can hold `Arc<dyn AnyDocDefinition>`.
pub trait AnyDocDefinition: Send + Sync + 'static {
    /// Stable persisted kind.
    fn kind(&self) -> &'static str;
    /// Current definition version.
    fn version(&self) -> u64;
    /// Scope and conversation history/fork semantics.
    fn semantics(&self) -> DocumentSemantics;
    /// Whether this is a keyed family.
    fn is_family(&self) -> bool;
    /// Whether the definition declares `migrate`.
    fn has_migrate(&self) -> bool;
    /// The initial value; families decode `seed` (`None` reads as `null`),
    /// singletons ignore it.
    ///
    /// # Errors
    /// The seed does not decode, or the value is not a JSON object.
    fn initial(&self, seed: Option<&JsonValue>) -> Result<Arc<JsonObject>, DocumentError>;
    /// The migrated value, or `None` when the definition has no `migrate`.
    fn migrate(
        &self,
        value: &JsonObject,
        from_version: u64,
    ) -> Option<Result<Arc<JsonObject>, DocumentError>>;
    /// Whether to store this ordinary change as a complete base; false
    /// without a `checkpoint_when`.
    fn checkpoint_when(&self, value: &JsonObject, ops: &[Op], info: CheckpointInfo) -> bool;
}

/// A typed document token (TS `DocToken` / `DocFamilyToken`). `Locator` is
/// the owner and family-key argument list of the TS overloads; `Seed` is the
/// creation seed (`()` for singletons).
pub trait DocToken: AnyDocDefinition + Copy {
    /// The typed document value `T`.
    type Value: Serialize + DeserializeOwned;
    /// Owner and key: `()`, `ConversationId`, `TaskId`, `&str`,
    /// `(ConversationId, &str)`, or `(TaskId, &str)`.
    type Locator<'a>: Copy;
    /// The family creation seed `I`; `()` for singletons.
    type Seed;

    /// The logical address the locator selects (TS `resolveAddress`).
    fn address(&self, locator: Self::Locator<'_>) -> DocumentAddress;

    /// The seed as JSON for [`AnyDocDefinition::initial`]; `None` for singletons.
    ///
    /// # Errors
    /// The seed is not strict JSON.
    fn encode_seed(&self, seed: &Self::Seed) -> Result<Option<JsonValue>, DocumentError>;
}

/// A singleton token: `tx.doc(token, owner)`.
pub trait SingletonDocToken: DocToken<Seed = ()> {}

/// A family token: `tx.doc(token, owner, key, seed)`.
pub trait FamilyDocToken: DocToken {}

/// A rewindable conversation token, accepted by `snapshotAsOf`.
pub trait RewindableDocToken: DocToken {}

fn object_of<T: Serialize>(kind: &str, value: &T) -> Result<Arc<JsonObject>, DocumentError> {
    match to_json(value)? {
        JsonValue::Object(object) => Ok(object),
        _ => Err(DocumentError::NotAnObject {
            kind: kind.to_owned(),
        }),
    }
}

fn migrate_with<T: Serialize>(
    kind: &str,
    migrate: Option<MigrateFn<T>>,
    value: &JsonObject,
    from_version: u64,
) -> Option<Result<Arc<JsonObject>, DocumentError>> {
    let migrate = migrate?;
    Some(
        migrate(value, from_version)
            .map_err(|error| DocumentError::Migrate(Arc::from(error)))
            .and_then(|migrated| object_of(kind, &migrated)),
    )
}

fn address_at(kind: &'static str, scope: DocumentScope, key: Option<&str>) -> DocumentAddress {
    DocumentAddress {
        kind: kind.to_owned(),
        scope,
        key: key.map(str::to_owned),
    }
}

macro_rules! singleton_token {
    (
        $(#[$meta:meta])*
        $name:ident { $($field:ident: $field_ty:ty),* },
        semantics: |$this:ident| $semantics:expr,
        locator: <$lt:lifetime> $locator:ty => |$owner:pat_param| $scope:expr,
        define: ($($arg:ident: $arg_ty:ty),*)
    ) => {
        $(#[$meta])*
        pub struct $name<T> {
            definition: DocDefinition<T>,
            $($field: $field_ty,)*
        }

        impl<T> $name<T> {
            /// Validate `definition` and build the token (TS `defineDoc`).
            ///
            /// # Errors
            /// The version is not a positive safe integer.
            pub const fn define(definition: DocDefinition<T> $(, $arg: $arg_ty)*) -> Result<Self, DefinitionError> {
                match validate_version(definition.kind, definition.version) {
                    Ok(()) => Ok(Self { definition $(, $field: $arg)* }),
                    Err(error) => Err(error),
                }
            }

            /// The definition.
            #[must_use]
            pub const fn definition(&self) -> &DocDefinition<T> {
                &self.definition
            }
        }

        impl<T> Clone for $name<T> {
            fn clone(&self) -> Self {
                *self
            }
        }

        impl<T> Copy for $name<T> {}

        impl<T> fmt::Debug for $name<T> {
            fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                f.debug_struct(stringify!($name)).field("definition", &self.definition)$(.field(stringify!($field), &self.$field))*.finish()
            }
        }

        impl<T: Serialize + DeserializeOwned + 'static> AnyDocDefinition for $name<T> {
            fn kind(&self) -> &'static str {
                self.definition.kind
            }

            fn version(&self) -> u64 {
                self.definition.version
            }

            fn semantics(&self) -> DocumentSemantics {
                let $this = self;
                $semantics
            }

            fn is_family(&self) -> bool {
                false
            }

            fn has_migrate(&self) -> bool {
                self.definition.migrate.is_some()
            }

            fn initial(&self, _seed: Option<&JsonValue>) -> Result<Arc<JsonObject>, DocumentError> {
                object_of(self.definition.kind, &(self.definition.initial)())
            }

            fn migrate(&self, value: &JsonObject, from_version: u64) -> Option<Result<Arc<JsonObject>, DocumentError>> {
                migrate_with(self.definition.kind, self.definition.migrate, value, from_version)
            }

            fn checkpoint_when(&self, value: &JsonObject, ops: &[Op], info: CheckpointInfo) -> bool {
                self.definition.checkpoint_when.is_some_and(|when| when(value, ops, info))
            }
        }

        impl<T: Serialize + DeserializeOwned + 'static> DocToken for $name<T> {
            type Value = T;
            type Locator<$lt> = $locator;
            type Seed = ();

            fn address(&self, $owner: Self::Locator<'_>) -> DocumentAddress {
                address_at(self.definition.kind, $scope, None)
            }

            fn encode_seed(&self, _seed: &()) -> Result<Option<JsonValue>, DocumentError> {
                Ok(None)
            }
        }

        impl<T: Serialize + DeserializeOwned + 'static> SingletonDocToken for $name<T> {}
    };
}

macro_rules! family_token {
    (
        $(#[$meta:meta])*
        $name:ident { $($field:ident: $field_ty:ty),* },
        semantics: |$this:ident| $semantics:expr,
        locator: <$lt:lifetime> $locator:ty => |$owner:pat_param| ($scope:expr, $key:expr),
        define: ($($arg:ident: $arg_ty:ty),*)
    ) => {
        $(#[$meta])*
        pub struct $name<T, I> {
            definition: DocFamilyDefinition<T, I>,
            $($field: $field_ty,)*
        }

        impl<T, I> $name<T, I> {
            /// Validate `definition` and build the token (TS `defineDocFamily`).
            ///
            /// # Errors
            /// The version is not a positive safe integer.
            pub const fn define(
                definition: DocFamilyDefinition<T, I> $(, $arg: $arg_ty)*
            ) -> Result<Self, DefinitionError> {
                match validate_version(definition.kind, definition.version) {
                    Ok(()) => Ok(Self { definition $(, $field: $arg)* }),
                    Err(error) => Err(error),
                }
            }

            /// The definition.
            #[must_use]
            pub const fn definition(&self) -> &DocFamilyDefinition<T, I> {
                &self.definition
            }
        }

        impl<T, I> Clone for $name<T, I> {
            fn clone(&self) -> Self {
                *self
            }
        }

        impl<T, I> Copy for $name<T, I> {}

        impl<T, I> fmt::Debug for $name<T, I> {
            fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                f.debug_struct(stringify!($name)).field("definition", &self.definition)$(.field(stringify!($field), &self.$field))*.finish()
            }
        }

        impl<T, I> AnyDocDefinition for $name<T, I>
        where
            T: Serialize + DeserializeOwned + 'static,
            I: Serialize + DeserializeOwned + 'static,
        {
            fn kind(&self) -> &'static str {
                self.definition.kind
            }

            fn version(&self) -> u64 {
                self.definition.version
            }

            fn semantics(&self) -> DocumentSemantics {
                let $this = self;
                $semantics
            }

            fn is_family(&self) -> bool {
                true
            }

            fn has_migrate(&self) -> bool {
                self.definition.migrate.is_some()
            }

            fn initial(&self, seed: Option<&JsonValue>) -> Result<Arc<JsonObject>, DocumentError> {
                let seed: I = from_json(seed.unwrap_or(&JsonValue::Null))?;
                object_of(self.definition.kind, &(self.definition.initial)(seed))
            }

            fn migrate(&self, value: &JsonObject, from_version: u64) -> Option<Result<Arc<JsonObject>, DocumentError>> {
                migrate_with(self.definition.kind, self.definition.migrate, value, from_version)
            }

            fn checkpoint_when(&self, value: &JsonObject, ops: &[Op], info: CheckpointInfo) -> bool {
                self.definition.checkpoint_when.is_some_and(|when| when(value, ops, info))
            }
        }

        impl<T, I> DocToken for $name<T, I>
        where
            T: Serialize + DeserializeOwned + 'static,
            I: Serialize + DeserializeOwned + 'static,
        {
            type Value = T;
            type Locator<$lt> = $locator;
            type Seed = I;

            fn address(&self, $owner: Self::Locator<'_>) -> DocumentAddress {
                address_at(self.definition.kind, $scope, Some($key))
            }

            fn encode_seed(&self, seed: &I) -> Result<Option<JsonValue>, DocumentError> {
                Ok(Some(to_json(seed)?))
            }
        }

        impl<T, I> FamilyDocToken for $name<T, I>
        where
            T: Serialize + DeserializeOwned + 'static,
            I: Serialize + DeserializeOwned + 'static,
        {
        }
    };
}

singleton_token!(
    /// Session-scoped singleton document (TS `SessionDocToken<T>`); access takes no owner.
    SessionDoc {},
    semantics: |_token| DocumentSemantics::Session,
    locator: <'a> () => |()| DocumentScope::Session,
    define: ()
);

singleton_token!(
    /// Latest-only conversation singleton document (TS `ConversationDocToken<T>`
    /// with `history: "latest"`); access takes the conversation ID.
    ConversationDoc { fork: LatestFork },
    semantics: |token| DocumentSemantics::Conversation(ConversationSemantics::Latest(token.fork)),
    locator: <'a> ConversationId => |conversation_id| DocumentScope::Conversation { conversation_id },
    define: (fork: LatestFork)
);

singleton_token!(
    /// Rewindable conversation singleton document (TS
    /// `RewindableConversationDocToken<T>`); access takes the conversation ID.
    RewindableConversationDoc { fork: RewindableFork },
    semantics: |token| DocumentSemantics::Conversation(ConversationSemantics::Rewindable(token.fork)),
    locator: <'a> ConversationId => |conversation_id| DocumentScope::Conversation { conversation_id },
    define: (fork: RewindableFork)
);

singleton_token!(
    /// Task-scoped singleton document (TS `TaskDocToken<T>`); access takes the task ID.
    TaskDoc {},
    semantics: |_token| DocumentSemantics::Task,
    locator: <'a> TaskId => |task_id| DocumentScope::Task { task_id },
    define: ()
);

family_token!(
    /// Session-scoped document family (TS `SessionDocFamilyToken<T, I>`); access takes the key.
    SessionDocFamily {},
    semantics: |_token| DocumentSemantics::Session,
    locator: <'a> &'a str => |key| (DocumentScope::Session, key),
    define: ()
);

family_token!(
    /// Latest-only conversation document family (TS
    /// `ConversationDocFamilyToken<T, I>` with `history: "latest"`); access
    /// takes the conversation ID and key.
    ConversationDocFamily { fork: LatestFork },
    semantics: |token| DocumentSemantics::Conversation(ConversationSemantics::Latest(token.fork)),
    locator: <'a> (ConversationId, &'a str) => |(conversation_id, key)| (DocumentScope::Conversation { conversation_id }, key),
    define: (fork: LatestFork)
);

family_token!(
    /// Rewindable conversation document family (TS
    /// `RewindableConversationDocFamilyToken<T, I>`); access takes the
    /// conversation ID and key.
    RewindableConversationDocFamily { fork: RewindableFork },
    semantics: |token| DocumentSemantics::Conversation(ConversationSemantics::Rewindable(token.fork)),
    locator: <'a> (ConversationId, &'a str) => |(conversation_id, key)| (DocumentScope::Conversation { conversation_id }, key),
    define: (fork: RewindableFork)
);

family_token!(
    /// Task-scoped document family (TS `TaskDocFamilyToken<T, I>`); access
    /// takes the task ID and key.
    TaskDocFamily {},
    semantics: |_token| DocumentSemantics::Task,
    locator: <'a> (TaskId, &'a str) => |(task_id, key)| (DocumentScope::Task { task_id }, key),
    define: ()
);

impl<T: Serialize + DeserializeOwned + 'static> RewindableDocToken
    for RewindableConversationDoc<T>
{
}

impl<T, I> RewindableDocToken for RewindableConversationDocFamily<T, I>
where
    T: Serialize + DeserializeOwned + 'static,
    I: Serialize + DeserializeOwned + 'static,
{
}

/// Logical address plus its string identity for maps.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct ResolvedAddress {
    /// The logical address.
    pub address: DocumentAddress,
    /// Its [`address_id`].
    pub id: String,
}

/// Resolve a typed token's owner/key arguments to an address.
#[must_use]
pub fn resolve_token_address<D: DocToken>(token: &D, locator: D::Locator<'_>) -> ResolvedAddress {
    let address = token.address(locator);
    let id = address_id(&address);
    ResolvedAddress { address, id }
}

/// Resolve erased arguments: `owner` is the conversation or task ID a
/// conversation or task definition requires (ignored for Session
/// definitions), `key` the family key (ignored for singletons). TS
/// `resolveAddress` without the argument-index bookkeeping its runtime
/// overload dispatch needs.
///
/// # Errors
/// A conversation or task definition without a safe-integer owner.
pub fn resolve_address<D: AnyDocDefinition + ?Sized>(
    definition: &D,
    owner: Option<u64>,
    key: Option<&str>,
) -> Result<ResolvedAddress, DocumentError> {
    let owner_id = |scope: &'static str| {
        owner
            .filter(|&id| id <= MAX_VERSION)
            .ok_or_else(|| DocumentError::MissingOwner {
                kind: definition.kind().to_owned(),
                scope,
            })
    };
    let scope = match definition.semantics() {
        DocumentSemantics::Session => DocumentScope::Session,
        DocumentSemantics::Conversation(_) => DocumentScope::Conversation {
            conversation_id: ConversationId::from_number(owner_id("conversation")?),
        },
        DocumentSemantics::Task => DocumentScope::Task {
            task_id: TaskId::from_number(owner_id("task")?),
        },
    };
    let key = if definition.is_family() { key } else { None };
    let address = address_at(definition.kind(), scope, key);
    let id = address_id(&address);
    Ok(ResolvedAddress { address, id })
}

/// Stable string identity of one logical address:
/// `JSON.stringify([kind, scope.kind, owner, key ?? null])`.
#[must_use]
pub fn address_id(address: &DocumentAddress) -> String {
    let owner = match address.scope {
        DocumentScope::Session => "null".to_owned(),
        DocumentScope::Conversation { conversation_id } => conversation_id.to_string(),
        DocumentScope::Task { task_id } => task_id.to_string(),
    };
    let key = address
        .key
        .as_deref()
        .map_or_else(|| "null".to_owned(), |key| JsonValue::from(key).to_string());
    format!(
        "[{},{},{owner},{key}]",
        JsonValue::from(address.kind.as_str()),
        JsonValue::from(address.scope.name()),
    )
}

/// Build the storage create record for a new incarnation at an address.
///
/// # Errors
/// The address has a conversation scope but the definition is not a
/// conversation definition (TS would build a record without history/fork).
pub fn document_create<D: AnyDocDefinition + ?Sized>(
    definition: &D,
    address: &DocumentAddress,
    id: DocumentId,
) -> Result<DocumentCreate, DocumentError> {
    let scope = match (address.scope, definition.semantics()) {
        (DocumentScope::Session, _) => DocumentRecordScope::Session,
        (DocumentScope::Task { task_id }, _) => DocumentRecordScope::Task { task_id },
        (
            DocumentScope::Conversation { conversation_id },
            DocumentSemantics::Conversation(semantics),
        ) => DocumentRecordScope::Conversation {
            conversation_id,
            semantics,
        },
        (
            DocumentScope::Conversation { .. },
            DocumentSemantics::Session | DocumentSemantics::Task,
        ) => {
            return Err(DocumentError::SemanticsMismatch {
                id,
                kind: address.kind.clone(),
            });
        }
    };
    Ok(DocumentCreate {
        id,
        kind: address.kind.clone(),
        key: address.key.clone(),
        scope,
    })
}

/// Reject typed access whose token disagrees with the persisted scope,
/// history, or fork semantics.
///
/// # Errors
/// [`DocumentError::SemanticsMismatch`].
pub fn check_record_scope<D: AnyDocDefinition + ?Sized>(
    definition: &D,
    record: &(impl DocumentIdentity + ?Sized),
) -> Result<(), DocumentError> {
    if record.record_scope().semantics() != definition.semantics() {
        return Err(DocumentError::SemanticsMismatch {
            id: record.id(),
            kind: record.kind().to_owned(),
        });
    }
    Ok(())
}

/// Reject typed access to a stored version the supplied definition cannot use.
///
/// # Errors
/// [`DocumentError::NewerVersion`] or [`DocumentError::MigrationRequired`].
pub fn check_record_version<D: AnyDocDefinition + ?Sized>(
    definition: &D,
    record: &(impl DocumentIdentity + ?Sized),
    version: u64,
) -> Result<(), DocumentError> {
    if version > definition.version() {
        return Err(DocumentError::NewerVersion {
            id: record.id(),
            kind: record.kind().to_owned(),
            version,
            supported: definition.version(),
        });
    }
    if version < definition.version() && !definition.has_migrate() {
        return Err(DocumentError::MigrationRequired {
            id: record.id(),
            kind: record.kind().to_owned(),
            version,
        });
    }
    Ok(())
}

/// Validate and materialize a detached stored value for typed access.
///
/// # Errors
/// See [`materialize_document_value`].
pub fn materialize_document<D: AnyDocDefinition + ?Sized>(
    definition: &D,
    stored: &StoredDocument,
) -> Result<Arc<JsonObject>, DocumentError> {
    materialize_document_value(definition, &stored.record, stored.version, &stored.value)
}

/// Validate and materialize one detached value before its first persisted
/// incarnation. A current-version value is returned as is; an older one is
/// migrated into a fresh object.
///
/// # Errors
/// Scope or version checks fail, or `migrate` fails.
pub fn materialize_document_value<D: AnyDocDefinition + ?Sized>(
    definition: &D,
    record: &(impl DocumentIdentity + ?Sized),
    version: u64,
    value: &Arc<JsonObject>,
) -> Result<Arc<JsonObject>, DocumentError> {
    check_record_scope(definition, record)?;
    check_record_version(definition, record, version)?;
    if version == definition.version() {
        return Ok(Arc::clone(value));
    }
    definition.migrate(value, version).unwrap_or_else(|| {
        Err(DocumentError::MigrationRequired {
            id: record.id(),
            kind: record.kind().to_owned(),
            version,
        })
    })
}

#[cfg(test)]
mod tests;
