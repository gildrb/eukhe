//! Record identifiers and commit sequences (`types.ts` `Id`, `Seq`).
//!
//! IDs are plain numbers in memory, JSON, JSONL, and SQLite; the Rust newtypes
//! only keep record kinds apart at compile time, like the TS brands. Every ID
//! kind shares the one Session-global numeric namespace that
//! [`Storage::mint_id`](crate::types::Storage::mint_id) allocates from.

use std::fmt;
use std::hash::{Hash, Hasher};
use std::marker::PhantomData;

use eukhe_chord::json::JsonValue;
use serde::{Deserialize, Deserializer, Serialize, Serializer};

/// A typed number identifying one durable record kind (TS `Id<Kind>`).
///
/// Implemented by every ID newtype; [`crate::ids::id_from_number`] and
/// [`crate::ids::mint`] use it to brand a raw allocation.
pub trait DurableId:
    Copy + Eq + Ord + Hash + fmt::Debug + fmt::Display + Send + Sync + 'static
{
    /// The record kind of the brand: `"conversation"`, `"entry"`, `"task"`,
    /// `"submission"`, or `"document"`.
    const KIND: &'static str;

    /// Apply the brand to a raw number at a trusted allocation or decoding
    /// boundary.
    fn from_number(value: u64) -> Self;

    /// The raw number.
    fn get(self) -> u64;
}

macro_rules! durable_id {
    ($(#[$meta:meta])* $name:ident, $kind:literal) => {
        $(#[$meta])*
        #[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
        #[serde(transparent)]
        pub struct $name(u64);

        impl $name {
            /// Apply the brand to a raw number (TS `idFromNumber`).
            #[must_use]
            pub const fn from_number(value: u64) -> Self {
                Self(value)
            }

            /// The raw number.
            #[must_use]
            pub const fn get(self) -> u64 {
                self.0
            }
        }

        impl DurableId for $name {
            const KIND: &'static str = $kind;

            fn from_number(value: u64) -> Self {
                Self(value)
            }

            fn get(self) -> u64 {
                self.0
            }
        }

        impl fmt::Debug for $name {
            fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                write!(f, "{}({})", stringify!($name), self.0)
            }
        }

        /// Prints the bare number, as JS string interpolation does.
        impl fmt::Display for $name {
            fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                fmt::Display::fmt(&self.0, f)
            }
        }
    };
}

durable_id!(
    /// Identity of one conversation (TS `ConversationId`).
    ConversationId,
    "conversation"
);
durable_id!(
    /// Identity of one transcript entry (TS `EntryId`). Entry IDs are
    /// Session-global and ordered.
    EntryId,
    "entry"
);
durable_id!(
    /// Identity of one admitted submission (TS `SubmissionId`).
    SubmissionId,
    "submission"
);
durable_id!(
    /// Identity of one document incarnation (TS `DocumentId`); never reused.
    DocumentId,
    "document"
);

/// Identity of one durable task, carrying its result type `R` (TS
/// `TaskId<Result>`). `TaskId` without a parameter is the erased ID whose
/// result is untyped JSON, the TS `TaskId<unknown>`.
///
/// A typed ID widens with [`TaskId::erase`]; an erased ID cannot be narrowed
/// again, except by branding a raw number with [`TaskId::from_number`] at a
/// trusted typed source.
pub struct TaskId<R = JsonValue> {
    value: u64,
    result: PhantomData<fn() -> R>,
}

impl<R> TaskId<R> {
    /// Apply the brand to a raw number (TS `idFromNumber`).
    #[must_use]
    pub const fn from_number(value: u64) -> Self {
        Self {
            value,
            result: PhantomData,
        }
    }

    /// The raw number.
    #[must_use]
    pub const fn get(self) -> u64 {
        self.value
    }

    /// The same ID with its result type erased (TS widening `TaskId<R>` to `TaskId`).
    #[must_use]
    pub const fn erase(self) -> TaskId {
        TaskId::from_number(self.value)
    }
}

impl<R> Clone for TaskId<R> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<R> Copy for TaskId<R> {}

impl<R> PartialEq for TaskId<R> {
    fn eq(&self, other: &Self) -> bool {
        self.value == other.value
    }
}

impl<R> Eq for TaskId<R> {}

impl<R> PartialOrd for TaskId<R> {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl<R> Ord for TaskId<R> {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.value.cmp(&other.value)
    }
}

impl<R> Hash for TaskId<R> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.value.hash(state);
    }
}

impl<R> fmt::Debug for TaskId<R> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "TaskId({})", self.value)
    }
}

/// Prints the bare number, as JS string interpolation does.
impl<R> fmt::Display for TaskId<R> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(&self.value, f)
    }
}

impl<R> Serialize for TaskId<R> {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        serializer.serialize_u64(self.value)
    }
}

impl<'de, R> Deserialize<'de> for TaskId<R> {
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        u64::deserialize(deserializer).map(Self::from_number)
    }
}

impl<R: 'static> DurableId for TaskId<R> {
    const KIND: &'static str = "task";

    fn from_number(value: u64) -> Self {
        Self::from_number(value)
    }

    fn get(self) -> u64 {
        self.value
    }
}

/// Strictly increasing sequence assigned to one atomic storage commit; gaps
/// are permitted (TS `Seq`). A distinct type, so an entity ID cannot be used
/// as a document commit point.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
#[serde(transparent)]
pub struct Seq(u64);

impl Seq {
    /// Apply the sequence brand at a trusted storage boundary (TS `seqFromNumber`).
    #[must_use]
    pub const fn from_number(value: u64) -> Self {
        Self(value)
    }

    /// The raw number.
    #[must_use]
    pub const fn get(self) -> u64 {
        self.0
    }
}

impl fmt::Debug for Seq {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Seq({})", self.0)
    }
}

/// Prints the bare number, as JS string interpolation does.
impl fmt::Display for Seq {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(&self.0, f)
    }
}

/// The root conversation always uses this reserved ID.
pub const ROOT_CONVERSATION_ID: ConversationId = ConversationId::from_number(1);
