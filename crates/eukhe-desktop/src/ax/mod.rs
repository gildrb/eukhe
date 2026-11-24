//! Accessibility trees: element props, the read seam, the ref registry, the
//! `[ref=eN]` text tree (port of omp `crates/natives/src/desktop/ax.rs`).

mod readback;
mod registry;
mod role;
mod stale;
pub(crate) mod tree;

use std::fmt;
use std::hash::{DefaultHasher, Hash, Hasher};
use std::str::FromStr;

use serde::{Deserialize, Deserializer, Serialize, Serializer};

use crate::error::Error;
use crate::geometry::ElementBounds;
use crate::types::{Focus, Window};

pub(crate) use readback::{text_readback, FieldKind};
pub(crate) use registry::Registry;
pub use role::{Role, TextLines};
pub(crate) use stale::{find_read_as, follow_row, refind_in, WindowRead};
pub(crate) use tree::{query, snapshot, SnapshotLimits};
pub use tree::{FindQuery, FoundNode, Tree, TreeOptions, TreeScope, Truncation};

/// A ref an observation printed as `[ref=eN]`.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct ElementRef(u64);

impl fmt::Display for ElementRef {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "e{}", self.0)
    }
}

/// Why a ref did not parse.
#[derive(Clone, Debug, PartialEq, Eq, thiserror::Error)]
#[error("{0:?} is not a ref; refs look like e12")]
pub struct RefSyntax(String);

impl FromStr for ElementRef {
    type Err = RefSyntax;

    fn from_str(text: &str) -> Result<Self, RefSyntax> {
        text.strip_prefix('e')
            .and_then(|digits| digits.parse().ok())
            .map(Self)
            .ok_or_else(|| RefSyntax(text.to_owned()))
    }
}

impl Serialize for ElementRef {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        serializer.collect_str(self)
    }
}

impl<'de> Deserialize<'de> for ElementRef {
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        std::borrow::Cow::<'de, str>::deserialize(deserializer)?
            .parse()
            .map_err(serde::de::Error::custom)
    }
}

/// Hash of the fields that tell an element apart in its window.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub(crate) struct Identity(pub(crate) u64);

/// Hash of the role and label a ref was read with.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub(crate) struct Fingerprint(u64);

/// Whether an element takes input.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum Availability {
    Enabled,
    Disabled,
}

/// Whether a row, cell, button or file icon reports itself selected.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum Selection {
    Selected,
    Unselected,
}

/// Whether the backend read every field one read of an element needs.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[allow(dead_code, reason = "the platform backends construct both variants")]
pub(crate) enum Completeness {
    Whole,
    Partial,
}

/// Children an element has that a walk did not read.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[allow(dead_code, reason = "the platform backends construct both variants")]
pub(crate) enum Unread {
    Count(u32),
    /// Their count could not be read.
    Unknown,
}

impl Unread {
    pub(crate) fn add(self, other: Self) -> Self {
        match (self, other) {
            (Self::Count(a), Self::Count(b)) => Self::Count(a.saturating_add(b)),
            (Self::Unknown, _) | (_, Self::Unknown) => Self::Unknown,
        }
    }

    pub(crate) fn any(self) -> bool {
        match self {
            Self::Count(count) => count > 0,
            Self::Unknown => true,
        }
    }
}

/// One read of an element, as a backend answers it.
#[derive(Clone, Debug, PartialEq)]
#[allow(dead_code, reason = "the platform backends construct it")]
pub(crate) struct AxProps {
    pub(crate) role: Role,
    /// The platform's own role name.
    pub(crate) native_role: String,
    pub(crate) title: Option<String>,
    pub(crate) value: Option<String>,
    pub(crate) description: Option<String>,
    /// A name the platform derives when the element has neither title nor
    /// description, such as a window's close button.
    pub(crate) role_name: Option<String>,
    pub(crate) availability: Availability,
    pub(crate) focus: Focus,
    pub(crate) selection: Selection,
    pub(crate) bounds: Option<ElementBounds>,
    pub(crate) actions: Vec<String>,
    pub(crate) child_count: u32,
    /// `None` where the backend reads no identity or could not read it all.
    pub(crate) identity: Option<Identity>,
    /// `Partial`: an identifying field or the children of an element still
    /// there could not be read, so a walk that met it proves no uniqueness.
    pub(crate) fields: Completeness,
    /// Whether the role and every field the label is chosen from answered.
    pub(crate) label_read: Completeness,
    pub(crate) unread_children: Unread,
}

impl AxProps {
    /// The display and match name: title, else description, else the
    /// platform's derived name.
    pub(crate) fn label(&self) -> Option<&str> {
        [&self.title, &self.description, &self.role_name]
            .into_iter()
            .filter_map(|label| Some(label.as_deref()?.trim()))
            .find(|label| !label.is_empty())
    }

    /// The role and label a ref is held to.
    pub(crate) fn fingerprint(&self) -> Fingerprint {
        fingerprint(&self.role, self.label())
    }

    fn named(&self) -> bool {
        [&self.title, &self.value, &self.description]
            .into_iter()
            .flatten()
            .any(|text| !text.trim().is_empty())
    }
}

pub(crate) fn fingerprint(role: &Role, label: Option<&str>) -> Fingerprint {
    let mut hasher = DefaultHasher::new();
    role.hash(&mut hasher);
    label.hash(&mut hasher);
    Fingerprint(hasher.finish())
}

/// Whether a tree walk reads each element's bounds: `ax` lines print none,
/// `find` results carry them.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum WalkBounds {
    Read,
    Skip,
}

/// Whether the element a handle was read from still exists.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[allow(dead_code, reason = "the platform backends construct both variants")]
pub(crate) enum Liveness {
    Alive,
    Gone,
}

/// Whether an element answers that its value can be written.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[allow(dead_code, reason = "the platform backends construct every variant")]
pub(crate) enum Settable {
    Yes,
    No,
    /// No answer, or the backend cannot ask.
    Unknown,
}

/// How a line lists an element's actions: macOS names are performable
/// (`AXPress` → `press`); AT-SPI names are provider-defined, so none show.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[allow(dead_code, reason = "each backend uses one variant")]
pub(crate) enum ActionNames {
    Ax,
    Hidden,
}

/// Reads one application's accessibility tree.
///
/// Implemented by the platform `Backend`; tests implement it over a fixed
/// tree. Handles compare equal when they name the same live element, however
/// many reads produced them. Every call reads live state; none caches.
pub(crate) trait AxRead {
    type Handle: Clone + Eq + Hash;

    /// The window element of `window`.
    fn window_root(&mut self, window: &Window) -> Result<Self::Handle, Error>;
    /// One element and its children. With very many children the backend
    /// may read only the first `max_children`, counting the rest in
    /// [`AxProps::unread_children`]. `Refusal::Vanished` when the element is
    /// gone.
    fn walk_node(
        &mut self,
        handle: &Self::Handle,
        bounds: WalkBounds,
        max_children: u32,
    ) -> Result<(AxProps, Vec<Self::Handle>), Error>;
    /// One element, bounds included.
    fn props(&mut self, handle: &Self::Handle) -> Result<AxProps, Error>;
    /// Whether the element still exists; backends whose identities a later
    /// element can take over check it, so a ref never renews onto another.
    fn liveness(&mut self, handle: &Self::Handle) -> Liveness;
    /// The element holding keyboard focus in `handle`'s application, when
    /// the backend reads focus per application.
    fn focused_within(&mut self, handle: &Self::Handle) -> Option<Self::Handle>;
    /// Whether the element's value can be written.
    fn value_settable(&mut self, handle: &Self::Handle) -> Settable;
}

#[cfg(test)]
pub(crate) mod fake;
