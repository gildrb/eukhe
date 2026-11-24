//! The backend seam: what the core asks of the platform (port of the
//! `Backend`/`AxBackend` traits of omp `crates/natives/src/desktop/backend.rs`,
//! as compile-time modules instead of trait objects).
//!
//! `crate::platform` is `macos` or `linux` by `cfg(target_os)`. Each exposes
//! the same items:
//! - `Backend`: owned by the session worker thread, never shared; `open()`,
//!   `capabilities`, `windows`, `capture`, `input_held`, `admit_takeover`,
//!   the element steps (`press`, `set_value`, `element_input`, `text_value`,
//!   `select_range`), the window steps (`window_input`, `pointer`), and
//!   `menu_items`/`menu_press`; plus `impl AxRead for Backend`.
//! - `AxHandle`: `Clone + Eq + Hash`, equal for the same live element.
//! - free functions `list_applications`, `application_at`, `app_kind`,
//!   `open_application`, `open_document`, `window_roster`, `process_started`.
//! - `UserInputMonitor::start` and `EscapeMonitor::start`: monitors whose
//!   threads feed the session until dropped.
//! - consts `BACKEND`, `ACTION_NAMES`, `OPENS_DOCUMENTS`.
//!
//! Every step method follows one contract: in `DeliveryMode::Background` it
//! never activates the target nor moves the pointer, and refuses with
//! `BackgroundUnavailable` before sending when it cannot; it calls
//! [`Delivery::before_press`] before each press it sends; an error says
//! whether input went out (`Refused` nothing, `Unverified` some). Element
//! steps report a destroyed element as `Refusal::Vanished`. A feature the
//! backend lacks is `Refusal::Unsupported`.

use serde::{Deserialize, Serialize};

use crate::control::intervention::InputWatch;
use crate::control::{Sent, Token};
use crate::error::Error;
use crate::geometry::{GlobalPoint, ScrollDelta};
use crate::keys::{Chord, Modifiers};
use crate::text_range::Utf16Range;
use crate::types::{DeliveryMode, Focus, MenuPress};

pub(crate) use crate::ax::FieldKind;

/// How one attempt of a step reaches its window.
#[allow(
    dead_code,
    reason = "the platform backends read the mode and menu policy"
)]
pub(crate) struct Delivery<'a> {
    pub(crate) mode: DeliveryMode,
    /// Whether a background press that opens a control's menu is refused.
    pub(crate) menus: MenuPress,
    token: &'a Token,
    watch: &'a InputWatch,
}

#[allow(dead_code, reason = "called by the platform backends")]
impl<'a> Delivery<'a> {
    pub(crate) fn new(
        mode: DeliveryMode,
        menus: MenuPress,
        token: &'a Token,
        watch: &'a InputWatch,
    ) -> Self {
        Self {
            mode,
            menus,
            token,
            watch,
        }
    }

    /// Before each press: refuses on a cancel or the user's own input, as
    /// `Refused` when `sent` is nothing yet, else `Unverified`.
    pub(crate) fn before_press(&self, sent: Sent) -> Result<(), Error> {
        self.token.check_sent(sent)?;
        self.watch.check_press(sent)
    }

    /// The step's cancellation, for waits between presses.
    pub(crate) fn token(&self) -> &Token {
        self.token
    }

    /// The step's watch on the user's input, to route a helper process.
    pub(crate) fn watch(&self) -> &InputWatch {
        self.watch
    }
}

/// A mouse button.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum MouseButton {
    #[default]
    Left,
    Right,
    Middle,
}

/// Clicks in one gesture: 1 to 3.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(try_from = "u8", into = "u8")]
pub struct ClickCount(u8);

impl ClickCount {
    pub const SINGLE: Self = Self(1);

    #[must_use]
    pub const fn get(self) -> u8 {
        self.0
    }
}

impl Default for ClickCount {
    fn default() -> Self {
        Self::SINGLE
    }
}

impl TryFrom<u8> for ClickCount {
    type Error = ClickCountRange;

    fn try_from(count: u8) -> Result<Self, ClickCountRange> {
        (1..=3)
            .contains(&count)
            .then_some(Self(count))
            .ok_or(ClickCountRange(count))
    }
}

impl From<ClickCount> for u8 {
    fn from(count: ClickCount) -> Self {
        count.0
    }
}

/// A click count outside 1 to 3.
#[derive(Clone, Copy, Debug, PartialEq, Eq, thiserror::Error)]
#[error("click count {0} is outside 1 to 3")]
pub struct ClickCountRange(u8);

/// Pointer input at a global point.
#[derive(Clone, Copy, Debug, PartialEq)]
#[allow(dead_code, reason = "the platform backends read every field")]
pub(crate) enum PointerEvent {
    Click {
        at: GlobalPoint,
        button: MouseButton,
        count: ClickCount,
        modifiers: Modifiers,
    },
    Scroll {
        at: GlobalPoint,
        delta: ScrollDelta,
    },
}

/// Keyboard input for an element or a window.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[allow(dead_code, reason = "the platform backends read both variants")]
pub(crate) enum Typing<'a> {
    Text(&'a str),
    Chord(Chord),
}

/// What an element's value reads right after `set_value` wrote it.
#[allow(dead_code, reason = "the platform backends construct it")]
pub(crate) struct ValueReadback {
    /// `None` when the value could not be read back.
    pub(crate) actual: Option<String>,
    pub(crate) field: FieldKind,
}

/// The selection an element reports right after `select_range`.
#[allow(dead_code, reason = "the platform backends construct it")]
pub(crate) struct SelectionReadback {
    pub(crate) range: Utf16Range,
    /// The element's value as read with the selection.
    pub(crate) value: String,
    pub(crate) focus: Focus,
}
