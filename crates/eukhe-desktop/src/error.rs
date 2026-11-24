//! Failures and step effects (port of omp `crates/natives/src/desktop/error.rs`).
//!
//! Every failure says whether input may have landed: [`Refusal`] means
//! nothing was sent, [`Unverified`] means some input may have landed. The
//! `Display` text is the model-facing message.

use std::borrow::Cow;
use std::fmt;
use std::time::Duration;

use serde::{Deserialize, Serialize};

use crate::applications::AppError;
use crate::ax::{ElementRef, Role};
use crate::frame::FrameError;
use crate::keys::KeyError;
use crate::menus::MenuError;
use crate::text_range::{TextRangeError, TextSelection};
use crate::types::{WindowFilter, WindowId, WindowSummary};

/// A failure's human-readable detail: a literal, or text built at the edge.
pub type Detail = Cow<'static, str>;

/// Why an operation did not complete.
#[derive(Clone, Debug, PartialEq, thiserror::Error, Serialize, Deserialize)]
#[serde(tag = "outcome", content = "reason", rename_all = "snake_case")]
pub enum Error {
    #[error(transparent)]
    Refused(#[from] Refusal),
    #[error(transparent)]
    Unverified(#[from] Unverified),
}

/// What one step did.
#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
#[serde(tag = "effect", rename_all = "snake_case")]
pub enum Effect {
    /// The step ran and its result was read back or is certain.
    Confirmed { done: Done },
    /// Input was sent, but what it did could not be confirmed.
    Unverifiable { reason: Unverified },
    /// Nothing was sent.
    Refused { reason: Refusal },
}

impl From<Error> for Effect {
    fn from(error: Error) -> Self {
        match error {
            Error::Refused(reason) => Self::Refused { reason },
            Error::Unverified(reason) => Self::Unverifiable { reason },
        }
    }
}

/// What a confirmed step produced.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub enum Done {
    Delivered,
    /// The selection `select_text` read back.
    Selected {
        selection: TextSelection,
    },
}

/// Nothing was sent. Adjacently tagged: the inner errors carry their own
/// `kind` tag, which would collide with this one in the same object.
#[derive(Clone, Debug, PartialEq, thiserror::Error, Serialize, Deserialize)]
#[serde(tag = "kind", content = "data", rename_all = "snake_case")]
pub enum Refusal {
    #[error("the desktop session is closed")]
    Closed,
    #[error("{permission} permission is not granted to the app that runs eukhe; nothing was sent")]
    NotPermitted { permission: Permission },
    #[error("no background route for this step: {detail}; nothing was sent")]
    BackgroundUnavailable { detail: Detail },
    #[error(transparent)]
    StaleRef(StaleRef),
    #[error(transparent)]
    UserIntervened(Intervention),
    #[error("{holder} holds desktop input control; nothing was sent")]
    InputBusy { holder: Holder },
    #[error("cancelled before any input was sent")]
    Cancelled,
    #[error(transparent)]
    Window(#[from] WindowError),
    #[error(transparent)]
    Frame(#[from] FrameError),
    #[error(transparent)]
    Key(#[from] KeyError),
    #[error(transparent)]
    Menu(#[from] MenuError),
    #[error(transparent)]
    Text(#[from] TextRangeError),
    #[error(transparent)]
    Application(#[from] AppError),
    #[error(transparent)]
    Element(#[from] ElementError),
    #[error("accessibility request failed: {detail}; nothing was sent")]
    Ax { detail: Detail },
    /// The app destroyed the element. The session turns it into
    /// [`Refusal::StaleRef`] when the element came from a ref.
    #[error("the app destroyed the element; nothing was sent")]
    Vanished,
    /// The element now reads with another role or label than its ref was
    /// read with. The session turns it into [`Refusal::StaleRef`].
    #[error("the element now reads as {role}{}; nothing was sent", Quoted(.label.as_deref()))]
    ReadsAs { role: Role, label: Option<String> },
    #[error("capture failed: {detail}")]
    Capture { detail: Detail },
    #[error("{feature} is not available on this backend")]
    Unsupported { feature: Feature },
    #[error("the screen is locked; nothing was sent")]
    ScreenLocked,
    #[error("the display is asleep; nothing was sent")]
    DisplayAsleep,
    #[error("{detail}; nothing was sent")]
    Platform { detail: Detail },
    #[error("timed out before any input was sent")]
    Timeout,
}

/// Input was sent; what it did is not confirmed.
#[derive(Clone, Debug, PartialEq, thiserror::Error, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub enum Unverified {
    #[error("{detail}; observe the window before retrying")]
    AxUnconfirmed { detail: Detail },
    #[error(transparent)]
    Interrupted(Interruption),
    #[error(transparent)]
    Readback(Readback),
    #[error("input failed part way: {detail}; some input may have landed; observe the window before retrying")]
    InputFailed { detail: Detail },
}

/// What stopped input that was already under way.
#[derive(Clone, Debug, PartialEq, Eq, thiserror::Error, Serialize, Deserialize)]
#[serde(tag = "by", rename_all = "snake_case")]
pub enum Interruption {
    #[error("cancelled during input; input sent before the cancel may have landed; {READ_AGAIN}")]
    Cancelled,
    #[error("the user pressed a key or clicked in {app} during this input; input sent before that may already have landed, and nothing more was sent; {READ_AGAIN}")]
    UserInput { app: String },
    #[error("the user's Escape stopped takeover input; input sent before it may have landed; {READ_AGAIN}")]
    Escape,
}

const READ_AGAIN: &str = "observe the window again before acting on it";

/// The user used the app the session acts in, or is still active.
#[derive(Clone, Debug, PartialEq, Eq, thiserror::Error, Serialize, Deserialize)]
#[serde(tag = "state", rename_all = "snake_case")]
pub enum Intervention {
    #[error("the user was using {app} (last input {:.1} s ago); nothing was sent; {READ_AGAIN}", .idle.as_secs_f64())]
    Used { app: String, idle: Duration },
    #[error("the user is still using {app} (last input {:.1} s ago); nothing was sent; once they pause, {READ_AGAIN}", .idle.as_secs_f64())]
    StillUsing { app: String, idle: Duration },
    #[error("the user is still typing, clicking or holding input (last activity {:.1} s ago), so no takeover started; nothing was sent; try again once they pause", .idle.as_secs_f64())]
    StillActive { idle: Duration },
    #[error("the user pressed or is holding a key or button as the takeover was starting, so none started; nothing was sent; try again once they pause")]
    TakeoverStart,
    #[error("the user pressed a key or clicked in {app} as this step began; nothing was sent; {READ_AGAIN}")]
    DuringInput { app: String },
}

/// Why a ref no longer names the element it was read from.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct StaleRef {
    pub reference: ElementRef,
    pub cause: StaleCause,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "cause", rename_all = "snake_case")]
pub enum StaleCause {
    /// The ref was missing from two observations of its window, or never
    /// existed.
    Expired,
    /// The app destroyed the element. `candidate` is the one element of the
    /// window with the identity the ref was read with; equal fields do not
    /// prove it is the same control.
    Destroyed { candidate: Option<ElementRef> },
    /// The element now reads with another role or label. `candidate` is the
    /// one other element this read found with the original role and label.
    ReadsAs {
        role: Role,
        label: Option<String>,
        candidate: Option<ElementRef>,
    },
}

impl std::error::Error for StaleRef {}

impl fmt::Display for StaleRef {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let reference = self.reference;
        match &self.cause {
            StaleCause::Expired => write!(f, "{reference} expired; observe the window again"),
            StaleCause::Destroyed { candidate: None } => write!(
                f,
                "the app destroyed {reference}'s element; nothing was sent; observe the window again"
            ),
            StaleCause::Destroyed {
                candidate: Some(candidate),
            } => write!(
                f,
                "the app destroyed {reference}'s element; nothing was sent; {candidate} is the one \
                 element in the window with the role, labels and value {reference} was read with; \
                 check it before acting on it"
            ),
            StaleCause::ReadsAs {
                role,
                label,
                candidate,
            } => {
                write!(
                    f,
                    "{reference} now reads as {role}{}, not with the role and label it was read \
                     with; nothing was sent",
                    Quoted(label.as_deref())
                )?;
                match candidate {
                    Some(candidate) => write!(
                        f,
                        "; {candidate} is the one other element this read of the window found with \
                         the original role and label"
                    ),
                    None => Ok(()),
                }
            }
        }
    }
}

/// An optional label written as ` "label"`, escaped and bounded.
pub(crate) struct Quoted<'a>(pub(crate) Option<&'a str>);

impl fmt::Display for Quoted<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.0 {
            Some(label) => {
                f.write_str(" ")?;
                crate::ax::tree::write_quoted_label(f, label)
            }
            None => Ok(()),
        }
    }
}

/// Who holds desktop input control, as its lock file records it.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "holder", rename_all = "snake_case")]
pub enum Holder {
    Unnamed,
    Named { name: String, pid: u32 },
}

impl fmt::Display for Holder {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Unnamed => f.write_str("another desktop session"),
            Self::Named { name, pid } => write!(f, "{name:?} (pid {pid})"),
        }
    }
}

/// Why a window selector named no window. Adjacently tagged: `NotFound`
/// holds a string, which an internal tag cannot sit beside.
#[derive(Clone, Debug, PartialEq, Eq, thiserror::Error, Serialize, Deserialize)]
#[serde(tag = "kind", content = "data", rename_all = "snake_case")]
pub enum WindowError {
    #[error("window {0} was not found; list the windows again")]
    NotFound(WindowId),
    #[error("no window matches app {:?} and title {:?}; list the windows", .0.app, .0.title)]
    NoMatch(WindowFilter),
    #[error("the selector matches several windows: {}; select one by id", Candidates(.candidates))]
    Ambiguous { candidates: Vec<WindowSummary> },
}

struct Candidates<'a>(&'a [WindowSummary]);

impl fmt::Display for Candidates<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for (index, window) in self.0.iter().enumerate() {
            if index > 0 {
                f.write_str(", ")?;
            }
            write!(f, "{} ({}", window.id, window.app)?;
            crate::error::Quoted(Some(&window.title)).fmt(f)?;
            f.write_str(")")?;
        }
        Ok(())
    }
}

/// Why a ref's element cannot take the step. Adjacently tagged, like
/// [`WindowError`].
#[derive(Clone, Debug, PartialEq, Eq, thiserror::Error, Serialize, Deserialize)]
#[serde(tag = "kind", content = "data", rename_all = "snake_case")]
pub enum ElementError {
    #[error("{0} has no clickable bounds; nothing was sent")]
    NoBounds(ElementRef),
    #[error("{reference} belongs to window {window}, not the window this step acts on; nothing was sent")]
    OtherWindow {
        reference: ElementRef,
        window: WindowId,
    },
}

/// An OS permission the app running eukhe needs.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum Permission {
    ScreenRecording,
    Accessibility,
    InputMonitoring,
}

impl fmt::Display for Permission {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(match self {
            Self::ScreenRecording => "Screen Recording",
            Self::Accessibility => "Accessibility",
            Self::InputMonitoring => "Input Monitoring",
        })
    }
}

/// A backend feature, as [`Refusal::Unsupported`] names it.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum Feature {
    Windows,
    Capture,
    Accessibility,
    Input,
    Menus,
    Applications,
    Documents,
    Roster,
    TextSelection,
    Takeover,
    EscapeStop,
    UserInputWatch,
}

impl fmt::Display for Feature {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(match self {
            Self::Windows => "window listing",
            Self::Capture => "screen capture",
            Self::Accessibility => "accessibility",
            Self::Input => "input",
            Self::Menus => "the menu bar",
            Self::Applications => "application discovery and launch",
            Self::Documents => "opening files, folders and URLs",
            Self::Roster => "the on-screen window roster",
            Self::TextSelection => "text selection by accessibility",
            Self::Takeover => "takeover input",
            Self::EscapeStop => "the physical Escape stop",
            Self::UserInputWatch => "watching the user's input",
        })
    }
}

/// What a field read back after a write that did not hold exactly what was
/// sent. Never quotes the written text, which may be a password.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Readback {
    /// Characters written.
    pub sent: usize,
    /// Characters the whole value should now have, when it is not `sent`.
    pub expected: Option<usize>,
    pub reads: FieldReads,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "reads", rename_all = "snake_case")]
pub enum FieldReads {
    Unreadable,
    SecureUnconfirmed,
    Empty,
    Mask {
        chars: usize,
    },
    SecureHidden,
    /// What the field reads, the written text replaced by a placeholder.
    Text {
        text: String,
    },
}

impl std::error::Error for Readback {}

impl fmt::Display for Readback {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "wrote {}", Chars(self.sent))?;
        if let Some(expected) = self.expected {
            write!(f, " into a value that should now be {}", Chars(expected))?;
        }
        f.write_str(", but ")?;
        match &self.reads {
            FieldReads::Unreadable => f.write_str("the field's value could not be read back")?,
            FieldReads::SecureUnconfirmed => {
                f.write_str("the secure text field's value could not be confirmed")?;
            }
            FieldReads::Empty => f.write_str("the field now reads empty")?,
            FieldReads::Mask { chars } => {
                write!(f, "the field now reads as a mask of {}", Chars(*chars))?;
            }
            FieldReads::SecureHidden => {
                f.write_str("the secure text field's value is not shown")?;
            }
            FieldReads::Text { text } => write!(f, "the field now reads {text:?}")?,
        }
        match self.reads {
            FieldReads::Unreadable | FieldReads::SecureUnconfirmed => {}
            FieldReads::Empty
            | FieldReads::Mask { .. }
            | FieldReads::SecureHidden
            | FieldReads::Text { .. } => {
                f.write_str(". The app may have reformatted it or not taken it")?;
            }
        }
        f.write_str("; inspect the target before writing again")
    }
}

struct Chars(usize);

impl fmt::Display for Chars {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.0 {
            1 => f.write_str("1 character"),
            count => write!(f, "{count} characters"),
        }
    }
}

impl Refusal {
    pub(crate) fn unsupported(feature: Feature) -> Self {
        Self::Unsupported { feature }
    }
}

impl Error {
    pub(crate) fn unsupported(feature: Feature) -> Self {
        Self::Refused(Refusal::unsupported(feature))
    }
}

impl From<StaleRef> for Error {
    fn from(stale: StaleRef) -> Self {
        Self::Refused(Refusal::StaleRef(stale))
    }
}

impl From<Intervention> for Error {
    fn from(intervention: Intervention) -> Self {
        Self::Refused(Refusal::UserIntervened(intervention))
    }
}

macro_rules! refused_from {
    ($($kind:ty),*) => {$(
        impl From<$kind> for Error {
            fn from(error: $kind) -> Self {
                Self::Refused(Refusal::from(error))
            }
        }
    )*};
}

refused_from!(
    WindowError,
    FrameError,
    KeyError,
    MenuError,
    TextRangeError,
    AppError,
    ElementError
);

#[cfg(test)]
mod tests {
    use super::*;
    use crate::types::WindowFilter;

    /// A refusal that wraps a tagged error, or a string, reaches a tool's
    /// details as JSON and reads back the same.
    #[test]
    fn refusals_round_trip_through_json() {
        let reference = "e3"
            .parse::<ElementRef>()
            .unwrap_or_else(|error| panic!("{error:?}"));
        let errors = [
            Error::from(WindowError::NotFound(WindowId::new("9"))),
            Error::from(WindowError::NoMatch(WindowFilter {
                app: Some("Mail".to_owned()),
                title: None,
            })),
            Error::from(ElementError::NoBounds(reference)),
            Error::Refused(Refusal::Cancelled),
        ];
        let read: Vec<Result<Error, String>> = errors
            .iter()
            .map(|error| {
                serde_json::to_string(error)
                    .and_then(|json| serde_json::from_str(&json))
                    .map_err(|error| error.to_string())
            })
            .collect();
        assert_eq!(read, errors.map(Ok));
    }
}
