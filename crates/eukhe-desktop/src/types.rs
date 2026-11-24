//! The session's vocabulary: windows, selectors, capabilities, policies
//! (port of omp `crates/natives/src/desktop/types.rs`).

use std::fmt;
use std::num::NonZeroU32;
use std::sync::Arc;

use serde::{Deserialize, Serialize};

use crate::error::WindowError;
use crate::geometry::GlobalRect;

/// A backend's window id, valid while the window lives. Opaque: never parsed.
#[derive(Clone, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[serde(transparent)]
pub struct WindowId(Arc<str>);

impl WindowId {
    #[must_use]
    pub fn new(id: &str) -> Self {
        Self(Arc::from(id))
    }

    #[must_use]
    pub fn as_str(&self) -> &str {
        &self.0
    }
}

impl fmt::Display for WindowId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.0)
    }
}

/// An operating-system process id.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[serde(transparent)]
pub struct Pid(pub u32);

/// Whether a window or element holds keyboard focus.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum Focus {
    Focused,
    Unfocused,
}

/// One top-level window in global logical desktop coordinates.
#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct Window {
    pub id: WindowId,
    /// Empty for untitled windows, and on macOS for other apps' windows
    /// without Screen Recording.
    pub title: String,
    /// The owning application's name.
    pub app: String,
    pub pid: Option<Pid>,
    pub bounds: GlobalRect,
    pub focus: Focus,
}

/// What a window list keeps: windows whose app and title contain these
/// texts, ignoring case. An absent field matches every window.
#[derive(Clone, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct WindowFilter {
    #[serde(default)]
    pub app: Option<String>,
    #[serde(default)]
    pub title: Option<String>,
}

impl WindowFilter {
    #[must_use]
    pub fn matches(&self, window: &Window) -> bool {
        contains_folded(&window.app, self.app.as_deref())
            && contains_folded(&window.title, self.title.as_deref())
    }
}

fn contains_folded(text: &str, needle: Option<&str>) -> bool {
    needle.is_none_or(|needle| text.to_lowercase().contains(&needle.to_lowercase()))
}

/// The one window an operation acts on.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum WindowSelector {
    Id(WindowId),
    Filter(WindowFilter),
}

/// How many candidates an ambiguous selector names.
const LISTED_CANDIDATES: usize = 20;

impl WindowSelector {
    /// The one window of `windows` this selector names.
    pub(crate) fn resolve(&self, windows: Vec<Window>) -> Result<Window, WindowError> {
        match self {
            Self::Id(id) => windows
                .into_iter()
                .find(|window| window.id == *id)
                .ok_or_else(|| WindowError::NotFound(id.clone())),
            Self::Filter(filter) => {
                let mut matches = windows.into_iter().filter(|window| filter.matches(window));
                match (matches.next(), matches.next()) {
                    (Some(only), None) => Ok(only),
                    (None, _) => Err(WindowError::NoMatch(filter.clone())),
                    (Some(first), Some(second)) => Err(WindowError::Ambiguous {
                        candidates: [first, second]
                            .into_iter()
                            .chain(matches)
                            .take(LISTED_CANDIDATES)
                            .map(WindowSummary::from)
                            .collect(),
                    }),
                }
            }
        }
    }
}

/// A window as an ambiguity error names it.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct WindowSummary {
    pub id: WindowId,
    pub app: String,
    pub title: String,
}

impl From<Window> for WindowSummary {
    fn from(window: Window) -> Self {
        let Window { id, app, title, .. } = window;
        Self { id, app, title }
    }
}

/// Whether the app running eukhe holds an OS permission.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum Access {
    Granted,
    Denied,
    /// The backend cannot tell without prompting.
    Unknown,
}

/// Whether the backend offers a feature on this desktop.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum Support {
    Supported,
    Unsupported,
}

/// Which backend serves the session.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum BackendKind {
    Macos,
    X11,
}

/// Whether the user session is locked.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum Lock {
    Unlocked,
    Locked,
}

/// Whether the display is awake.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum DisplayPower {
    Awake,
    Asleep,
}

/// Lock and display-sleep state, read live per call. Backends that cannot
/// tell report unlocked and awake.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ScreenState {
    pub lock: Lock,
    pub display: DisplayPower,
}

/// macOS Secure Event Input: while on, the user's keys are hidden from every
/// event monitor, so the Escape stop and intervention watch see nothing.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "state", rename_all = "snake_case")]
pub enum SecureInput {
    Off,
    On { app: Option<String> },
}

/// What the backend can do on this desktop now.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Capabilities {
    pub backend: BackendKind,
    pub capture: Access,
    pub input: Access,
    pub accessibility: Access,
    /// Window input without activating the target or moving the pointer.
    pub background_input: Support,
    /// A foreground rerun of a refused background step.
    pub takeover: Support,
    pub menus: Support,
    pub applications: Support,
    /// A physical Escape stops takeover input.
    pub escape_stop: Support,
    pub secure_input: SecureInput,
    pub screen: ScreenState,
}

/// Whether a step the background route refuses may rerun in the foreground,
/// set by the caller's policy; the model never chooses it.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum Takeover {
    /// A refused background step stays refused.
    Refuse,
    /// A refused background step reruns once in the foreground, then focus
    /// goes back to the user's app.
    Fallback,
}

/// How one attempt of a step reaches its window.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum DeliveryMode {
    /// No activation, no pointer movement; a route that cannot do that
    /// refuses with `BackgroundUnavailable`.
    Background,
    /// The policy's rerun: activates the target, sends real input, hands
    /// focus back to the user's app.
    Takeover,
}

/// Whether a background press that would open a control's menu is refused
/// first: an open menu takes the user's keyboard.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum MenuPress {
    Allow,
    Refuse,
}

impl From<Takeover> for MenuPress {
    fn from(policy: Takeover) -> Self {
        match policy {
            Takeover::Refuse => Self::Refuse,
            Takeover::Fallback => Self::Allow,
        }
    }
}

/// The largest screenshot the caller's transport takes; larger captures
/// are scaled down to fit, keeping their aspect ratio.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ImageCaps {
    pub max_width: NonZeroU32,
    pub max_height: NonZeroU32,
}

#[cfg(test)]
mod tests {
    use super::*;

    fn window(id: &str, app: &str, title: &str) -> Window {
        Window {
            id: WindowId::new(id),
            title: title.to_owned(),
            app: app.to_owned(),
            pid: Some(Pid(1)),
            bounds: GlobalRect {
                x: 0,
                y: 0,
                width: 100,
                height: 100,
            },
            focus: Focus::Unfocused,
        }
    }

    #[test]
    fn a_filter_names_one_window_or_lists_the_candidates() {
        let windows = || {
            vec![
                window("1", "TextEdit", "Notes.txt"),
                window("2", "TextEdit", "Todo.txt"),
                window("3", "Safari", "Start"),
            ]
        };
        let filter = |app: &str, title: Option<&str>| {
            WindowSelector::Filter(WindowFilter {
                app: Some(app.to_owned()),
                title: title.map(str::to_owned),
            })
        };
        assert_eq!(
            filter("safari", None).resolve(windows()),
            Ok(window("3", "Safari", "Start"))
        );
        assert_eq!(
            filter("textedit", Some("TODO")).resolve(windows()),
            Ok(window("2", "TextEdit", "Todo.txt"))
        );
        assert_eq!(
            filter("textedit", None).resolve(windows()),
            Err(WindowError::Ambiguous {
                candidates: vec![
                    WindowSummary::from(window("1", "TextEdit", "Notes.txt")),
                    WindowSummary::from(window("2", "TextEdit", "Todo.txt")),
                ]
            })
        );
        assert_eq!(
            WindowSelector::Id(WindowId::new("9")).resolve(windows()),
            Err(WindowError::NotFound(WindowId::new("9")))
        );
    }
}
