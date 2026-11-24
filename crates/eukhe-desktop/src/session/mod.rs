//! The desktop session: one worker thread that owns the platform backend,
//! the ref registry and the screenshot frames; callers reach it through a
//! read tier ([`Reader`]) and an exec tier ([`Executor`]). Replaces the
//! napi `DesktopSession` of omp `crates/natives/src/desktop/mod.rs`.

mod worker;

use std::path::PathBuf;
use std::sync::mpsc;
use std::thread::{self, JoinHandle};

use serde::{Deserialize, Serialize};

use crate::applications::{AppQuery, Application, OpenRequest, Opened};
use crate::ax::tree::{FindQuery, FoundNode, Tree, TreeOptions};
use crate::ax::ElementRef;
use crate::backend::{ClickCount, MouseButton};
use crate::control::{CancelSource, Token};
use crate::error::{Effect, Error, Refusal};
use crate::frame::Screenshot;
use crate::geometry::{FramePoint, ScrollDelta};
use crate::keys::{Chord, Modifiers};
use crate::menus::{MenuItem, MenuPath};
use crate::roster::RosterWindow;
use crate::text_range::TextSelectRequest;
use crate::types::{Capabilities, ImageCaps, Takeover, Window, WindowFilter, WindowSelector};

/// How a session takes the input lease.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SessionOptions {
    /// The per-user lock file every session's input goes through
    /// ([`crate::default_input_lock`]).
    pub input_lock: PathBuf,
    /// The name other sessions see while this one holds input.
    pub holder: String,
}

/// What an observation returns; absent fields are not taken.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct ObserveOptions {
    /// Take a screenshot scaled into these caps.
    #[serde(default)]
    pub screenshot: Option<ImageCaps>,
    /// Read the accessibility tree.
    #[serde(default)]
    pub tree: Option<TreeOptions>,
}

/// One window as observed now.
#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct Observation {
    pub window: Window,
    pub screenshot: Option<Screenshot>,
    pub tree: Option<Tree>,
}

/// Where keys and text go: the element holding focus in the window, or an
/// element by ref, which is focused first.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
#[serde(from = "Option<ElementRef>", into = "Option<ElementRef>")]
pub enum KeyTarget {
    #[default]
    Focused,
    Element(ElementRef),
}

impl From<Option<ElementRef>> for KeyTarget {
    fn from(element: Option<ElementRef>) -> Self {
        element.map_or(Self::Focused, Self::Element)
    }
}

impl From<KeyTarget> for Option<ElementRef> {
    fn from(target: KeyTarget) -> Self {
        match target {
            KeyTarget::Focused => None,
            KeyTarget::Element(element) => Some(element),
        }
    }
}

/// Where a click or scroll lands: an element's center, or a pixel of the
/// window's last screenshot.
#[derive(Clone, Copy, Debug, PartialEq, Serialize, Deserialize)]
#[serde(untagged)]
pub enum PointTarget {
    Element(ElementRef),
    Pixel(FramePoint),
}

/// One input step on a window.
#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
#[serde(tag = "type", rename_all = "snake_case")]
pub enum Step {
    /// The element's own press action.
    Press {
        target: ElementRef,
    },
    /// Writes the element's value, then reads it back.
    SetValue {
        target: ElementRef,
        value: String,
    },
    /// Types text as key presses.
    Type {
        text: String,
        #[serde(default)]
        into: KeyTarget,
    },
    /// Presses one chord, such as `cmd+s`.
    Key {
        chord: Chord,
        #[serde(default)]
        into: KeyTarget,
    },
    Click {
        at: PointTarget,
        #[serde(default)]
        button: MouseButton,
        #[serde(default)]
        count: ClickCount,
        #[serde(default)]
        modifiers: Modifiers,
    },
    Scroll {
        at: PointTarget,
        delta: ScrollDelta,
    },
    /// Runs a menu-bar command by its label path.
    Menu {
        path: MenuPath,
    },
    /// Selects text in the element's value, or places the caret, without
    /// changing the value.
    SelectText {
        target: ElementRef,
        #[serde(flatten)]
        request: TextSelectRequest,
    },
}

/// What a batch of steps did, one effect per step run. The batch stops after
/// the first effect that is not `Confirmed`; later steps are not run.
#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct ActReport {
    pub steps: Vec<Effect>,
}

type Reply<T> = mpsc::SyncSender<T>;

/// One request to the worker, with its reply channel.
enum Job {
    Capabilities {
        reply: Reply<Capabilities>,
    },
    Windows {
        filter: WindowFilter,
        reply: Reply<Result<Vec<Window>, Error>>,
    },
    Window {
        selector: WindowSelector,
        reply: Reply<Result<Window, Error>>,
    },
    Observe {
        selector: WindowSelector,
        options: ObserveOptions,
        token: Token,
        reply: Reply<Result<Observation, Error>>,
    },
    Find {
        selector: WindowSelector,
        query: FindQuery,
        token: Token,
        reply: Reply<Result<Vec<FoundNode>, Error>>,
    },
    MenuItems {
        selector: WindowSelector,
        path: Vec<String>,
        reply: Reply<Result<Vec<MenuItem>, Error>>,
    },
    Applications {
        query: AppQuery,
        reply: Reply<Result<Vec<Application>, Error>>,
    },
    Roster {
        reply: Reply<Result<Vec<RosterWindow>, Error>>,
    },
    Act {
        selector: WindowSelector,
        steps: Vec<Step>,
        takeover: Takeover,
        token: Token,
        reply: Reply<Result<ActReport, Error>>,
    },
    Open {
        request: OpenRequest,
        token: Token,
        reply: Reply<Result<Opened, Error>>,
    },
}

/// Cancels the session's operation when the last owner lets go.
struct CancelOnDrop(CancelSource);

impl Drop for CancelOnDrop {
    fn drop(&mut self) {
        self.0.cancel();
    }
}

/// A desktop session. Every call blocks until the worker answers; call it
/// from a blocking context. The worker serves one call at a time, in order.
pub struct Desktop {
    jobs: mpsc::Sender<Job>,
    cancel: CancelOnDrop,
    worker: JoinHandle<()>,
}

fn closed<T>(_: T) -> Error {
    Error::Refused(Refusal::Closed)
}

impl Desktop {
    /// Starts the worker and opens the platform backend on it.
    ///
    /// # Errors
    ///
    /// The backend's refusal: `Unsupported` where no backend serves this
    /// desktop, `NotPermitted`, `Platform`.
    pub fn open(options: SessionOptions) -> Result<Self, Error> {
        let cancel = CancelSource::default();
        let (jobs, inbox) = mpsc::channel();
        let (ready, opened) = mpsc::sync_channel(1);
        let stop = cancel.clone();
        let worker = thread::Builder::new()
            .name("eukhe-desktop".to_owned())
            .spawn(move || worker::run(&options, stop, &inbox, &ready))
            .map_err(|error| {
                Error::Refused(Refusal::Platform {
                    detail: format!("cannot start the desktop worker: {error}").into(),
                })
            })?;
        opened.recv().map_err(closed)??;
        Ok(Self {
            jobs,
            cancel: CancelOnDrop(cancel),
            worker,
        })
    }

    /// Read-tier operations: inspection, never input.
    #[must_use]
    pub fn read(&self) -> Reader<'_> {
        Reader { desktop: self }
    }

    /// Exec-tier operations: input and launches, under the caller's
    /// takeover policy.
    #[must_use]
    pub fn exec(&self, takeover: Takeover) -> Executor<'_> {
        Executor {
            desktop: self,
            takeover,
        }
    }

    /// Stops the running call and every call queued before this one.
    pub fn cancel(&self) {
        self.cancel.0.cancel();
    }

    /// How many times the user's physical Escape stopped this session.
    #[must_use]
    pub fn escape_stops(&self) -> u32 {
        self.cancel.0.escapes()
    }

    /// Stops the worker and waits for it to release the backend.
    ///
    /// # Errors
    ///
    /// `Platform` when the worker thread panicked.
    pub fn close(self) -> Result<(), Error> {
        let Self {
            jobs,
            cancel,
            worker,
        } = self;
        drop(cancel);
        drop(jobs);
        worker.join().map_err(|_| {
            Error::Refused(Refusal::Platform {
                detail: "the desktop worker panicked".into(),
            })
        })
    }

    fn token(&self) -> Token {
        self.cancel.0.token()
    }

    fn call<T>(&self, job: impl FnOnce(Reply<T>) -> Job) -> Result<T, Error> {
        let (reply, answer) = mpsc::sync_channel(1);
        self.jobs.send(job(reply)).map_err(closed)?;
        answer.recv().map_err(closed)
    }
}

/// Inspection: windows, screenshots, trees, menus, applications.
pub struct Reader<'a> {
    desktop: &'a Desktop,
}

impl Reader<'_> {
    /// # Errors
    ///
    /// `Closed` once the session is closed.
    pub fn capabilities(&self) -> Result<Capabilities, Error> {
        self.desktop.call(|reply| Job::Capabilities { reply })
    }

    /// The top-level windows `filter` keeps, front to back.
    ///
    /// # Errors
    ///
    /// The backend's refusal.
    pub fn windows(&self, filter: WindowFilter) -> Result<Vec<Window>, Error> {
        self.desktop.call(|reply| Job::Windows { filter, reply })?
    }

    /// The one window `selector` names.
    ///
    /// # Errors
    ///
    /// `Window` when it names none or several, listing the candidates.
    pub fn window(&self, selector: WindowSelector) -> Result<Window, Error> {
        self.desktop.call(|reply| Job::Window { selector, reply })?
    }

    /// A screenshot and/or the accessibility tree of one window. A
    /// screenshot becomes the frame that window's pixel steps use.
    ///
    /// # Errors
    ///
    /// `Window`, `Capture`, `NotPermitted`, `Cancelled`.
    pub fn observe(
        &self,
        selector: WindowSelector,
        options: ObserveOptions,
    ) -> Result<Observation, Error> {
        let token = self.desktop.token();
        self.desktop.call(|reply| Job::Observe {
            selector,
            options,
            token,
            reply,
        })?
    }

    /// Elements of one window matching `query`, each with a ref.
    ///
    /// # Errors
    ///
    /// `Window`, `NotPermitted`, `Cancelled`.
    pub fn find(
        &self,
        selector: WindowSelector,
        query: FindQuery,
    ) -> Result<Vec<FoundNode>, Error> {
        let token = self.desktop.token();
        self.desktop.call(|reply| Job::Find {
            selector,
            query,
            token,
            reply,
        })?
    }

    /// The items of the menu at `path` in the window's menu bar; the bar
    /// itself for an empty path.
    ///
    /// # Errors
    ///
    /// `Window`, `Menu`, `Unsupported`.
    pub fn menu_items(
        &self,
        selector: WindowSelector,
        path: Vec<String>,
    ) -> Result<Vec<MenuItem>, Error> {
        self.desktop.call(|reply| Job::MenuItems {
            selector,
            path,
            reply,
        })?
    }

    /// Installed applications `query` keeps, sorted by name.
    ///
    /// # Errors
    ///
    /// `Unsupported`, `Platform`.
    pub fn applications(&self, query: AppQuery) -> Result<Vec<Application>, Error> {
        self.desktop
            .call(|reply| Job::Applications { query, reply })?
    }

    /// Every on-screen window, popup menus and system panels included.
    ///
    /// # Errors
    ///
    /// `Unsupported` off macOS.
    pub fn roster(&self) -> Result<Vec<RosterWindow>, Error> {
        self.desktop.call(|reply| Job::Roster { reply })?
    }
}

/// Input and launches.
pub struct Executor<'a> {
    desktop: &'a Desktop,
    takeover: Takeover,
}

impl Executor<'_> {
    /// Runs `steps` on one window under the input lease, in order.
    ///
    /// # Errors
    ///
    /// Refusals before any step ran: `Window`, `InputBusy`,
    /// `UserIntervened`, `Cancelled`.
    pub fn act(&self, selector: WindowSelector, steps: Vec<Step>) -> Result<ActReport, Error> {
        let token = self.desktop.token();
        let takeover = self.takeover;
        self.desktop.call(|reply| Job::Act {
            selector,
            steps,
            takeover,
            token,
            reply,
        })?
    }

    /// Opens an application, file, folder or URL.
    ///
    /// # Errors
    ///
    /// `Application`, `Unsupported`, `Platform`, `InputBusy`.
    pub fn open_application(&self, request: OpenRequest) -> Result<Opened, Error> {
        let token = self.desktop.token();
        self.desktop.call(|reply| Job::Open {
            request,
            token,
            reply,
        })?
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::keys::Key;

    #[test]
    fn steps_decode_from_tool_json() {
        let steps: Result<Vec<Step>, _> = serde_json::from_str(
            r#"[
                {"type": "press", "target": "e4"},
                {"type": "key", "chord": "cmd+s"},
                {"type": "type", "text": "hi", "into": "e9"},
                {"type": "click", "at": {"x": 10.5, "y": 4}},
                {"type": "click", "at": "e2", "count": 2},
                {"type": "menu", "path": ["File", "Export…"]},
                {"type": "select_text", "target": "e3", "text": "cat", "prefix": "red "}
            ]"#,
        );
        let steps = steps.unwrap_or_else(|error| panic!("{error}"));
        assert_eq!(steps.len(), 7);
        assert_eq!(
            steps[1],
            Step::Key {
                chord: Chord {
                    modifiers: Modifiers::NONE.with(crate::keys::Modifier::Meta),
                    key: Some(Key::Char('s')),
                },
                into: KeyTarget::Focused,
            }
        );
        assert!(matches!(
            steps[3],
            Step::Click {
                at: PointTarget::Pixel(FramePoint { .. }),
                count: ClickCount::SINGLE,
                ..
            }
        ));
        assert!(
            serde_json::from_str::<Step>(r#"{"type": "click", "at": "e2", "count": 4}"#).is_err()
        );
        assert!(serde_json::from_str::<Step>(r#"{"type": "menu", "path": []}"#).is_err());
    }
}
