//! The macOS backend: `ScreenCaptureKit` capture, AX inspection, background
//! input routed to one process through `SkyLight`, takeover by policy (port
//! of omp `crates/natives/src/desktop/macos/mod.rs`). See `crate::backend`
//! for the contract.

mod applications;
mod ax;
mod capture;
mod ffi;
mod guard;
mod input;
mod keymap;
mod menus;
mod monitor;
mod windows;

use std::path::Path;
use std::time::Instant;

use self::ax::{NodeRead, NodeValues, Requests};
use self::ffi::ax::{AxCode, Value};
use self::ffi::quartz::{self, Source};
use self::ffi::sky::Spi;
use self::ffi::{appkit, process};
use self::input::{Insertion, Target};
use self::windows::CaptureGrant;
use crate::applications::{Activation, AppKind, Application, Document, Opened};
use crate::ax::{
    ActionNames, AxProps, AxRead, Completeness, Liveness, Settable, Unread, WalkBounds,
};
use crate::backend::{Delivery, FieldKind, PointerEvent, SelectionReadback, Typing, ValueReadback};
use crate::control::intervention::{Held, StartTime, QUIET};
use crate::control::{Sent, Token};
use crate::error::{Error, Feature, Intervention, Permission, Refusal, Unverified};
use crate::frame::Capture;
use crate::keys::{Chord, KeyError};
use crate::menus::MenuItem;
use crate::roster::RosterWindow;
use crate::text_range::Utf16Range;
use crate::types::{
    Access, BackendKind, Capabilities, DeliveryMode, DisplayPower, Focus, Lock, MenuPress, Pid,
    ScreenState, SecureInput, Support, Window,
};

pub(crate) use self::ffi::ax::AxHandle;
pub(crate) use self::monitor::{EscapeMonitor, UserInputMonitor};

pub(crate) const BACKEND: BackendKind = BackendKind::Macos;
/// AX action names are performable (`AXPress` is `press`).
pub(crate) const ACTION_NAMES: ActionNames = ActionNames::Ax;
pub(crate) const OPENS_DOCUMENTS: Support = Support::Supported;

/// The window server, AX and input state of one session.
pub(crate) struct Backend {
    spi: Spi,
    requests: Requests,
    /// `None` when Quartz gives no HID event source: input then refuses.
    source: Option<Source>,
}

const fn access(granted: bool) -> Access {
    if granted {
        Access::Granted
    } else {
        Access::Denied
    }
}

const fn support(supported: bool) -> Support {
    if supported {
        Support::Supported
    } else {
        Support::Unsupported
    }
}

fn grant() -> CaptureGrant {
    if quartz::screen_capture_access() {
        CaptureGrant::Granted
    } else {
        CaptureGrant::Denied
    }
}

fn require_accessibility() -> Result<(), Error> {
    if ffi::ax::trusted() {
        Ok(())
    } else {
        Err(Error::Refused(Refusal::NotPermitted {
            permission: Permission::Accessibility,
        }))
    }
}

/// Control roles whose own press opens a menu, which takes the user's
/// keyboard while open.
fn opens_menu(native_role: &str) -> bool {
    matches!(
        native_role,
        "AXPopUpButton" | "AXMenuButton" | "AXMenuBarItem" | "AXComboBox"
    )
}

fn app_name(pid: i32) -> String {
    appkit::app(pid)
        .and_then(|app| app.name)
        .unwrap_or_else(|| format!("process {pid}"))
}

fn element_pid(element: &AxHandle) -> Result<i32, Error> {
    element
        .pid()
        .map_err(|code| ax::refused(code, "reading the element's process"))
}

fn chord_presses(chord: Chord) -> Result<Vec<keymap::Press>, Error> {
    keymap::chord_presses(chord).map_err(|keymap::NoKey| {
        Error::from(KeyError::Unknown {
            name: chord.to_string(),
        })
    })
}

/// The listed window `pid` shows in front, if any.
fn front_window(pid: i32) -> Option<Window> {
    let records = quartz::window_list()?;
    windows::windows(records, grant(), None, None)
        .into_iter()
        .find(|window| window.pid == u32::try_from(pid).ok().map(Pid))
}

impl Backend {
    #[allow(
        clippy::unnecessary_wraps,
        reason = "the seam's signature; opening never fails on macOS"
    )]
    pub(crate) fn open() -> Result<Self, Error> {
        Ok(Self {
            spi: Spi::load(),
            requests: Requests::new(),
            source: Source::hid(),
        })
    }

    fn source(&self) -> Result<&Source, Error> {
        self.source.as_ref().ok_or_else(|| {
            Error::Refused(Refusal::Platform {
                detail: "Quartz gives no HID event source".into(),
            })
        })
    }

    pub(crate) fn capabilities(&mut self) -> Capabilities {
        let accessibility = ffi::ax::trusted();
        let session = quartz::session();
        Capabilities {
            backend: BACKEND,
            capture: access(quartz::screen_capture_access()),
            input: access(quartz::post_event_access()),
            accessibility: access(accessibility),
            background_input: support(accessibility && self.spi.background_input()),
            takeover: support(self.spi.takeover()),
            menus: support(accessibility),
            applications: Support::Supported,
            escape_stop: support(quartz::listen_event_access() && session.secure_input.is_none()),
            secure_input: match session.secure_input {
                Some(pid) => SecureInput::On {
                    app: appkit::app(pid).and_then(|app| app.name),
                },
                None => SecureInput::Off,
            },
            screen: ScreenState {
                lock: if session.locked {
                    Lock::Locked
                } else {
                    Lock::Unlocked
                },
                display: if quartz::display_asleep() {
                    DisplayPower::Asleep
                } else {
                    DisplayPower::Awake
                },
            },
        }
    }

    /// The front app's pid, as `WindowServer` reports it.
    fn front_pid(&self) -> Option<i32> {
        self.spi
            .front_process()
            .and_then(|(_, pid)| pid)
            .or_else(appkit::frontmost_pid)
    }

    pub(crate) fn windows(&mut self) -> Result<Vec<Window>, Error> {
        let records = quartz::window_list().ok_or_else(|| {
            Error::Refused(Refusal::Platform {
                detail: "the window server did not list its windows".into(),
            })
        })?;
        let front = self.front_pid();
        let focused = front.and_then(|pid| ax::focused_window_id(&self.spi, pid));
        Ok(windows::windows(records, grant(), front, focused))
    }

    #[allow(clippy::unused_self, reason = "the seam's signature")]
    pub(crate) fn capture(&mut self, window: &Window) -> Result<Capture, Error> {
        capture::window(window)
    }

    #[allow(clippy::unused_self, reason = "the seam's signature")]
    pub(crate) fn input_held(&mut self) -> Held {
        /// Command, Shift, Control and Option.
        const MODIFIERS: u64 = 0x0010_0000 | 0x0002_0000 | 0x0004_0000 | 0x0008_0000;
        let held = (0..3).any(quartz::button_held)
            || quartz::hid_flags() & MODIFIERS != 0
            || (0..128).any(quartz::key_held);
        if held {
            Held::Holding
        } else {
            Held::Released
        }
    }

    /// Before a takeover: the screen is usable and the user has not pressed
    /// a key or clicked for [`QUIET`], waiting at most that long.
    pub(crate) fn admit_takeover(&mut self, token: &Token) -> Result<(), Error> {
        if !self.spi.takeover() {
            return Err(Error::unsupported(Feature::Takeover));
        }
        if quartz::session().locked {
            return Err(Error::Refused(Refusal::ScreenLocked));
        }
        if quartz::display_asleep() {
            return Err(Error::Refused(Refusal::DisplayAsleep));
        }
        let limit = Instant::now() + QUIET;
        loop {
            let idle = quartz::press_idle();
            if idle >= QUIET {
                return Ok(());
            }
            let now = Instant::now();
            if now >= limit {
                return Err(Intervention::StillActive { idle }.into());
            }
            token.wait(
                QUIET
                    .saturating_sub(idle)
                    .min(limit.saturating_duration_since(now)),
            )?;
        }
    }

    pub(crate) fn press(
        &mut self,
        element: &AxHandle,
        delivery: &Delivery<'_>,
    ) -> Result<(), Error> {
        require_accessibility()?;
        let role = ax::native_role(element)?;
        let refuse_menu = delivery.mode == DeliveryMode::Background
            && delivery.menus == MenuPress::Refuse
            && opens_menu(&role);
        if refuse_menu {
            return Err(Error::Refused(Refusal::BackgroundUnavailable {
                detail: format!(
                    "pressing this {role} opens its menu, which takes the user's keyboard"
                )
                .into(),
            }));
        }
        let pid = element_pid(element)?;
        let perform = || {
            delivery.before_press(Sent::Nothing)?;
            element
                .perform("AXPress")
                .map_err(|code| ax::after_send(code, "pressing the element"))
        };
        match delivery.mode {
            DeliveryMode::Background => guard::watch(&self.spi, pid, |visit| {
                guard::still_behind(&self.spi, pid, &app_name(pid), visit, Sent::Nothing)?;
                perform()
            }),
            DeliveryMode::Takeover => perform(),
        }
    }

    pub(crate) fn set_value(
        &mut self,
        element: &AxHandle,
        value: &str,
        delivery: &Delivery<'_>,
    ) -> Result<ValueReadback, Error> {
        require_accessibility()?;
        match element.settable("AXValue") {
            Ok(true) => {}
            Ok(false) => {
                return Err(Error::Refused(Refusal::Ax {
                    detail: "the element's value cannot be written".into(),
                }))
            }
            Err(code) => return Err(ax::refused(code, "asking whether the value is writable")),
        }
        let field = match element.read("AXSubrole") {
            Ok(Some(Value::Text(subrole))) if subrole == "AXSecureTextField" => FieldKind::Secure,
            Ok(_) | Err(_) => FieldKind::Plain,
        };
        let pid = element_pid(element)?;
        let write = || {
            delivery.before_press(Sent::Nothing)?;
            element
                .write_text("AXValue", value)
                .map_err(|code| ax::after_send(code, "writing the value"))
        };
        match delivery.mode {
            DeliveryMode::Background => guard::watch(&self.spi, pid, |visit| {
                guard::still_behind(&self.spi, pid, &app_name(pid), visit, Sent::Nothing)?;
                write()
            })?,
            DeliveryMode::Takeover => write()?,
        }
        let actual = match element.read("AXValue") {
            Ok(Some(value)) => ax::stringify(&value),
            Ok(None) => Some(String::new()),
            Err(_) => None,
        };
        Ok(ValueReadback { actual, field })
    }

    /// The listed window `element` sits in, as input addresses it.
    fn element_window(&mut self, element: &AxHandle) -> Result<Window, Error> {
        let wid = ax::element_window_id(&self.spi, element).ok_or_else(|| {
            Error::Refused(Refusal::Ax {
                detail: "the element's window could not be identified".into(),
            })
        })?;
        self.windows()?
            .into_iter()
            .find(|window| windows::server_id(window) == Some(wid))
            .ok_or_else(|| {
                Error::Refused(Refusal::Ax {
                    detail: format!("the element's window {wid} is not on screen").into(),
                })
            })
    }

    pub(crate) fn element_input(
        &mut self,
        element: &AxHandle,
        typing: Typing<'_>,
        delivery: &Delivery<'_>,
    ) -> Result<(), Error> {
        require_accessibility()?;
        let window = self.element_window(element)?;
        let target = Target::of(&window)?;
        let presses = match typing {
            Typing::Text("") => return Ok(()),
            Typing::Text(text) => {
                if delivery.mode == DeliveryMode::Background
                    && self.insert_into(element, &target, text, delivery)? == Insertion::Inserted
                {
                    return Ok(());
                }
                keymap::text_presses(text)
            }
            Typing::Chord(chord) => chord_presses(chord)?,
        };
        let source = self.source()?;
        match delivery.mode {
            DeliveryMode::Background => input::background_keys(
                &self.spi,
                source,
                &target,
                Some(element),
                &presses,
                delivery,
            ),
            DeliveryMode::Takeover => input::takeover(&self.spi, &target, delivery, |foreground| {
                input::focus(element, target.pid)?;
                input::foreground_keys(source, &presses, foreground)
            }),
        }
    }

    /// AX insertion at the element's selection, focusing it first when an
    /// unfocused field publishes no settable selection.
    fn insert_into(
        &self,
        element: &AxHandle,
        target: &Target<'_>,
        text: &str,
        delivery: &Delivery<'_>,
    ) -> Result<Insertion, Error> {
        let app = target.window.app.as_str();
        guard::watch(&self.spi, target.pid, |visit| {
            let before_write = || {
                delivery.before_press(Sent::Nothing)?;
                guard::still_behind(&self.spi, target.pid, app, visit, Sent::Nothing)
            };
            match input::insert(element, text, before_write)? {
                Insertion::Inserted => Ok(Insertion::Inserted),
                Insertion::NotTaken => {
                    before_write()?;
                    input::focus(element, target.pid)?;
                    input::insert(element, text, before_write)
                }
            }
        })
    }

    #[allow(clippy::unused_self, reason = "the seam's signature")]
    pub(crate) fn text_value(&mut self, element: &AxHandle) -> Result<String, Error> {
        match element.read("AXValue") {
            Ok(Some(Value::Text(text))) => Ok(text),
            Ok(_) => Err(Error::Refused(Refusal::Ax {
                detail: "the element holds no text".into(),
            })),
            Err(code) => Err(ax::refused(code, "reading the element's text")),
        }
    }

    pub(crate) fn select_range(
        &mut self,
        element: &AxHandle,
        range: Utf16Range,
        delivery: &Delivery<'_>,
    ) -> Result<SelectionReadback, Error> {
        require_accessibility()?;
        let pid = element_pid(element)?;
        let units = |value: usize| {
            i64::try_from(value).map_err(|_| {
                Error::Refused(Refusal::Ax {
                    detail: "the selection is past the platform's range".into(),
                })
            })
        };
        let (start, length) = (units(range.start)?, units(range.length)?);
        let write = || {
            delivery.before_press(Sent::Nothing)?;
            element
                .write_range("AXSelectedTextRange", start, length)
                .map_err(|code| ax::after_send(code, "selecting the text"))
        };
        match delivery.mode {
            DeliveryMode::Background => guard::watch(&self.spi, pid, |visit| {
                guard::still_behind(&self.spi, pid, &app_name(pid), visit, Sent::Nothing)?;
                write()
            })?,
            DeliveryMode::Takeover => write()?,
        }
        let unread = || {
            Error::Unverified(Unverified::AxUnconfirmed {
                detail: "the selection was written but could not be read back".into(),
            })
        };
        let Ok(Some(Value::Range { location, length })) = element.read("AXSelectedTextRange")
        else {
            return Err(unread());
        };
        let Ok(Some(Value::Text(value))) = element.read("AXValue") else {
            return Err(unread());
        };
        let focus = match element.read("AXFocused") {
            Ok(Some(Value::Bool(true))) => Focus::Focused,
            Ok(_) | Err(_) => Focus::Unfocused,
        };
        Ok(SelectionReadback {
            range: Utf16Range {
                start: usize::try_from(location).map_err(|_| unread())?,
                length: usize::try_from(length).map_err(|_| unread())?,
            },
            value,
            focus,
        })
    }

    pub(crate) fn window_input(
        &mut self,
        window: &Window,
        typing: Typing<'_>,
        delivery: &Delivery<'_>,
    ) -> Result<(), Error> {
        require_accessibility()?;
        let target = Target::of(window)?;
        let presses = match typing {
            Typing::Text("") => return Ok(()),
            Typing::Text(text) => {
                if delivery.mode == DeliveryMode::Background
                    && self.insert_focused(&target, text, delivery)? == Insertion::Inserted
                {
                    return Ok(());
                }
                keymap::text_presses(text)
            }
            Typing::Chord(chord) => chord_presses(chord)?,
        };
        let source = self.source()?;
        match delivery.mode {
            DeliveryMode::Background => {
                input::background_keys(&self.spi, source, &target, None, &presses, delivery)
            }
            DeliveryMode::Takeover => input::takeover(&self.spi, &target, delivery, |foreground| {
                input::foreground_keys(source, &presses, foreground)
            }),
        }
    }

    /// AX insertion into the element holding focus in the target window.
    fn insert_focused(
        &self,
        target: &Target<'_>,
        text: &str,
        delivery: &Delivery<'_>,
    ) -> Result<Insertion, Error> {
        let Some(focused) = ax::focused_element(target.pid) else {
            return Ok(Insertion::NotTaken);
        };
        if ax::element_window_id(&self.spi, &focused) != Some(target.wid) {
            return Ok(Insertion::NotTaken);
        }
        let app = target.window.app.as_str();
        guard::watch(&self.spi, target.pid, |visit| {
            input::insert(&focused, text, || {
                delivery.before_press(Sent::Nothing)?;
                guard::still_behind(&self.spi, target.pid, app, visit, Sent::Nothing)
            })
        })
    }

    pub(crate) fn pointer(
        &mut self,
        window: &Window,
        event: &PointerEvent,
        delivery: &Delivery<'_>,
    ) -> Result<(), Error> {
        require_accessibility()?;
        let target = Target::of(window)?;
        let source = self.source()?;
        match delivery.mode {
            DeliveryMode::Background => {
                input::background_pointer(&self.spi, source, &target, event, delivery)
            }
            DeliveryMode::Takeover => input::takeover(&self.spi, &target, delivery, |foreground| {
                input::foreground_pointer(source, event, foreground)
            }),
        }
    }

    #[allow(clippy::unused_self, reason = "the seam's signature")]
    pub(crate) fn menu_items(
        &mut self,
        window: &Window,
        path: &[String],
    ) -> Result<Vec<MenuItem>, Error> {
        require_accessibility()?;
        menus::items(Target::of(window)?.pid, path)
    }

    pub(crate) fn menu_press(
        &mut self,
        window: &Window,
        path: &[String],
        delivery: &Delivery<'_>,
    ) -> Result<(), Error> {
        require_accessibility()?;
        menus::press(&self.spi, self.source()?, window, path, delivery)
    }
}

impl AxRead for Backend {
    type Handle = AxHandle;

    fn window_root(&mut self, window: &Window) -> Result<AxHandle, Error> {
        require_accessibility()?;
        ax::window_element(&self.spi, Target::of(window)?.pid, window)
    }

    fn walk_node(
        &mut self,
        handle: &AxHandle,
        bounds: WalkBounds,
        max_children: u32,
    ) -> Result<(AxProps, Vec<AxHandle>), Error> {
        let mut values = NodeValues::read(handle, &self.requests, NodeRead::of(bounds));
        let (mut children, answer) = values.take_children();
        let total = u32::try_from(children.len()).unwrap_or(u32::MAX);
        let actions = handle.actions().unwrap_or_default();
        let mut props = ax::props(&values, total, bounds, actions, ax::linked_label)?;
        match answer {
            ax::Answer::Answered => {
                let kept = total.min(max_children);
                children.truncate(usize::try_from(kept).unwrap_or(usize::MAX));
                props.unread_children = Unread::Count(total - kept);
            }
            ax::Answer::Unanswered => {
                props.unread_children = Unread::Unknown;
                props.fields = Completeness::Partial;
            }
        }
        Ok((props, children))
    }

    fn props(&mut self, handle: &AxHandle) -> Result<AxProps, Error> {
        let values = NodeValues::read(handle, &self.requests, NodeRead::Props);
        let child_count = handle.count("AXChildren").unwrap_or(0);
        let actions = handle.actions().unwrap_or_default();
        ax::props(
            &values,
            child_count,
            WalkBounds::Read,
            actions,
            ax::linked_label,
        )
    }

    /// An app answers `InvalidUIElement` only for an element it no longer
    /// has; a busy app answers otherwise.
    fn liveness(&mut self, handle: &AxHandle) -> Liveness {
        match handle.read("AXRole") {
            Err(AxCode::InvalidElement) => Liveness::Gone,
            Ok(_) | Err(_) => Liveness::Alive,
        }
    }

    fn focused_within(&mut self, handle: &AxHandle) -> Option<AxHandle> {
        ax::focused_element(handle.pid().ok()?)
    }

    fn value_settable(&mut self, handle: &AxHandle) -> Settable {
        match handle.settable("AXValue") {
            Ok(true) => Settable::Yes,
            Ok(false) => Settable::No,
            Err(_) => Settable::Unknown,
        }
    }
}

#[allow(
    clippy::unnecessary_wraps,
    reason = "the seam's signature; a missing folder only lists fewer apps"
)]
pub(crate) fn list_applications() -> Result<Vec<Application>, Error> {
    Ok(applications::list())
}

pub(crate) fn application_at(path: &Path) -> Result<Application, Error> {
    applications::at(path)
}

/// Agents, background-only apps and bundles nested in another app are
/// helpers.
pub(crate) fn app_kind(app: &Application) -> AppKind {
    applications::kind(app)
}

pub(crate) fn open_application(app: &Application, activation: Activation) -> Result<Opened, Error> {
    applications::open(app, activation, front_window)
}

pub(crate) fn open_document(
    target: &str,
    how: &Document<'_>,
    activation: Activation,
) -> Result<Opened, Error> {
    applications::open_document(target, how, activation, front_window)
}

pub(crate) fn window_roster() -> Result<Vec<RosterWindow>, Error> {
    let records = quartz::window_list().ok_or_else(|| {
        Error::Refused(Refusal::Platform {
            detail: "the window server did not list its windows".into(),
        })
    })?;
    Ok(windows::roster(records, grant()))
}

pub(crate) fn process_started(pid: Pid) -> Option<StartTime> {
    process::started(i32::try_from(pid.0).ok()?).map(StartTime)
}
