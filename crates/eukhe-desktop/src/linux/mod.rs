//! The Linux backend: X11 for the window list, capture and input, AT-SPI
//! for accessibility and menus (port of omp `crates/natives/src/desktop/linux/mod.rs`
//! and `linux/x11/mod.rs`). Wayland-only sessions are refused.

mod a11y;
mod applications;
mod x11;

use std::ffi::OsStr;

pub(crate) use a11y::AxHandle;
pub(crate) use applications::{
    app_kind, application_at, list_applications, open_application, open_document, process_started,
};
pub(crate) use x11::{window_roster, EscapeMonitor, UserInputMonitor};

use crate::ax::{ActionNames, AxProps, AxRead, Liveness, Settable, WalkBounds};
use crate::backend::{Delivery, PointerEvent, SelectionReadback, Typing, ValueReadback};
use crate::control::intervention::Held;
use crate::control::Token;
use crate::error::{Error, Feature, Refusal};
use crate::frame::Capture;
use crate::menus::MenuItem;
use crate::text_range::Utf16Range;
use crate::types::{
    Access, BackendKind, Capabilities, DeliveryMode, DisplayPower, Focus, Lock, ScreenState,
    SecureInput, Support, Window,
};

pub(crate) const BACKEND: BackendKind = BackendKind::X11;
/// AT-SPI action names are provider-defined: lines list none.
pub(crate) const ACTION_NAMES: ActionNames = ActionNames::Hidden;
pub(crate) const OPENS_DOCUMENTS: Support = Support::Unsupported;

/// The display server the session can drive.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Server {
    X11,
    WaylandOnly,
    Absent,
}

/// `DISPLAY` names an X server (`XWayland` included); a session with only
/// `WAYLAND_DISPLAY` has none.
fn server(display: Option<&OsStr>, wayland: Option<&OsStr>) -> Server {
    let set = |value: Option<&OsStr>| value.is_some_and(|value| !value.is_empty());
    match (set(display), set(wayland)) {
        (true, _) => Server::X11,
        (false, true) => Server::WaylandOnly,
        (false, false) => Server::Absent,
    }
}

/// The X11 connection and AT-SPI bus of one session.
pub(crate) struct Backend {
    x: x11::X11,
    bus: a11y::Bus,
}

impl Backend {
    pub(crate) fn open() -> Result<Self, Error> {
        let display = std::env::var_os("DISPLAY");
        let wayland = std::env::var_os("WAYLAND_DISPLAY");
        match server(display.as_deref(), wayland.as_deref()) {
            Server::X11 => {}
            Server::WaylandOnly => return Err(Error::unsupported(Feature::Wayland)),
            Server::Absent => {
                return Err(Error::Refused(Refusal::Platform {
                    detail: "no display server: neither DISPLAY nor WAYLAND_DISPLAY is set".into(),
                }));
            }
        }
        let x = x11::X11::open()?;
        let bus = a11y::Bus::connect(x.atspi_address().as_deref());
        Ok(Self { x, bus })
    }

    /// The bus, reconnecting once if it was missing: the bus launcher may
    /// have started since.
    fn a11y(&mut self) -> Result<&a11y::A11y, Error> {
        if let a11y::Bus::Missing(_) = self.bus {
            self.bus = a11y::Bus::connect(self.x.atspi_address().as_deref());
        }
        self.bus.a11y()
    }

    pub(crate) fn capabilities(&mut self) -> Capabilities {
        let extensions = self.x.extensions();
        let accessibility = match self.a11y() {
            Ok(_) => Access::Granted,
            Err(_) => Access::Denied,
        };
        let both = |a: Support, b: Support| match (a, b) {
            (Support::Supported, Support::Supported) => Support::Supported,
            (Support::Unsupported, _) | (_, Support::Unsupported) => Support::Unsupported,
        };
        Capabilities {
            backend: BACKEND,
            capture: Access::Granted,
            input: match extensions.xtest {
                Support::Supported => Access::Granted,
                Support::Unsupported => Access::Denied,
            },
            accessibility,
            background_input: both(extensions.xtest, extensions.xinput),
            takeover: both(extensions.xtest, extensions.xinput),
            menus: match accessibility {
                Access::Granted => Support::Supported,
                Access::Denied | Access::Unknown => Support::Unsupported,
            },
            applications: Support::Supported,
            escape_stop: extensions.xinput,
            secure_input: SecureInput::Off,
            screen: ScreenState {
                lock: Lock::Unlocked,
                display: DisplayPower::Awake,
            },
        }
    }

    pub(crate) fn windows(&mut self) -> Result<Vec<Window>, Error> {
        Ok(self.x.windows()?)
    }

    pub(crate) fn capture(&mut self, window: &Window) -> Result<Capture, Error> {
        self.x.capture(window)
    }

    pub(crate) fn input_held(&mut self) -> Held {
        self.x.input_held()
    }

    pub(crate) fn admit_takeover(&mut self, _: &Token) -> Result<(), Error> {
        self.x.admit_takeover()
    }

    pub(crate) fn press(
        &mut self,
        element: &AxHandle,
        delivery: &Delivery<'_>,
    ) -> Result<(), Error> {
        self.a11y()?.press(element, delivery)
    }

    pub(crate) fn set_value(
        &mut self,
        element: &AxHandle,
        value: &str,
        delivery: &Delivery<'_>,
    ) -> Result<ValueReadback, Error> {
        self.a11y()?.set_value(element, value, delivery)
    }

    /// Background text goes in through the element's editable-text
    /// interface, needing neither focus nor keys. Background keys go only to
    /// an element that holds its window's keyboard focus, as GTK 3 reports
    /// it: a focus request makes toolkits present the window. Takeover
    /// focuses the element and sends keys.
    pub(crate) fn element_input(
        &mut self,
        element: &AxHandle,
        typing: Typing<'_>,
        delivery: &Delivery<'_>,
    ) -> Result<(), Error> {
        self.a11y()?;
        let a11y = self.bus.a11y()?;
        let frame = a11y.frame_of(element)?;
        let window = self.x.window_of(frame.pid, &frame.title)?;
        match delivery.mode {
            DeliveryMode::Background => {
                let declined = match typing {
                    Typing::Text(text) => match a11y.insert_text(element, text, delivery)? {
                        a11y::TextRoute::Inserted => return Ok(()),
                        a11y::TextRoute::Absent => None,
                        a11y::TextRoute::Declined => {
                            Some("the application refused the inserted text")
                        }
                    },
                    Typing::Chord(_) => None,
                };
                let refusal = match a11y.key_focus(element)? {
                    a11y::KeyFocus::Reported(Focus::Focused) => None,
                    a11y::KeyFocus::Reported(Focus::Unfocused) => {
                        Some(format!("the element does not hold the keyboard focus of window {}", window.id))
                    }
                    a11y::KeyFocus::Unreported(toolkit) => Some(format!(
                        "keys sent to window {} may miss the element, since its {} toolkit does not \
                         report which element holds the window's keyboard",
                        window.id,
                        if toolkit.is_empty() { "unidentified" } else { toolkit.as_str() }
                    )),
                };
                if let Some(reason) = refusal {
                    let declined = declined.map_or_else(String::new, |why| {
                        format!("; its accessibility text route was not used, since {why}")
                    });
                    return Err(Error::Refused(Refusal::BackgroundUnavailable {
                        detail: format!(
                            "{reason}, and focusing it would bring that window to the front{declined}"
                        )
                        .into(),
                    }));
                }
                self.x.window_keys(&window, typing, delivery)
            }
            DeliveryMode::Takeover => self
                .x
                .takeover_keys(&window, typing, delivery, || a11y.grab_focus(element)),
        }
    }

    pub(crate) fn text_value(&mut self, element: &AxHandle) -> Result<String, Error> {
        self.a11y()?.text(element)
    }

    pub(crate) fn select_range(
        &mut self,
        element: &AxHandle,
        range: Utf16Range,
        delivery: &Delivery<'_>,
    ) -> Result<SelectionReadback, Error> {
        self.a11y()?.select(element, range, delivery)
    }

    pub(crate) fn window_input(
        &mut self,
        window: &Window,
        typing: Typing<'_>,
        delivery: &Delivery<'_>,
    ) -> Result<(), Error> {
        self.x.window_keys(window, typing, delivery)
    }

    pub(crate) fn pointer(
        &mut self,
        window: &Window,
        event: &PointerEvent,
        delivery: &Delivery<'_>,
    ) -> Result<(), Error> {
        self.x.pointer(window, event, delivery)
    }

    pub(crate) fn menu_items(
        &mut self,
        window: &Window,
        path: &[String],
    ) -> Result<Vec<MenuItem>, Error> {
        let a11y = self.a11y()?;
        let root = a11y.window_root(window)?;
        a11y::menu_items(a11y, &root, path)
    }

    pub(crate) fn menu_press(
        &mut self,
        window: &Window,
        path: &[String],
        delivery: &Delivery<'_>,
    ) -> Result<(), Error> {
        let a11y = self.a11y()?;
        let root = a11y.window_root(window)?;
        a11y::menu_press(a11y, &root, path, delivery)
    }
}

impl AxRead for Backend {
    type Handle = AxHandle;

    fn window_root(&mut self, window: &Window) -> Result<AxHandle, Error> {
        self.a11y()?.window_root(window)
    }

    fn walk_node(
        &mut self,
        handle: &AxHandle,
        bounds: WalkBounds,
        max_children: u32,
    ) -> Result<(AxProps, Vec<AxHandle>), Error> {
        self.a11y()?.read_node(handle, bounds, Some(max_children))
    }

    fn props(&mut self, handle: &AxHandle) -> Result<AxProps, Error> {
        self.a11y()?
            .read_node(handle, WalkBounds::Read, None)
            .map(|(props, _)| props)
    }

    fn liveness(&mut self, handle: &AxHandle) -> Liveness {
        match self.a11y() {
            Ok(a11y) => a11y.liveness(handle),
            Err(_) => Liveness::Alive,
        }
    }

    fn focused_within(&mut self, handle: &AxHandle) -> Option<AxHandle> {
        self.a11y().ok()?.focused_within(handle)
    }

    fn value_settable(&mut self, handle: &AxHandle) -> Settable {
        match self.a11y() {
            Ok(a11y) => a11y.value_settable(handle),
            Err(_) => Settable::Unknown,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn only_a_wayland_display_is_refused_and_xwayland_is_driven() {
        let some = Some(OsStr::new(":0"));
        let wayland = Some(OsStr::new("wayland-0"));
        assert_eq!(server(some, None), Server::X11);
        assert_eq!(server(some, wayland), Server::X11);
        assert_eq!(server(None, wayland), Server::WaylandOnly);
        assert_eq!(server(Some(OsStr::new("")), wayland), Server::WaylandOnly);
        assert_eq!(server(None, None), Server::Absent);
    }
}
