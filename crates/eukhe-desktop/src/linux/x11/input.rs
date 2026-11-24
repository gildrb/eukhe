//! X11 input routes (port of omp `crates/natives/src/desktop/linux/x11/input.rs`
//! and `x11/mpx.rs`).
//!
//! - Background: an XI2 MPX master pair of the session's own. XTEST on a
//!   connection whose client pointer is that pair moves its pointer and types
//!   on its keyboard (`XISetFocus`), never the user's; core events are off,
//!   so window managers never see it. omp drives the pair with uinput slaves;
//!   XTEST reaches it without `/dev/uinput` or udev hotplug.
//! - Takeover: activates the target, sends core XTEST, then hands focus and
//!   the pointer back.

use std::time::Duration;

use x11rb::connection::Connection;
use x11rb::protocol::xinput::{
    self, ConnectionExt as _, DeviceType, HierarchyChange, HierarchyChangeData,
    HierarchyChangeDataAddMaster,
};
use x11rb::protocol::xproto::{self, ConnectionExt as _, KeyButMask};
use x11rb::protocol::xtest::ConnectionExt as _;
use x11rb::rust_connection::RustConnection;
use x11rb::CURRENT_TIME;

use super::keymap::{self, Keycode, Keymap, Stroke};
use super::{landed, refused, XError, XWindow, X11};
use crate::backend::{Delivery, MouseButton, PointerEvent, Typing};
use crate::control::intervention::Held;
use crate::control::{Sent, Token};
use crate::error::{Detail, Error, Feature, Intervention, Refusal};
use crate::geometry::GlobalPoint;
use crate::keys::Modifiers;
use crate::types::{DeliveryMode, Support, Window};

/// The session's master pair: `eukhe pointer` and `eukhe keyboard`.
const PAIR_NAME: &[u8] = b"eukhe";
const PAIR_POINTER: &[u8] = b"eukhe pointer";
/// How long each button and key stays down, so toolkits see two frames.
const PRESS_HOLD: Duration = Duration::from_millis(12);
/// Release to next press of a multi-click, well under GTK's 250 ms
/// double-click time.
const CLICK_GAP: Duration = Duration::from_millis(50);
const SCROLL_GAP: Duration = Duration::from_millis(35);
const KEY_GAP: Duration = Duration::from_millis(10);
/// Lets the toolkit take the last event before focus and pointer go back.
const TAKEOVER_SETTLE: Duration = Duration::from_millis(120);
/// Most scroll detents one step sends.
const MAX_DETENTS: u32 = 100;

/// Asks for `XInput` 2.2, which MPX and raw events need.
pub(super) fn xi2(conn: &RustConnection) -> Result<Support, XError> {
    let version = conn.xinput_xi_query_version(2, 2)?.reply()?;
    Ok(
        if (version.major_version, version.minor_version) >= (2, 2) {
            Support::Supported
        } else {
            Support::Unsupported
        },
    )
}

/// The background route, set up on first use.
pub(in crate::linux) enum Pair {
    Unprobed,
    /// Boxed: a connection is large next to the other states.
    Ready(Box<Mpx>),
    Unavailable(Detail),
}

/// A connection whose XTEST input drives the session's master pair.
pub(in crate::linux) struct Mpx {
    conn: RustConnection,
    root: xproto::Window,
    keyboard: xinput::DeviceId,
}

impl Mpx {
    fn acquire() -> Result<Self, XError> {
        let (conn, screen) = RustConnection::connect(None)?;
        let root = conn
            .setup()
            .roots
            .get(screen)
            .map(|screen| screen.root)
            .ok_or(XError::NoScreen)?;
        xi2(&conn)?;
        let pair = if let Some(pair) = find_pair(&conn)? {
            pair
        } else {
            // A pair stays for the server's life: removing masters crashes
            // Qt 6.5+ clients (QTBUG-146876) and mutter 42.
            let add = HierarchyChangeDataAddMaster {
                send_core: false,
                enable: true,
                name: PAIR_NAME.to_vec(),
            };
            let words = 2 + PAIR_NAME.len().div_ceil(4);
            let change = HierarchyChange {
                len: u16::try_from(words).unwrap_or(u16::MAX),
                data: HierarchyChangeData::AddMaster(add),
            };
            conn.xinput_xi_change_hierarchy(&[change])?.check()?;
            find_pair(&conn)?.ok_or(XError::NoPair)?
        };
        let (pointer, keyboard) = pair;
        conn.xinput_xi_set_client_pointer(x11rb::NONE, pointer)?
            .check()?;
        Ok(Self {
            conn,
            root,
            keyboard,
        })
    }

    fn xtest(&self) -> Xtest<'_> {
        Xtest {
            conn: &self.conn,
            root: self.root,
        }
    }

    fn focus(&self, window: XWindow) -> Result<(), XError> {
        self.conn
            .xinput_xi_set_focus(window.0, CURRENT_TIME, self.keyboard)?
            .check()?;
        Ok(())
    }
}

/// The master pointer named for the session's pair and its keyboard.
fn find_pair(
    conn: &RustConnection,
) -> Result<Option<(xinput::DeviceId, xinput::DeviceId)>, XError> {
    let devices = conn
        .xinput_xi_query_device(xinput::Device::ALL_MASTER)?
        .reply()?;
    Ok(devices
        .infos
        .iter()
        .find(|info| info.type_ == DeviceType::MASTER_POINTER && info.name == PAIR_POINTER)
        .map(|info| (info.deviceid, info.attachment)))
}

/// XTEST on one connection: the core devices, or the pair its client
/// pointer names.
#[derive(Clone, Copy)]
struct Xtest<'a> {
    conn: &'a RustConnection,
    root: xproto::Window,
}

impl Xtest<'_> {
    fn send(&self, kind: u8, detail: u8, (x, y): (i16, i16)) -> Result<(), XError> {
        self.conn
            .xtest_fake_input(kind, detail, CURRENT_TIME, self.root, x, y, 0)?;
        Ok(())
    }

    fn motion(&self, at: (i16, i16)) -> Result<(), XError> {
        self.send(xproto::MOTION_NOTIFY_EVENT, 0, at)
    }

    fn button(&self, press: bool, button: u8) -> Result<(), XError> {
        let kind = if press {
            xproto::BUTTON_PRESS_EVENT
        } else {
            xproto::BUTTON_RELEASE_EVENT
        };
        self.send(kind, button, (0, 0))
    }

    fn key(&self, press: bool, code: Keycode) -> Result<(), XError> {
        let kind = if press {
            xproto::KEY_PRESS_EVENT
        } else {
            xproto::KEY_RELEASE_EVENT
        };
        self.send(kind, code.0, (0, 0))
    }

    /// Waits until the server ran every request sent so far.
    fn sync(&self) -> Result<(), XError> {
        self.conn.get_input_focus()?.reply()?;
        Ok(())
    }
}

/// One gesture's sending: what went out, and the step's checks between.
struct Gesture<'a> {
    xtest: Xtest<'a>,
    delivery: &'a Delivery<'a>,
    sent: Sent,
}

impl<'a> Gesture<'a> {
    fn new(xtest: Xtest<'a>, delivery: &'a Delivery<'a>) -> Self {
        Self {
            xtest,
            delivery,
            sent: Sent::Nothing,
        }
    }

    /// The step's check before a press, then the press.
    fn press(&mut self, send: impl FnOnce(Xtest<'a>) -> Result<(), XError>) -> Result<(), Error> {
        self.delivery.before_press(self.sent)?;
        self.sent = Sent::Some;
        send(self.xtest).map_err(|error| landed(&error))
    }

    /// A release or motion: never refused, since a held key must come up.
    fn release(&self, send: impl FnOnce(Xtest<'a>) -> Result<(), XError>) -> Result<(), Error> {
        send(self.xtest).map_err(|error| self.failed(&error))
    }

    fn failed(&self, error: &XError) -> Error {
        match self.sent {
            Sent::Nothing => refused(error),
            Sent::Some => landed(error),
        }
    }

    /// A refusal built here: `Refused` before input went out, else
    /// `InputFailed`.
    fn refuse(&self, detail: String) -> Error {
        match self.sent {
            Sent::Nothing => Error::Refused(Refusal::Platform {
                detail: detail.into(),
            }),
            Sent::Some => Error::Unverified(crate::error::Unverified::InputFailed {
                detail: detail.into(),
            }),
        }
    }

    fn pause(&self, duration: Duration) -> Result<(), Error> {
        self.xtest
            .conn
            .flush()
            .map_err(|error| self.failed(&XError::from(error)))?;
        match self.delivery.token().wait(duration) {
            Ok(()) => Ok(()),
            Err(_) => self.delivery.before_press(self.sent),
        }
    }

    /// Holds `modifiers`, runs `body`, releases them in reverse whatever
    /// `body` returned.
    fn holding(
        &mut self,
        modifiers: &[Keycode],
        body: impl FnOnce(&mut Self) -> Result<(), Error>,
    ) -> Result<(), Error> {
        let mut held = 0;
        let mut result = Ok(());
        for code in modifiers {
            result = self.press(|xtest| xtest.key(true, *code));
            if result.is_err() {
                break;
            }
            held += 1;
        }
        if result.is_ok() {
            result = body(self);
        }
        for code in modifiers[..held].iter().rev() {
            let released = self.release(|xtest| xtest.key(false, *code));
            result = result.and(released);
        }
        result
    }

    /// Taps `code`: press, hold, release.
    fn tap(&mut self, code: Keycode) -> Result<(), Error> {
        self.press(|xtest| xtest.key(true, code))?;
        let held = self.pause(PRESS_HOLD);
        let released = self.release(|xtest| xtest.key(false, code));
        held.and(released)
    }

    fn click(&mut self, button: u8, count: u8) -> Result<(), Error> {
        for index in 0..count {
            if index > 0 {
                self.pause(CLICK_GAP)?;
            }
            self.press(|xtest| xtest.button(true, button))?;
            let held = self.pause(PRESS_HOLD);
            let released = self.release(|xtest| xtest.button(false, button));
            held.and(released)?;
        }
        Ok(())
    }

    fn finish(&self) -> Result<(), Error> {
        self.xtest.sync().map_err(|error| self.failed(&error))
    }
}

/// X button numbers: 1 left, 2 middle, 3 right; 4 to 7 scroll up, down,
/// left, right.
fn button(button: MouseButton) -> u8 {
    match button {
        MouseButton::Left => 1,
        MouseButton::Middle => 2,
        MouseButton::Right => 3,
    }
}

/// The scroll buttons and detents of a delta in lines.
fn detents(dx: i32, dy: i32) -> [(u8, u32); 2] {
    let axis = |delta: i32, negative: u8, positive: u8| {
        let button = if delta < 0 { negative } else { positive };
        (button, delta.unsigned_abs().min(MAX_DETENTS))
    };
    [axis(dy, 4, 5), axis(dx, 6, 7)]
}

/// A global point as root coordinates.
fn root_point(point: GlobalPoint) -> Result<(i16, i16), Error> {
    match (coordinate(point.x), coordinate(point.y)) {
        (Some(x), Some(y)) => Ok((x, y)),
        _ => Err(Error::Refused(Refusal::Platform {
            detail: "the point lies outside the X coordinate range".into(),
        })),
    }
}

#[allow(
    clippy::cast_possible_truncation,
    reason = "the value is rounded and checked to lie in i16's range first"
)]
fn coordinate(value: f64) -> Option<i16> {
    let rounded = value.round();
    (rounded.is_finite() && rounded >= f64::from(i16::MIN) && rounded <= f64::from(i16::MAX))
        .then_some(rounded as i16)
}

fn unavailable(detail: impl Into<Detail>) -> Error {
    Error::Refused(Refusal::BackgroundUnavailable {
        detail: detail.into(),
    })
}

impl X11 {
    fn core_xtest(&self) -> Xtest<'_> {
        Xtest {
            conn: &self.conn,
            root: self.root,
        }
    }

    /// Sets the pair up on first use.
    fn probe_pair(&mut self) {
        if let Pair::Unprobed = self.pair {
            self.pair = match self.extensions.xinput {
                Support::Unsupported => Pair::Unavailable("the X server lacks XInput 2.2".into()),
                Support::Supported => match Mpx::acquire() {
                    Ok(mpx) => Pair::Ready(Box::new(mpx)),
                    Err(error) => Pair::Unavailable(error.to_string().into()),
                },
            };
        }
    }

    /// The pair [`Self::probe_pair`] set up.
    fn pair(&self) -> Result<&Mpx, Error> {
        match &self.pair {
            Pair::Ready(mpx) => Ok(mpx),
            Pair::Unavailable(detail) => Err(unavailable(format!(
                "the session's virtual input devices are unavailable ({detail})"
            ))),
            Pair::Unprobed => Err(unavailable(
                "the session's virtual input devices were not set up",
            )),
        }
    }

    pub(super) fn keymap(&self) -> Result<Keymap, XError> {
        let setup = self.conn.setup();
        let (min, max) = (setup.min_keycode, setup.max_keycode);
        let reply = self
            .conn
            .get_keyboard_mapping(min, max - min + 1)?
            .reply()?;
        Ok(Keymap::new(min, reply.keysyms_per_keycode, reply.keysyms))
    }

    fn strokes(&self, typing: Typing<'_>) -> Result<(Keymap, Vec<Stroke>), Error> {
        let keymap = self.keymap()?;
        let planned = match typing {
            Typing::Text(text) => keymap::plan_text(&keymap, text),
            Typing::Chord(chord) => keymap::plan_chord(&keymap, chord).map(|stroke| vec![stroke]),
        };
        let strokes = planned.map_err(|error| {
            Error::Refused(Refusal::Platform {
                detail: error.to_string().into(),
            })
        })?;
        Ok((keymap, strokes))
    }

    /// The step's pointer input at a point of `window`.
    pub(in crate::linux) fn pointer(
        &mut self,
        window: &Window,
        event: &PointerEvent,
        delivery: &Delivery<'_>,
    ) -> Result<(), Error> {
        let target = XWindow::of(&window.id)?;
        let (at, modifiers) = match event {
            PointerEvent::Click { at, modifiers, .. } => (root_point(*at)?, *modifiers),
            PointerEvent::Scroll { at, .. } => (root_point(*at)?, Modifiers::NONE),
        };
        let keymap = self.keymap()?;
        let held = keymap::modifier_codes(&keymap, modifiers).map_err(|error| {
            Error::Refused(Refusal::Platform {
                detail: error.to_string().into(),
            })
        })?;
        match delivery.mode {
            DeliveryMode::Background => {
                match self.shown_at(at.0, at.1)? {
                    Some(top) if self.is_within(target.0, top) => {}
                    Some(top) => {
                        return Err(unavailable(format!(
                            "window {} covers the point, and a background click would reach it",
                            top.0
                        )));
                    }
                    None => return Err(unavailable("no window shows the point")),
                }
                self.probe_pair();
                let mpx = self.pair()?;
                gesture(mpx.xtest(), delivery, at, event, &held)
            }
            DeliveryMode::Takeover => self.takeover(target, delivery.token(), Some(at), |this| {
                gesture(this.core_xtest(), delivery, at, event, &held)
            }),
        }
    }

    /// Keys for `window`'s focused element.
    pub(in crate::linux) fn window_keys(
        &mut self,
        window: &Window,
        typing: Typing<'_>,
        delivery: &Delivery<'_>,
    ) -> Result<(), Error> {
        let target = XWindow::of(&window.id)?;
        let (keymap, strokes) = self.strokes(typing)?;
        match delivery.mode {
            DeliveryMode::Background => {
                self.probe_pair();
                let mpx = self.pair()?;
                mpx.focus(target)?;
                type_strokes(&self.conn, &keymap, mpx.xtest(), &strokes, delivery)
            }
            DeliveryMode::Takeover => self.takeover(target, delivery.token(), None, |this| {
                type_strokes(&this.conn, &keymap, this.core_xtest(), &strokes, delivery)
            }),
        }
    }

    /// Keys sent in a takeover of `window`, after `prepare` (an element's
    /// focus request, which may raise the window) ran inside it.
    pub(in crate::linux) fn takeover_keys(
        &mut self,
        window: &Window,
        typing: Typing<'_>,
        delivery: &Delivery<'_>,
        prepare: impl FnOnce() -> Result<(), Error>,
    ) -> Result<(), Error> {
        let target = XWindow::of(&window.id)?;
        let (keymap, strokes) = self.strokes(typing)?;
        self.takeover(target, delivery.token(), None, |this| {
            prepare()?;
            type_strokes(&this.conn, &keymap, this.core_xtest(), &strokes, delivery)
        })
    }

    /// Activates `window`, runs `body`, then gives the user's focus and
    /// pointer back. `moves_to` is where `body` leaves the core pointer.
    fn takeover(
        &self,
        window: XWindow,
        token: &Token,
        moves_to: Option<(i16, i16)>,
        body: impl FnOnce(&Self) -> Result<(), Error>,
    ) -> Result<(), Error> {
        let user = self.user_state()?;
        if let Err(error) = self.activate(window, token) {
            self.hand_back(&user, window, None);
            return Err(error);
        }
        let result = body(self);
        // The toolkit reads the state the input left before it changes.
        std::thread::sleep(TAKEOVER_SETTLE);
        self.hand_back(&user, window, moves_to);
        result
    }

    /// Whether the user holds a key or button on the core devices now.
    pub(in crate::linux) fn input_held(&self) -> Held {
        let keys = self
            .conn
            .query_keymap()
            .ok()
            .and_then(|cookie| cookie.reply().ok());
        let pointer = self
            .conn
            .query_pointer(self.root)
            .ok()
            .and_then(|cookie| cookie.reply().ok());
        let buttons = KeyButMask::BUTTON1
            | KeyButMask::BUTTON2
            | KeyButMask::BUTTON3
            | KeyButMask::BUTTON4
            | KeyButMask::BUTTON5;
        match (keys, pointer) {
            (Some(keys), Some(pointer)) => {
                if keys.keys.iter().any(|byte| *byte != 0)
                    || u16::from(pointer.mask) & u16::from(buttons) != 0
                {
                    Held::Holding
                } else {
                    Held::Released
                }
            }
            _ => Held::Unknown,
        }
    }

    /// A takeover needs XTEST for its input and `XInput` 2 to watch the
    /// user's, and starts only once they hold nothing.
    pub(in crate::linux) fn admit_takeover(&self) -> Result<(), Error> {
        match (self.extensions.xtest, self.extensions.xinput) {
            (Support::Supported, Support::Supported) => {}
            (Support::Unsupported, _) | (_, Support::Unsupported) => {
                return Err(Error::unsupported(Feature::Takeover));
            }
        }
        match self.input_held() {
            Held::Holding => Err(Intervention::TakeoverStart.into()),
            Held::Released | Held::Unknown => Ok(()),
        }
    }
}

/// A click or scroll at `at`, with `modifiers` held.
fn gesture(
    xtest: Xtest<'_>,
    delivery: &Delivery<'_>,
    at: (i16, i16),
    event: &PointerEvent,
    modifiers: &[Keycode],
) -> Result<(), Error> {
    let mut gesture = Gesture::new(xtest, delivery);
    gesture.press(|xtest| xtest.motion(at))?;
    gesture.holding(modifiers, |gesture| match event {
        PointerEvent::Click {
            button: which,
            count,
            ..
        } => gesture.click(button(*which), count.get()),
        PointerEvent::Scroll { delta, .. } => {
            for (button, count) in detents(delta.dx, delta.dy) {
                for _ in 0..count {
                    gesture.click(button, 1)?;
                    gesture.pause(SCROLL_GAP)?;
                }
            }
            Ok(())
        }
    })?;
    gesture.finish()
}

/// Types `strokes` through `xtest`. A character the layout lacks borrows a
/// spare keycode of the core map (`main`), given back right after.
fn type_strokes(
    main: &RustConnection,
    keymap: &Keymap,
    xtest: Xtest<'_>,
    strokes: &[Stroke],
    delivery: &Delivery<'_>,
) -> Result<(), Error> {
    let mut gesture = Gesture::new(xtest, delivery);
    for stroke in strokes {
        match stroke {
            Stroke::Mapped { modifiers, key } => {
                gesture.holding(modifiers, |gesture| match key {
                    Some(code) => gesture.tap(*code),
                    None => Ok(()),
                })?;
            }
            Stroke::Borrowed { keysym } => {
                let spare = keymap.spare().ok_or_else(|| {
                    gesture.refuse(format!(
                        "the keyboard layout lacks keysym {:#x} and has no free keycode to lend it",
                        keysym.0
                    ))
                })?;
                let width = keymap.per_code().max(1);
                let row = vec![keysym.0; usize::from(width)];
                lend(main, spare, width, &row).map_err(|error| gesture.failed(&error))?;
                let typed = gesture.tap(spare);
                // The key must reach the server before its keysym goes back.
                let synced = xtest.sync().map_err(|error| landed(&error));
                let restored = lend(main, spare, width, &vec![0; row.len()]);
                typed?;
                synced?;
                restored.map_err(|error| landed(&error))?;
            }
        }
        gesture.pause(KEY_GAP)?;
    }
    gesture.finish()
}

/// Maps `code` to `keysyms` in the core keymap and waits until the server
/// applied it, so input on another connection meets the new mapping.
fn lend(main: &RustConnection, code: Keycode, width: u8, keysyms: &[u32]) -> Result<(), XError> {
    main.change_keyboard_mapping(1, code.0, width, keysyms)?;
    main.get_input_focus()?.reply()?;
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn scroll_lines_become_detents_of_the_matching_buttons() {
        assert_eq!(detents(0, 3), [(5, 3), (7, 0)]);
        assert_eq!(detents(-2, -1), [(4, 1), (6, 2)]);
        assert_eq!(detents(0, 1_000), [(5, MAX_DETENTS), (7, 0)]);
    }

    #[test]
    fn points_round_into_root_coordinates() {
        assert_eq!(root_point(GlobalPoint { x: 10.4, y: 20.6 }), Ok((10, 21)));
        assert!(root_point(GlobalPoint {
            x: f64::NAN,
            y: 0.0
        })
        .is_err());
        assert!(root_point(GlobalPoint {
            x: 70_000.0,
            y: 0.0
        })
        .is_err());
    }
}
