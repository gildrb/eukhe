//! Input to one window: background keys and pointer events routed to its
//! process through `SkyLight`, AX text insertion, and the takeover rerun that
//! brings the window in front and hands focus back (port of omp
//! `crates/natives/src/desktop/macos/input.rs`).

use std::thread;
use std::time::Duration;

use super::ax;
use super::ffi::ax::{AxCode, AxHandle, Value};
use super::ffi::quartz::{self, Event, Source};
use super::ffi::sky::{Psn, Spi, CPS_NO_WINDOWS, CPS_USER_GENERATED};
use super::guard;
use super::keymap::{Edge, Press};
use super::windows;
use crate::backend::{Delivery, MouseButton, PointerEvent};
use crate::control::Sent;
use crate::error::{Detail, Error, Refusal, Unverified};
use crate::keys::{Modifier, Modifiers};
use crate::types::Window;

/// `kCGEventSourceUserData` on every event this backend posts, so its own
/// taps tell them from the user's.
pub(super) const SYNTHETIC_TAG: i64 = 0x6575_6b68_6564;

const FIELD_MOUSE_EVENT_NUMBER: u32 = 0;
const FIELD_CLICK_STATE: u32 = 1;
const FIELD_PRESSURE: u32 = 2;
const FIELD_BUTTON_NUMBER: u32 = 3;
const FIELD_SUBTYPE: u32 = 7;
const FIELD_TARGET_PID: u32 = 40;
const FIELD_USER_DATA: u32 = 42;
const FIELD_WINDOW_NUMBER: u32 = 51;
const FIELD_WINDOW_CONTEXT: u32 = 52;
const FIELD_APPKIT_SUBTYPE: u32 = 83;
const FIELD_WINDOW_UNDER_POINTER: u32 = 91;
const FIELD_WINDOW_UNDER_POINTER_THAT_CAN_HANDLE: u32 = 92;
const SUBTYPE_TOUCH: i64 = 3;
/// `NSEventTypeAppKitDefined` and its application-activated subtype.
const APPKIT_DEFINED: u32 = 13;
const APPLICATION_ACTIVATED: i64 = 1;
const ACTIVATION_FLAGS: u64 = 0xc_0000;

const MOUSE_MOVED: u32 = 5;
const SCROLL_WHEEL: u32 = 22;

/// How long a window may take to become its app's key window.
const KEY_WINDOW_TIMEOUT: Duration = Duration::from_millis(250);
/// How long an element may take to take keyboard focus.
const ELEMENT_FOCUS_TIMEOUT: Duration = Duration::from_millis(250);
/// How long an app may take to say it is active after the activation event.
const ACTIVE_STATE_TIMEOUT: Duration = Duration::from_millis(500);
/// How long a takeover's window may take to come in front.
const ACTIVATION_TIMEOUT: Duration = Duration::from_millis(400);
const POLL: Duration = Duration::from_millis(10);
const KEY_GAP: Duration = Duration::from_millis(8);
/// An `NSButton` press enters a tracking loop that can miss a release
/// arriving before its first poll.
const PRESS_GAP: Duration = Duration::from_millis(28);
const MULTI_CLICK_GAP: Duration = Duration::from_millis(80);
/// Lets the target take foreground input before focus goes back.
const FOREGROUND_SETTLE: Duration = Duration::from_millis(40);

/// The window input goes to.
pub(super) struct Target<'w> {
    pub(super) pid: i32,
    pub(super) wid: u32,
    pub(super) window: &'w Window,
}

impl<'w> Target<'w> {
    pub(super) fn of(window: &'w Window) -> Result<Self, Error> {
        let pid = window.pid.and_then(|pid| i32::try_from(pid.0).ok());
        match (pid, windows::server_id(window)) {
            (Some(pid), Some(wid)) => Ok(Self { pid, wid, window }),
            (None, _) | (_, None) => Err(Error::Refused(Refusal::Platform {
                detail: format!(
                    "window {} has no owning process or window number",
                    window.id
                )
                .into(),
            })),
        }
    }

    /// `(x, y)` relative to the window's top-left, title bar included.
    fn local(&self, x: f64, y: f64) -> (f64, f64) {
        (
            x - f64::from(self.window.bounds.x),
            y - f64::from(self.window.bounds.y),
        )
    }
}

/// What background input makes the window key for.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum Purpose {
    /// Keys: no activating press when the window is key already.
    Keyboard,
    /// A left click, which goes to the window under it.
    Pointer,
    /// Menu commands, which dispatch through the key window.
    Menu,
}

fn unavailable(detail: impl Into<Detail>) -> Error {
    Error::Refused(Refusal::BackgroundUnavailable {
        detail: detail.into(),
    })
}

fn input_failed(detail: impl Into<Detail>) -> Error {
    Error::Unverified(Unverified::InputFailed {
        detail: detail.into(),
    })
}

fn tagged(event: Option<Event>) -> Result<Event, Error> {
    let event = event.ok_or_else(|| {
        Error::Refused(Refusal::Platform {
            detail: "Quartz did not create an input event".into(),
        })
    })?;
    event.set_field(FIELD_USER_DATA, SYNTHETIC_TAG);
    Ok(event)
}

pub(super) fn modifier_flags(modifiers: Modifiers) -> u64 {
    modifiers
        .iter()
        .map(|modifier| match modifier {
            Modifier::Ctrl => 0x0004_0000,
            Modifier::Alt => 0x0008_0000,
            Modifier::Shift => 0x0002_0000,
            Modifier::Meta => 0x0010_0000,
        })
        .fold(0, |flags, flag| flags | flag)
}

/// Tells the background app it is active with the target window key, as
/// `AppKit` does for a real activation, while `WindowServer`'s front process
/// stays the user's. With `purpose` other than keys, or when the window is
/// not key yet, posts the press just outside its frame that makes it key.
pub(super) fn make_key(
    spi: &Spi,
    source: &Source,
    target: &Target<'_>,
    purpose: Purpose,
) -> Result<(), Error> {
    let context = spi
        .connection()
        .ok_or_else(|| unavailable("the SkyLight connection is unavailable"))?;
    let activation = tagged(Event::blank(source))?;
    activation.set_type(APPKIT_DEFINED);
    activation.set_flags(ACTIVATION_FLAGS);
    spi.set_fields(
        &activation,
        &[
            (FIELD_WINDOW_NUMBER, i64::from(target.wid)),
            (FIELD_WINDOW_CONTEXT, context),
            (FIELD_APPKIT_SUBTYPE, APPLICATION_ACTIVATED),
        ],
    );
    spi.post_routed(target.pid, &activation);
    guard::wait_for(ACTIVE_STATE_TIMEOUT, POLL, || {
        ax::reports_active(target.pid) != Some(false)
    });
    if purpose == Purpose::Keyboard && ax::focused_window_id(spi, target.pid) == Some(target.wid) {
        return Ok(());
    }
    let x = f64::from(target.window.bounds.x) - 1.0;
    let y = f64::from(target.window.bounds.y) - 1.0;
    for (kind, number) in [(1, 1), (2, 2)] {
        let press = tagged(Event::mouse(source, kind, x, y, 0))?;
        spi.set_fields(
            &press,
            &[
                (FIELD_MOUSE_EVENT_NUMBER, number),
                (FIELD_CLICK_STATE, 1),
                (FIELD_PRESSURE, 255),
                (FIELD_BUTTON_NUMBER, 0),
                (FIELD_SUBTYPE, SUBTYPE_TOUCH),
                (FIELD_WINDOW_NUMBER, i64::from(target.wid)),
                (FIELD_WINDOW_CONTEXT, context),
                (FIELD_WINDOW_UNDER_POINTER, i64::from(target.wid)),
                (
                    FIELD_WINDOW_UNDER_POINTER_THAT_CAN_HANDLE,
                    i64::from(target.wid),
                ),
            ],
        );
        spi.set_window_location(&press, -1.0, -1.0);
        spi.post_routed(target.pid, &press);
    }
    Ok(())
}

/// Waits until the target is its app's key window.
pub(super) fn await_key_window(spi: &Spi, target: &Target<'_>) -> Result<(), Error> {
    if guard::wait_for(KEY_WINDOW_TIMEOUT, POLL, || {
        ax::focused_window_id(spi, target.pid) == Some(target.wid)
    }) {
        return Ok(());
    }
    Err(unavailable(format!(
        "window {} did not become {}'s key window, so background keys could not be shown to \
         reach it",
        target.wid, target.window.app
    )))
}

/// Posts `presses` through `post`, running `check` before every key down;
/// a key that went down is always released, even when a check stops the
/// rest.
fn post_presses(
    source: &Source,
    presses: &[Press],
    mut check: impl FnMut(Sent) -> Result<(), Error>,
    post: impl Fn(&Event),
) -> Result<(), Error> {
    let mut held: Vec<u16> = Vec::new();
    let mut sent = Sent::Nothing;
    for press in presses {
        if press.edge == Edge::Down {
            if let Err(error) = check(sent) {
                release(source, &held, &post);
                return Err(error);
            }
        }
        let event = match tagged(Event::key(source, press.code, press.edge == Edge::Down)) {
            Ok(event) => event,
            Err(error) => {
                release(source, &held, &post);
                return Err(match sent {
                    Sent::Nothing => error,
                    Sent::Some => input_failed("Quartz stopped creating key events"),
                });
            }
        };
        event.set_flags(press.flags);
        if let Some(text) = press.text {
            let mut buffer = [0u8; 4];
            event.set_text(text.encode_utf8(&mut buffer));
        }
        post(&event);
        sent = Sent::Some;
        match press.edge {
            Edge::Down => held.push(press.code),
            Edge::Up => held.retain(|code| *code != press.code),
        }
        thread::sleep(KEY_GAP);
    }
    Ok(())
}

fn release(source: &Source, held: &[u16], post: &impl Fn(&Event)) {
    for code in held.iter().rev() {
        if let Ok(event) = tagged(Event::key(source, *code, false)) {
            post(&event);
        }
    }
}

/// Background keys into the target window, or `element` in it: makes the
/// window key inside its app, focuses the element, then posts each key to
/// the process once the window still holds the keyboard.
pub(super) fn background_keys(
    spi: &Spi,
    source: &Source,
    target: &Target<'_>,
    element: Option<&AxHandle>,
    presses: &[Press],
    delivery: &Delivery<'_>,
) -> Result<(), Error> {
    if !spi.background_input() {
        return Err(unavailable("the SkyLight input routes are unavailable"));
    }
    let app = target.window.app.as_str();
    guard::watch(spi, target.pid, |visit| {
        delivery.before_press(Sent::Nothing)?;
        guard::still_behind(spi, target.pid, app, visit, Sent::Nothing)?;
        make_key(spi, source, target, Purpose::Keyboard)?;
        await_key_window(spi, target)?;
        if let Some(element) = element {
            focus(element, target.pid)?;
        }
        post_presses(
            source,
            presses,
            |sent| {
                delivery.before_press(sent)?;
                guard::still_behind(spi, target.pid, app, visit, sent)?;
                keys_still_reach(spi, target, sent)
            },
            |event| {
                spi.post_keyboard(target.pid, event);
            },
        )
    })
}

/// Before each key: the target is still its app's key window.
fn keys_still_reach(spi: &Spi, target: &Target<'_>, sent: Sent) -> Result<(), Error> {
    if ax::focused_window_id(spi, target.pid) == Some(target.wid) {
        return Ok(());
    }
    let detail = format!(
        "keyboard focus left window {} during background input",
        target.wid
    );
    Err(match sent {
        Sent::Nothing => unavailable(detail),
        Sent::Some => input_failed(detail),
    })
}

/// Gives `element` keyboard focus in its app, waiting until the app says
/// it has it.
pub(super) fn focus(element: &AxHandle, pid: i32) -> Result<(), Error> {
    match element.write_bool("AXFocused", true) {
        Ok(()) | Err(AxCode::CannotComplete) => {}
        Err(code) => return Err(ax::refused(code, "focusing the element")),
    }
    if guard::wait_for(ELEMENT_FOCUS_TIMEOUT, POLL, || {
        ax::focused_element(pid).as_ref() == Some(element)
    }) {
        return Ok(());
    }
    Err(unavailable(
        "the element did not take keyboard focus, so keys could not be shown to reach it",
    ))
}

/// Whether AX insertion took the text.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum Insertion {
    Inserted,
    /// The element takes no insertion; nothing was written.
    NotTaken,
}

/// Roles whose selection takes typed text.
fn takes_text(role: &str) -> bool {
    matches!(role, "AXTextField" | "AXTextArea" | "AXComboBox")
}

/// Inserts `text` at `element`'s selection through `AXSelectedText`, the
/// way typing inserts it, then reads the value back.
pub(super) fn insert(
    element: &AxHandle,
    text: &str,
    before_write: impl FnOnce() -> Result<(), Error>,
) -> Result<Insertion, Error> {
    let role = ax::native_role(element)?;
    if !takes_text(&role) || element.settable("AXSelectedText") != Ok(true) {
        return Ok(Insertion::NotTaken);
    }
    let Ok(Some(Value::Text(before))) = element.read("AXValue") else {
        return Ok(Insertion::NotTaken);
    };
    let Ok(Some(Value::Range { location, length })) = element.read("AXSelectedTextRange") else {
        return Ok(Insertion::NotTaken);
    };
    let Some(expected) = replace_utf16(&before, location, length, text) else {
        return Ok(Insertion::NotTaken);
    };
    before_write()?;
    element
        .write_text("AXSelectedText", text)
        .map_err(|code| ax::after_send(code, "inserting the text"))?;
    match element.read("AXValue") {
        Ok(Some(Value::Text(after))) if after == expected => Ok(Insertion::Inserted),
        Ok(_) | Err(_) => Err(Error::Unverified(Unverified::AxUnconfirmed {
            detail: "the text was inserted, but the field does not read as expected after it"
                .into(),
        })),
    }
}

/// `before` with UTF-16 units `[location, location + length)` replaced by
/// `text`; `None` when the range is outside it or splits a character.
pub(super) fn replace_utf16(
    before: &str,
    location: i64,
    length: i64,
    text: &str,
) -> Option<String> {
    let start = usize::try_from(location).ok()?;
    let end = start.checked_add(usize::try_from(length).ok()?)?;
    let byte = |units: usize| -> Option<usize> {
        let mut counted = 0;
        for (index, character) in before.char_indices() {
            if counted == units {
                return Some(index);
            }
            counted += character.len_utf16();
            if counted > units {
                return None;
            }
        }
        (counted == units).then_some(before.len())
    };
    let (start, end) = (byte(start)?, byte(end)?);
    let mut replaced = String::with_capacity(before.len() - (end - start) + text.len());
    replaced.push_str(&before[..start]);
    replaced.push_str(text);
    replaced.push_str(&before[end..]);
    Some(replaced)
}

/// Background pointer input to the target window: a left click makes the
/// window key first; every event goes to the window's process with the
/// window-routing fields, never moving the user's pointer.
pub(super) fn background_pointer(
    spi: &Spi,
    source: &Source,
    target: &Target<'_>,
    event: &PointerEvent,
    delivery: &Delivery<'_>,
) -> Result<(), Error> {
    if !spi.background_input() {
        return Err(unavailable("the SkyLight input routes are unavailable"));
    }
    let app = target.window.app.as_str();
    guard::watch(spi, target.pid, |visit| {
        delivery.before_press(Sent::Nothing)?;
        guard::still_behind(spi, target.pid, app, visit, Sent::Nothing)?;
        let check = |sent| {
            delivery.before_press(sent)?;
            guard::still_behind(spi, target.pid, app, visit, sent)
        };
        match *event {
            PointerEvent::Click {
                at,
                button: MouseButton::Left,
                count,
                modifiers,
            } => {
                make_key(spi, source, target, Purpose::Pointer)?;
                left_click(
                    spi,
                    source,
                    target,
                    (at.x, at.y),
                    count.get(),
                    modifier_flags(modifiers),
                    check,
                )
            }
            PointerEvent::Click {
                at,
                button,
                count,
                modifiers,
            } => button_click(
                spi,
                source,
                target,
                (at.x, at.y),
                button,
                count.get(),
                modifier_flags(modifiers),
                check,
            ),
            PointerEvent::Scroll { at, delta } => {
                hover(spi, source, target, at.x, at.y)?;
                thread::sleep(Duration::from_millis(12));
                check(Sent::Some)?;
                let event = tagged(Event::scroll(
                    source,
                    delta.dy.saturating_neg(),
                    delta.dx.saturating_neg(),
                ))?;
                event.set_location(at.x, at.y);
                route(spi, target, &event, at.x, at.y);
                spi.post_pointer(target.pid, &event);
                Ok(())
            }
        }
    })
}

/// Stamps the window-routing fields on a background pointer event.
fn route(spi: &Spi, target: &Target<'_>, event: &Event, x: f64, y: f64) {
    spi.set_fields(
        event,
        &[
            (FIELD_SUBTYPE, SUBTYPE_TOUCH),
            (FIELD_TARGET_PID, i64::from(target.pid)),
            (FIELD_WINDOW_NUMBER, i64::from(target.wid)),
            (FIELD_WINDOW_UNDER_POINTER, i64::from(target.wid)),
            (
                FIELD_WINDOW_UNDER_POINTER_THAT_CAN_HANDLE,
                i64::from(target.wid),
            ),
        ],
    );
    let (local_x, local_y) = target.local(x, y);
    spi.set_window_location(event, local_x, local_y);
    event.stamp_now();
}

/// Moves the window's idea of the pointer to `(x, y)`.
fn hover(spi: &Spi, source: &Source, target: &Target<'_>, x: f64, y: f64) -> Result<(), Error> {
    let event = tagged(Event::mouse(source, MOUSE_MOVED, x, y, 0))?;
    route(spi, target, &event, x, y);
    spi.post_pointer(target.pid, &event);
    Ok(())
}

/// A background left click: a hover, a press and release outside every
/// view that satisfies Chromium's user-activation gate, then the presses.
fn left_click(
    spi: &Spi,
    source: &Source,
    target: &Target<'_>,
    (x, y): (f64, f64),
    count: u8,
    flags: u64,
    check: impl Fn(Sent) -> Result<(), Error>,
) -> Result<(), Error> {
    let post = |kind: u32, (x, y): (f64, f64), local: (f64, f64), phase: i64, state: i64, flags| {
        let event = tagged(Event::mouse(source, kind, x, y, 0))?;
        event.set_flags(flags);
        spi.set_fields(
            &event,
            &[
                (FIELD_MOUSE_EVENT_NUMBER, phase),
                (FIELD_CLICK_STATE, state),
                (FIELD_BUTTON_NUMBER, 0),
                (FIELD_SUBTYPE, SUBTYPE_TOUCH),
                (FIELD_TARGET_PID, i64::from(target.pid)),
                (FIELD_WINDOW_NUMBER, i64::from(target.wid)),
                (FIELD_WINDOW_UNDER_POINTER, i64::from(target.wid)),
                (
                    FIELD_WINDOW_UNDER_POINTER_THAT_CAN_HANDLE,
                    i64::from(target.wid),
                ),
            ],
        );
        spi.set_window_location(&event, local.0, local.1);
        event.stamp_now();
        spi.post_routed(target.pid, &event);
        Ok::<(), Error>(())
    };
    let at = (x, y);
    let local = target.local(x, y);
    let outside = (-1.0, -1.0);
    post(MOUSE_MOVED, at, local, 2, 0, flags)?;
    thread::sleep(Duration::from_millis(15));
    check(Sent::Some)?;
    post(1, outside, outside, 1, 1, 0)?;
    thread::sleep(Duration::from_millis(1));
    post(2, outside, outside, 2, 1, 0)?;
    thread::sleep(Duration::from_millis(100));
    for state in 1..=count.max(1) {
        check(Sent::Some)?;
        post(1, at, local, 3, i64::from(state), flags)?;
        thread::sleep(Duration::from_millis(1));
        post(2, at, local, 3, i64::from(state), flags)?;
        if state < count {
            thread::sleep(MULTI_CLICK_GAP);
        }
    }
    Ok(())
}

/// The CG button number and its down and up event types.
const fn button_types(button: MouseButton) -> (u32, u32, u32) {
    match button {
        MouseButton::Left => (0, 1, 2),
        MouseButton::Right => (1, 3, 4),
        MouseButton::Middle => (2, 25, 26),
    }
}

#[allow(
    clippy::too_many_arguments,
    reason = "the parts of one click, passed explicitly"
)]
fn button_click(
    spi: &Spi,
    source: &Source,
    target: &Target<'_>,
    (x, y): (f64, f64),
    button: MouseButton,
    count: u8,
    flags: u64,
    check: impl Fn(Sent) -> Result<(), Error>,
) -> Result<(), Error> {
    let (number, down, up) = button_types(button);
    check(Sent::Nothing)?;
    hover(spi, source, target, x, y)?;
    thread::sleep(Duration::from_millis(12));
    for state in 1..=count.max(1) {
        check(Sent::Some)?;
        for kind in [down, up] {
            let event = tagged(Event::mouse(source, kind, x, y, number))?;
            event.set_flags(flags);
            spi.set_fields(
                &event,
                &[
                    (FIELD_CLICK_STATE, i64::from(state)),
                    (FIELD_BUTTON_NUMBER, i64::from(number)),
                ],
            );
            route(spi, target, &event, x, y);
            spi.post_pointer(target.pid, &event);
            if kind == down {
                thread::sleep(PRESS_GAP);
            }
        }
        if state < count {
            thread::sleep(MULTI_CLICK_GAP);
        }
    }
    Ok(())
}

/// The user's front app and key window, put back after a takeover.
struct Handback {
    previous: Option<(Psn, Option<i32>)>,
    key: Option<u32>,
}

/// A takeover in progress: the target window is in front and key.
pub(super) struct Foreground<'a> {
    spi: &'a Spi,
    target: &'a Target<'a>,
    delivery: &'a Delivery<'a>,
}

impl Foreground<'_> {
    fn in_front(&self) -> bool {
        self.spi.front_process().and_then(|(_, pid)| pid) == Some(self.target.pid)
            && ax::focused_window_id(self.spi, self.target.pid) == Some(self.target.wid)
    }

    /// Before each press: no cancel or user input, and the target still in
    /// front, so input never follows the user into a window they picked.
    pub(super) fn check(&self, sent: Sent) -> Result<(), Error> {
        self.delivery.before_press(sent)?;
        if self.in_front() {
            return Ok(());
        }
        let detail = format!(
            "window {} left the front during the takeover",
            self.target.wid
        );
        Err(match sent {
            Sent::Nothing => Error::Refused(Refusal::Platform {
                detail: detail.into(),
            }),
            Sent::Some => input_failed(detail),
        })
    }
}

/// Runs `input` with the target window in front and key, then hands focus
/// back to the user's app and the pointer back to where it was.
pub(super) fn takeover<'a, T>(
    spi: &'a Spi,
    target: &'a Target<'a>,
    delivery: &'a Delivery<'a>,
    input: impl FnOnce(&Foreground<'a>) -> Result<T, Error>,
) -> Result<T, Error> {
    let psn = spi.psn_of(target.pid).ok_or_else(|| {
        Error::Refused(Refusal::Platform {
            detail: format!("{} has no process serial number", target.window.app).into(),
        })
    })?;
    let previous = spi.front_process();
    let handback = Handback {
        previous,
        key: previous
            .and_then(|(_, pid)| pid)
            .and_then(|pid| ax::focused_window_id(spi, pid)),
    };
    delivery.before_press(Sent::Nothing)?;
    spi.set_front(psn, target.wid, CPS_USER_GENERATED);
    spi.make_key(psn, target.wid);
    let foreground = Foreground {
        spi,
        target,
        delivery,
    };
    if !guard::wait_for(ACTIVATION_TIMEOUT, POLL, || foreground.in_front()) {
        hand_back(spi, target, &handback);
        return Err(Error::Refused(Refusal::Platform {
            detail: format!(
                "window {} of {} did not come in front for the takeover",
                target.wid, target.window.app
            )
            .into(),
        }));
    }
    let pointer = quartz::pointer();
    let result = input(&foreground);
    thread::sleep(FOREGROUND_SETTLE);
    if let Some((x, y)) = pointer {
        quartz::warp_pointer(x, y);
    }
    hand_back(spi, target, &handback);
    result
}

fn hand_back(spi: &Spi, target: &Target<'_>, handback: &Handback) {
    let Some((psn, pid)) = handback.previous else {
        return;
    };
    if pid == Some(target.pid) {
        return;
    }
    // A refused hand-back leaves the target in front; the user's next
    // click takes them back, and the step's own outcome stands.
    spi.set_front(psn, handback.key.unwrap_or(0), CPS_NO_WINDOWS);
    if let Some(key) = handback.key {
        spi.make_key(psn, key);
    }
}

/// Keys at the HID tap, for a takeover.
pub(super) fn foreground_keys(
    source: &Source,
    presses: &[Press],
    foreground: &Foreground<'_>,
) -> Result<(), Error> {
    post_presses(
        source,
        presses,
        |sent| foreground.check(sent),
        Event::post_hid,
    )
}

/// Pointer input at the HID tap, for a takeover: it moves the real pointer.
pub(super) fn foreground_pointer(
    source: &Source,
    event: &PointerEvent,
    foreground: &Foreground<'_>,
) -> Result<(), Error> {
    match *event {
        PointerEvent::Click {
            at,
            button,
            count,
            modifiers,
        } => {
            let (number, down, up) = button_types(button);
            let flags = modifier_flags(modifiers);
            foreground.check(Sent::Nothing)?;
            tagged(Event::mouse(source, MOUSE_MOVED, at.x, at.y, number))?.post_hid();
            thread::sleep(Duration::from_millis(12));
            for state in 1..=count.get() {
                foreground.check(Sent::Some)?;
                for kind in [down, up] {
                    let event = tagged(Event::mouse(source, kind, at.x, at.y, number))?;
                    event.set_flags(flags);
                    event.set_field(FIELD_CLICK_STATE, i64::from(state));
                    event.post_hid();
                    if kind == down {
                        thread::sleep(PRESS_GAP);
                    }
                }
                if state < count.get() {
                    thread::sleep(MULTI_CLICK_GAP);
                }
            }
            Ok(())
        }
        PointerEvent::Scroll { at, delta } => {
            foreground.check(Sent::Nothing)?;
            tagged(Event::mouse(source, MOUSE_MOVED, at.x, at.y, 0))?.post_hid();
            thread::sleep(Duration::from_millis(12));
            foreground.check(Sent::Some)?;
            let event = tagged(Event::scroll(
                source,
                delta.dy.saturating_neg(),
                delta.dx.saturating_neg(),
            ))?;
            event.set_type(SCROLL_WHEEL);
            event.set_location(at.x, at.y);
            event.post_hid();
            Ok(())
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn insertion_replaces_the_selection_in_utf16_units() {
        assert_eq!(replace_utf16("héllo", 1, 1, "e").as_deref(), Some("hello"));
        assert_eq!(replace_utf16("ab", 2, 0, "c").as_deref(), Some("abc"));
        // 😀 is two UTF-16 units: a range that splits it is refused.
        assert_eq!(replace_utf16("😀x", 1, 0, "y"), None);
        assert_eq!(replace_utf16("😀x", 2, 1, "y").as_deref(), Some("😀y"));
        assert_eq!(replace_utf16("ab", 3, 0, "c"), None);
    }

    #[test]
    fn modifiers_map_to_quartz_flags() {
        let held = Modifiers::NONE.with(Modifier::Meta).with(Modifier::Shift);
        assert_eq!(modifier_flags(held), 0x0012_0000);
        assert_eq!(modifier_flags(Modifiers::NONE), 0);
    }
}
