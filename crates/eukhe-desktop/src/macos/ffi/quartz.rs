//! Quartz: the window list, input events and the HID state, the login
//! session and privacy preflights (port of the Quartz calls of omp
//! `crates/natives/src/desktop/macos/capture.rs`, `input.rs`, `session.rs`
//! and `permission.rs`).

use std::time::Duration;

use objc2_core_foundation::{
    CFArray, CFBoolean, CFDictionary, CFNumber, CFRetained, CFString, CFType, CGPoint, CGRect,
};
use objc2_core_graphics::{
    kCGWindowAlpha, kCGWindowBounds, kCGWindowIsOnscreen, kCGWindowLayer, kCGWindowName,
    kCGWindowNumber, kCGWindowOwnerName, kCGWindowOwnerPID, kCGWindowSharingState,
    CGDisplayIsAsleep, CGEvent, CGEventField, CGEventFlags, CGEventSource, CGEventSourceStateID,
    CGEventTapLocation, CGEventType, CGMainDisplayID, CGMouseButton, CGPreflightListenEventAccess,
    CGPreflightPostEventAccess, CGPreflightScreenCaptureAccess,
    CGRectMakeWithDictionaryRepresentation, CGScrollEventUnit, CGSessionCopyCurrentDictionary,
    CGWarpMouseCursorPosition, CGWindowListCopyWindowInfo, CGWindowListOption,
};

/// A rectangle in global logical points.
#[derive(Clone, Copy, Debug, PartialEq)]
pub(crate) struct Rect {
    pub(crate) x: f64,
    pub(crate) y: f64,
    pub(crate) width: f64,
    pub(crate) height: f64,
}

/// One window as the window server lists it.
#[derive(Clone, Debug, PartialEq)]
pub(crate) struct WindowRecord {
    pub(crate) id: u32,
    pub(crate) pid: i32,
    pub(crate) layer: i32,
    pub(crate) alpha: f64,
    pub(crate) onscreen: bool,
    /// `kCGWindowSharingState`; 0 is a window capture never sees.
    pub(crate) sharing: Option<i64>,
    pub(crate) bounds: Rect,
    /// Empty without Screen Recording for other apps' windows.
    pub(crate) title: String,
    pub(crate) owner: String,
}

/// The on-screen windows, front to back; `None` when the list fails.
pub(crate) fn window_list() -> Option<Vec<WindowRecord>> {
    records(
        CGWindowListOption::OptionOnScreenOnly | CGWindowListOption::ExcludeDesktopElements,
        0,
    )
}

fn records(options: CGWindowListOption, relative: u32) -> Option<Vec<WindowRecord>> {
    let list = CGWindowListCopyWindowInfo(options, relative)?;
    // SAFETY: the window list is an immutable array of dictionaries keyed
    // by CFStrings with CF values.
    let list =
        unsafe { CFRetained::cast_unchecked::<CFArray<CFDictionary<CFString, CFType>>>(list) };
    Some(list.iter().filter_map(|entry| record(&entry)).collect())
}

fn record(entry: &CFDictionary<CFString, CFType>) -> Option<WindowRecord> {
    // SAFETY: the key constants are process-lived CFStrings.
    let keys = unsafe {
        (
            kCGWindowNumber,
            kCGWindowOwnerPID,
            kCGWindowLayer,
            kCGWindowAlpha,
            kCGWindowIsOnscreen,
            kCGWindowSharingState,
            kCGWindowBounds,
            kCGWindowName,
            kCGWindowOwnerName,
        )
    };
    let (number, owner_pid, layer, alpha, onscreen, sharing, bounds, name, owner) = keys;
    Some(WindowRecord {
        id: u32::try_from(integer(entry, number)?).ok()?,
        pid: i32::try_from(integer(entry, owner_pid)?).ok()?,
        layer: i32::try_from(integer(entry, layer).unwrap_or(0)).unwrap_or(0),
        alpha: get(entry, alpha)
            .and_then(|value| value.downcast_ref::<CFNumber>()?.as_f64())
            .unwrap_or(1.0),
        onscreen: get(entry, onscreen)
            .and_then(|value| value.downcast_ref::<CFBoolean>().map(CFBoolean::as_bool))
            .unwrap_or(false),
        sharing: integer(entry, sharing),
        bounds: rect(get(entry, bounds)?)?,
        title: text(entry, name),
        owner: text(entry, owner),
    })
}

fn get<'a>(entry: &'a CFDictionary<CFString, CFType>, key: &CFString) -> Option<&'a CFType> {
    // SAFETY: the list is a copy nobody mutates while it is borrowed.
    unsafe { entry.get_unchecked(key) }
}

fn integer(entry: &CFDictionary<CFString, CFType>, key: &CFString) -> Option<i64> {
    get(entry, key)?.downcast_ref::<CFNumber>()?.as_i64()
}

fn text(entry: &CFDictionary<CFString, CFType>, key: &CFString) -> String {
    get(entry, key)
        .and_then(|value| value.downcast_ref::<CFString>())
        .map(ToString::to_string)
        .unwrap_or_default()
}

fn rect(value: &CFType) -> Option<Rect> {
    let dictionary = value.downcast_ref::<CFDictionary>()?;
    let mut rect = CGRect::default();
    // SAFETY: `rect` is writable for the synchronous decode.
    unsafe { CGRectMakeWithDictionaryRepresentation(Some(dictionary), &raw mut rect) }.then_some(
        Rect {
            x: rect.origin.x,
            y: rect.origin.y,
            width: rect.size.width,
            height: rect.size.height,
        },
    )
}

/// Whether the app running eukhe may capture the screen (no prompt).
pub(crate) fn screen_capture_access() -> bool {
    CGPreflightScreenCaptureAccess()
}

/// Whether posted events reach the event stream (no prompt).
pub(crate) fn post_event_access() -> bool {
    CGPreflightPostEventAccess()
}

/// Whether an event tap sees the user's input (no prompt).
pub(crate) fn listen_event_access() -> bool {
    CGPreflightListenEventAccess()
}

/// The login session as the window server reports it.
pub(crate) struct Session {
    pub(crate) locked: bool,
    /// The process that turned Secure Event Input on, while it is on.
    pub(crate) secure_input: Option<i32>,
}

pub(crate) fn session() -> Session {
    let Some(dictionary) = CGSessionCopyCurrentDictionary() else {
        return Session {
            locked: false,
            secure_input: None,
        };
    };
    // SAFETY: the session dictionary holds CFString keys and CF values.
    let dictionary =
        unsafe { CFRetained::cast_unchecked::<CFDictionary<CFString, CFType>>(dictionary) };
    let locked = get(
        &dictionary,
        &CFString::from_static_str("CGSSessionScreenIsLocked"),
    )
    .and_then(|value| value.downcast_ref::<CFBoolean>().map(CFBoolean::as_bool))
    .unwrap_or(false);
    let secure_input = integer(
        &dictionary,
        &CFString::from_static_str("kCGSSessionSecureInputPID"),
    )
    .and_then(|pid| i32::try_from(pid).ok())
    .filter(|pid| *pid > 0);
    Session {
        locked,
        secure_input,
    }
}

pub(crate) fn display_asleep() -> bool {
    CGDisplayIsAsleep(CGMainDisplayID())
}

/// Time since the user's last key press or click; mouse moves do not count.
pub(crate) fn press_idle() -> Duration {
    // KeyDown, LeftMouseDown, RightMouseDown, OtherMouseDown.
    let seconds = [10, 1, 3, 25]
        .map(|kind| {
            CGEventSource::seconds_since_last_event_type(
                CGEventSourceStateID::HIDSystemState,
                CGEventType(kind),
            )
        })
        .into_iter()
        .fold(f64::INFINITY, f64::min);
    Duration::try_from_secs_f64(seconds).unwrap_or(Duration::MAX)
}

/// How many presses of `kind` the HID system has counted.
pub(crate) fn hid_count(kind: u32) -> u32 {
    CGEventSource::counter_for_event_type(CGEventSourceStateID::HIDSystemState, CGEventType(kind))
}

/// The physical keyboard's modifier flags.
pub(crate) fn hid_flags() -> u64 {
    CGEventSource::flags_state(CGEventSourceStateID::HIDSystemState).bits()
}

pub(crate) fn button_held(button: u32) -> bool {
    CGEventSource::button_state(CGEventSourceStateID::HIDSystemState, CGMouseButton(button))
}

pub(crate) fn key_held(code: u16) -> bool {
    CGEventSource::key_state(CGEventSourceStateID::HIDSystemState, code)
}

/// The pointer's global location.
pub(crate) fn pointer() -> Option<(f64, f64)> {
    let event = CGEvent::new(None)?;
    let point = CGEvent::location(Some(&event));
    Some((point.x, point.y))
}

pub(crate) fn warp_pointer(x: f64, y: f64) {
    // A refused warp leaves the pointer where the takeover left it.
    let _ = CGWarpMouseCursorPosition(CGPoint { x, y });
}

/// An event source on the HID system state.
pub(crate) struct Source(CFRetained<CGEventSource>);

impl Source {
    pub(crate) fn hid() -> Option<Self> {
        CGEventSource::new(CGEventSourceStateID::HIDSystemState).map(Self)
    }
}

/// One Quartz event being built and posted.
pub(crate) struct Event(CFRetained<CGEvent>);

impl Event {
    pub(crate) fn blank(source: &Source) -> Option<Self> {
        CGEvent::new(Some(&source.0)).map(Self)
    }

    /// A pointer event of CG type `kind` at a global point; no modifiers.
    pub(crate) fn mouse(source: &Source, kind: u32, x: f64, y: f64, button: u32) -> Option<Self> {
        let event = CGEvent::new_mouse_event(
            Some(&source.0),
            CGEventType(kind),
            CGPoint { x, y },
            CGMouseButton(button),
        )
        .map(Self)?;
        event.set_flags(0);
        Some(event)
    }

    pub(crate) fn key(source: &Source, code: u16, down: bool) -> Option<Self> {
        let event = CGEvent::new_keyboard_event(Some(&source.0), code, down).map(Self)?;
        event.set_flags(0);
        Some(event)
    }

    /// A wheel event of whole lines; positive values scroll up and left.
    pub(crate) fn scroll(source: &Source, vertical: i32, horizontal: i32) -> Option<Self> {
        CGEvent::new_scroll_wheel_event2(
            Some(&source.0),
            CGScrollEventUnit::Line,
            2,
            vertical,
            horizontal,
            0,
        )
        .map(Self)
    }

    pub(crate) fn set_type(&self, kind: u32) {
        CGEvent::set_type(Some(&self.0), CGEventType(kind));
    }

    pub(crate) fn set_flags(&self, flags: u64) {
        CGEvent::set_flags(Some(&self.0), CGEventFlags::from_bits_retain(flags));
    }

    pub(crate) fn set_field(&self, field: u32, value: i64) {
        CGEvent::set_integer_value_field(Some(&self.0), CGEventField(field), value);
    }

    pub(crate) fn set_location(&self, x: f64, y: f64) {
        CGEvent::set_location(Some(&self.0), CGPoint { x, y });
    }

    /// The text the key types, at most 20 UTF-16 units.
    pub(crate) fn set_text(&self, text: &str) {
        let units: Vec<u16> = text.encode_utf16().collect();
        // SAFETY: `units` is live for the call, which copies it.
        unsafe {
            CGEvent::keyboard_set_unicode_string(Some(&self.0), units.len() as _, units.as_ptr());
        }
    }

    /// Stamps the event with now in uptime nanoseconds: Quartz leaves 0.
    pub(crate) fn stamp_now(&self) {
        CGEvent::set_timestamp(Some(&self.0), super::process::uptime_ns());
    }

    /// Posts at the HID tap, as the user's own devices do.
    pub(crate) fn post_hid(&self) {
        CGEvent::post(CGEventTapLocation::HIDEventTap, Some(&self.0));
    }

    pub(super) fn raw(&self) -> &CGEvent {
        &self.0
    }
}
