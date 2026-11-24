//! The private `SkyLight` routes background input posts through, and the
//! front-process calls the focus guard and takeover use (port of omp
//! `crates/natives/src/desktop/macos/route.rs` and `skylight.rs`).

use std::ffi::c_void;
use std::ptr;

use objc2::runtime::{AnyClass, AnyObject, Sel};
use objc2::{msg_send, sel};
use objc2_core_foundation::{CFDictionary, CFNumber, CFString, CGPoint};
use objc2_core_graphics::CGEvent;

use super::ax::WindowIdFn;
use super::quartz::Event;
use super::symbol;

/// A Carbon process serial number, as `SkyLight` names processes.
#[repr(C)]
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub(crate) struct Psn {
    high: u32,
    low: u32,
}

#[cfg(test)]
impl Psn {
    pub(crate) const fn for_test(low: u32) -> Self {
        Self { high: 0, low }
    }
}

type PostToPidFn = unsafe extern "C" fn(i32, *mut c_void);
type SetIntegerFieldFn = unsafe extern "C" fn(*mut c_void, u32, i64);
type SetWindowLocationFn = unsafe extern "C" fn(*mut c_void, CGPoint);
type SetAuthenticationFn = unsafe extern "C" fn(*mut c_void, *mut AnyObject);
type MainConnectionFn = unsafe extern "C" fn() -> u32;
type GetFrontFn = unsafe extern "C" fn(*mut Psn) -> i32;
type SetFrontFn = unsafe extern "C" fn(*const Psn, u32, u32) -> i32;
type SetFrontWithInfoFn = unsafe extern "C" fn(*const Psn, u32, u32, *const c_void) -> i32;
type PostRecordFn = unsafe extern "C" fn(*const Psn, *const u8) -> i32;
type ProcessForPidFn = unsafe extern "C" fn(i32, *mut Psn) -> i32;
type ProcessPidFn = unsafe extern "C" fn(*const Psn, *mut i32) -> i32;

/// What background input posts through: the per-process routes.
#[derive(Clone, Copy)]
struct Routes {
    post_to_pid: PostToPidFn,
    /// `CGEventPostToPid` when it is a separate function; where it re-exports
    /// `SLEventPostToPid` a second post would deliver every event twice.
    public_post_to_pid: Option<PostToPidFn>,
    set_integer: SetIntegerFieldFn,
    set_window_location: SetWindowLocationFn,
    main_connection: MainConnectionFn,
    /// Authenticates keyboard events so `AppKit` and Chromium take them.
    authenticate: Option<SetAuthenticationFn>,
}

/// The front-process calls.
#[derive(Clone, Copy)]
struct Front {
    get: GetFrontFn,
    set: SetFrontFn,
    post_record: PostRecordFn,
    process_for_pid: ProcessForPidFn,
    process_pid: ProcessPidFn,
    /// The request `WindowServer` refuses once the user acted after it.
    conditional: Option<(SetFrontWithInfoFn, TimestampKey)>,
}

/// `kSLSSetFrontProcessRequestTimestampKey`.
#[derive(Clone, Copy)]
struct TimestampKey(&'static CFString);

// SAFETY: an immutable CFString constant SkyLight owns for the process;
// nothing mutates it, and CF strings are safe to read from any thread.
unsafe impl Send for TimestampKey {}
// SAFETY: as above.
unsafe impl Sync for TimestampKey {}

/// The private symbols this backend uses, resolved once when it opens.
pub(crate) struct Spi {
    routes: Option<Routes>,
    front: Option<Front>,
    window_id: Option<WindowIdFn>,
}

/// What a front-process request did.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum FrontRequest {
    Done,
    /// `WindowServer` refused it: the user pressed or clicked after it began.
    UserActed,
    Rejected,
}

/// `kCPSUserGenerated`: lets `AppKit` install the requested key window.
pub(crate) const CPS_USER_GENERATED: u32 = 0x200;
/// `kCPSNoWindows`: changes the front process without raising windows.
pub(crate) const CPS_NO_WINDOWS: u32 = 0x400;
/// `SLSSetFrontProcessWithInfo`'s answer when the user acted after the
/// request's timestamp.
const EXPIRED_FRONT_REQUEST: i32 = -13066;
const EVENT_RECORD_LENGTH: usize = 248;
const WINDOW_ID_OFFSET: usize = 0x3c;

/// Casts a resolved symbol to its function type.
macro_rules! resolve {
    ($name:literal as $ty:ty) => {
        symbol($name).map(|raw| {
            // SAFETY: every call site names the symbol's exact C ABI.
            unsafe { std::mem::transmute::<*mut c_void, $ty>(raw) }
        })
    };
}

impl Spi {
    /// Loads `SkyLight` and resolves every symbol; missing ones leave their
    /// route off, which the backend reports as unavailable.
    pub(crate) fn load() -> Self {
        let path = c"/System/Library/PrivateFrameworks/SkyLight.framework/SkyLight";
        // SAFETY: a static NUL-terminated path; the handle lives for the
        // process, as frameworks do.
        let loaded =
            !unsafe { libc::dlopen(path.as_ptr(), libc::RTLD_NOW | libc::RTLD_GLOBAL) }.is_null();
        Self {
            routes: loaded.then(routes).flatten(),
            front: loaded.then(front).flatten(),
            window_id: resolve!(c"_AXUIElementGetWindow" as WindowIdFn),
        }
    }

    pub(crate) fn background_input(&self) -> bool {
        self.routes.is_some() && self.front.is_some()
    }

    pub(crate) fn takeover(&self) -> bool {
        self.front.is_some()
    }

    pub(crate) fn window_id_fn(&self) -> Option<WindowIdFn> {
        self.window_id
    }

    /// The front process and its pid.
    pub(crate) fn front_process(&self) -> Option<(Psn, Option<i32>)> {
        let front = self.front?;
        let mut psn = Psn::default();
        // SAFETY: `psn` is the writable 8-byte record the call fills.
        if unsafe { (front.get)(&raw mut psn) } != 0 {
            return None;
        }
        Some((psn, pid_of(front, psn)))
    }

    pub(crate) fn psn_of(&self, pid: i32) -> Option<Psn> {
        let front = self.front?;
        let mut psn = Psn::default();
        // SAFETY: `psn` is writable for the synchronous lookup.
        (unsafe { (front.process_for_pid)(pid, &raw mut psn) } == 0).then_some(psn)
    }

    /// Brings `psn` in front with `wid` as its key window under `options`.
    pub(crate) fn set_front(&self, psn: Psn, wid: u32, options: u32) -> FrontRequest {
        let Some(front) = self.front else {
            return FrontRequest::Rejected;
        };
        // SAFETY: `psn` lives through the synchronous call.
        match unsafe { (front.set)(&raw const psn, wid, options) } {
            0 => FrontRequest::Done,
            _ => FrontRequest::Rejected,
        }
    }

    /// [`Self::set_front`] that `WindowServer` refuses once the user pressed a
    /// key or clicked after `since` (uptime nanoseconds).
    pub(crate) fn set_front_unless_user_acted(
        &self,
        psn: Psn,
        wid: u32,
        options: u32,
        since: u64,
    ) -> FrontRequest {
        let Some((set_front, key)) = self.front.and_then(|front| front.conditional) else {
            return self.set_front(psn, wid, options);
        };
        let stamp = CFNumber::new_i64(i64::try_from(since).unwrap_or(i64::MAX));
        let info = CFDictionary::<CFString, CFNumber>::from_slices(&[key.0], &[&*stamp]);
        let info: *const CFDictionary<CFString, CFNumber> = &raw const *info;
        // SAFETY: `psn` and `info` live through the synchronous call.
        match unsafe { set_front(&raw const psn, wid, options, info.cast()) } {
            0 => FrontRequest::Done,
            EXPIRED_FRONT_REQUEST => FrontRequest::UserActed,
            _ => FrontRequest::Rejected,
        }
    }

    /// Posts the paired records that make `wid` the key window of `psn`.
    pub(crate) fn make_key(&self, psn: Psn, wid: u32) -> bool {
        let Some(front) = self.front else {
            return false;
        };
        [0x01, 0x02].into_iter().all(|kind| {
            let record = make_key_record(wid, kind);
            // SAFETY: the PSN and the whole 248-byte record live through the
            // synchronous call.
            unsafe { (front.post_record)(&raw const psn, record.as_ptr()) == 0 }
        })
    }

    /// This process's `WindowServer` connection, stamped on window events.
    pub(crate) fn connection(&self) -> Option<i64> {
        let routes = self.routes?;
        // SAFETY: the no-argument query has this exact signature.
        Some(i64::from(unsafe { (routes.main_connection)() }))
    }

    /// Stamps raw `SkyLight` integer fields on `event`.
    pub(crate) fn set_fields(&self, event: &Event, fields: &[(u32, i64)]) -> bool {
        let Some(routes) = self.routes else {
            return false;
        };
        for &(field, value) in fields {
            // SAFETY: the event is alive for the call.
            unsafe { (routes.set_integer)(event_pointer(event), field, value) };
        }
        true
    }

    /// Stamps the window-local point a pid-addressed pointer event hits.
    pub(crate) fn set_window_location(&self, event: &Event, x: f64, y: f64) -> bool {
        let Some(routes) = self.routes else {
            return false;
        };
        // SAFETY: the event is alive for the call.
        unsafe { (routes.set_window_location)(event_pointer(event), CGPoint { x, y }) };
        true
    }

    /// Posts a pointer event to `pid` through `SkyLight` and, where it is a
    /// separate function, the public per-process queue.
    pub(crate) fn post_pointer(&self, pid: i32, event: &Event) -> bool {
        let Some(routes) = self.routes else {
            return false;
        };
        // SAFETY: the event is alive for both synchronous posts.
        unsafe {
            (routes.post_to_pid)(pid, event_pointer(event));
            if let Some(public) = routes.public_post_to_pid {
                public(pid, event_pointer(event));
            }
        }
        true
    }

    /// Posts an event that only makes a window key, through `SkyLight` alone.
    pub(crate) fn post_routed(&self, pid: i32, event: &Event) -> bool {
        let Some(routes) = self.routes else {
            return false;
        };
        // SAFETY: the event is alive for the synchronous post.
        unsafe { (routes.post_to_pid)(pid, event_pointer(event)) };
        true
    }

    /// Posts a keyboard event to `pid` on the authenticated `SkyLight` route.
    pub(crate) fn post_keyboard(&self, pid: i32, event: &Event) -> bool {
        let Some(routes) = self.routes else {
            return false;
        };
        if let Some(set) = routes.authenticate {
            authenticate(set, pid, event);
        }
        // SAFETY: the event is alive for the synchronous post.
        unsafe { (routes.post_to_pid)(pid, event_pointer(event)) };
        true
    }
}

fn routes() -> Option<Routes> {
    let post_to_pid = resolve!(c"SLEventPostToPid" as PostToPidFn)?;
    Some(Routes {
        post_to_pid,
        public_post_to_pid: resolve!(c"CGEventPostToPid" as PostToPidFn)
            .filter(|public| *public as usize != post_to_pid as usize),
        set_integer: resolve!(c"SLEventSetIntegerValueField" as SetIntegerFieldFn)?,
        set_window_location: resolve!(c"CGEventSetWindowLocation" as SetWindowLocationFn)?,
        main_connection: resolve!(c"CGSMainConnectionID" as MainConnectionFn)?,
        authenticate: resolve!(c"SLEventSetAuthenticationMessage" as SetAuthenticationFn),
    })
}

fn front() -> Option<Front> {
    Some(Front {
        get: resolve!(c"_SLPSGetFrontProcess" as GetFrontFn)?,
        set: resolve!(c"_SLPSSetFrontProcessWithOptions" as SetFrontFn)?,
        post_record: resolve!(c"SLPSPostEventRecordTo" as PostRecordFn)?,
        process_for_pid: resolve!(c"GetProcessForPID" as ProcessForPidFn)?,
        process_pid: resolve!(c"GetProcessPID" as ProcessPidFn)?,
        conditional: conditional(),
    })
}

fn conditional() -> Option<(SetFrontWithInfoFn, TimestampKey)> {
    let set = resolve!(c"SLSSetFrontProcessWithInfo" as SetFrontWithInfoFn)?;
    let key = symbol(c"kSLSSetFrontProcessRequestTimestampKey")?;
    // SAFETY: the export is a `CFStringRef` variable `SkyLight` initializes
    // before any of its functions runs; the string lives for the process.
    let key = unsafe { key.cast::<*const CFString>().read().as_ref() }?;
    Some((set, TimestampKey(key)))
}

fn pid_of(front: Front, psn: Psn) -> Option<i32> {
    let mut pid = 0;
    // SAFETY: both pointers are valid for the synchronous lookup.
    (unsafe { (front.process_pid)(&raw const psn, &raw mut pid) } == 0 && pid > 0).then_some(pid)
}

fn make_key_record(wid: u32, kind: u8) -> [u8; EVENT_RECORD_LENGTH] {
    let mut record = [0u8; EVENT_RECORD_LENGTH];
    record[0x04] = 0xf8;
    record[0x08] = kind;
    record[0x20..0x30].fill(0xff);
    record[0x3a] = 0x10;
    record[WINDOW_ID_OFFSET..WINDOW_ID_OFFSET + 4].copy_from_slice(&wid.to_le_bytes());
    record
}

fn event_pointer(event: &Event) -> *mut c_void {
    let event: *const CGEvent = event.raw();
    event.cast_mut().cast()
}

/// Attaches `SkyLight`'s authentication message, on macOS 15 and later, so
/// `AppKit` and Chromium take a pid-posted keyboard event.
fn authenticate(set: SetAuthenticationFn, pid: i32, event: &Event) {
    let Some(class) = AnyClass::get(c"SLSEventAuthenticationMessage") else {
        return;
    };
    let selector: Sel = sel!(messageWithEventRecord:pid:version:);
    if !class.responds_to(selector) {
        return;
    }
    let pointer = event_pointer(event);
    // __CGEvent keeps its SLSEventRecord pointer after CFRuntimeBase and a
    // padded u32; these are the known slots.
    let record = [24usize, 32, 16].into_iter().find_map(|offset| {
        // SAFETY: pointer-aligned slots inside the live __CGEvent; the read
        // is unaligned-safe and copies a pointer value only.
        let candidate =
            unsafe { ptr::read_unaligned(pointer.cast::<u8>().add(offset).cast::<*mut c_void>()) };
        (!candidate.is_null()).then_some(candidate)
    });
    let Some(record) = record else {
        return;
    };
    // SAFETY: the class answers this factory selector (checked above), whose
    // arguments are the event record pointer, a pid and a version.
    let message: *mut AnyObject =
        unsafe { msg_send![class, messageWithEventRecord: record, pid: pid, version: 0u32] };
    if message.is_null() {
        return;
    }
    // SAFETY: the event and the autoreleased message are alive for the
    // synchronous attachment.
    unsafe { set(pointer, message) };
}
