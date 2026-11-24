//! The macOS platform boundary: AX, Quartz events and window list, the
//! private `SkyLight` routes, `AppKit`, `ScreenCaptureKit` and event taps. The
//! crate's one macOS module with `unsafe` code; only safe wrappers without
//! raw pointers leave it.
#![allow(
    unsafe_code,
    reason = "the macOS platform APIs: AX, Quartz, SkyLight, AppKit, ScreenCaptureKit"
)]

pub(super) mod appkit;
pub(super) mod ax;
pub(super) mod capture;
pub(super) mod process;
pub(super) mod quartz;
pub(super) mod sky;
pub(super) mod tap;

use std::ffi::{c_void, CStr};

/// `RTLD_DEFAULT` on Darwin.
const RTLD_DEFAULT: *mut c_void = -2isize as *mut c_void;

/// A symbol's address in the loaded images, `None` when absent.
fn symbol(name: &CStr) -> Option<*mut c_void> {
    // SAFETY: `name` is NUL-terminated; RTLD_DEFAULT searches every loaded
    // image and the call keeps no pointer.
    let raw = unsafe { libc::dlsym(RTLD_DEFAULT, name.as_ptr()) };
    (!raw.is_null()).then_some(raw)
}
