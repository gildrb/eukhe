//! The C boundary to the compiled Bend core (`c/shim.c`): the workspace's one
//! module with `unsafe` code.
#![allow(unsafe_code, reason = "the C boundary to the compiled Bend core")]

use std::ffi::c_char;
use std::ptr;

use crate::CallError;

// The pointer-sized lengths below travel as u64 (the shim's ABI).
const _: () = assert!(usize::BITS == u64::BITS, "eukhe-bend needs a 64-bit target");

/// `c/shim.c`'s fault codes.
const EB_ABI: u64 = 1;
const EB_HANDLE: u64 = 2;
const EB_NOMEM: u64 = 3;

extern "C" {
    fn eukhe_bend_call(entry: u32, input: *const c_char, n: u64, out_n: *mut u64) -> *mut c_char;
    fn eukhe_bend_open(
        entry: u32,
        input: *const c_char,
        n: u64,
        out: *mut *mut c_char,
        out_n: *mut u64,
    ) -> u64;
    fn eukhe_bend_step(
        handle: u64,
        input: *const c_char,
        n: u64,
        out: *mut *mut c_char,
        out_n: *mut u64,
    ) -> i32;
    fn eukhe_bend_close(handle: u64);
    fn eukhe_bend_free(text: *mut c_char);
}

fn fault(code: u64) -> CallError {
    match code {
        EB_HANDLE => CallError::StaleHandle,
        EB_NOMEM => CallError::OutOfMemory,
        // EB_ABI, and the codes the shim does not define: out of step.
        0 | EB_ABI | 4..=u64::MAX => CallError::Abi,
    }
}

/// Copies a reply buffer of the shim into a `String` and frees it.
fn take(text: *mut c_char, n: u64) -> Result<String, CallError> {
    #[allow(
        clippy::cast_possible_truncation,
        reason = "usize is 64 bits (the assertion above)"
    )]
    let len = n as usize;
    // SAFETY: the shim answered `text`, non-null, a malloc'd buffer of `n`
    // initialized bytes that nothing else holds; it stays alive until the
    // eukhe_bend_free below.
    let bytes = unsafe { std::slice::from_raw_parts(text.cast::<u8>(), len) }.to_vec();
    // SAFETY: `text` came from the shim and is freed exactly once, here.
    unsafe { eukhe_bend_free(text) };
    String::from_utf8(bytes).map_err(CallError::InvalidUtf8)
}

/// The reply of entry `entry`'s `ffi` to `input`.
pub(crate) fn call(entry: u32, input: &str) -> Result<String, CallError> {
    let mut n = 0u64;
    // SAFETY: `input` points to `input.len()` initialized bytes alive for the
    // call; `n` is a valid u64 the shim writes. The shim serializes callers.
    let text =
        unsafe { eukhe_bend_call(entry, input.as_ptr().cast(), input.len() as u64, &raw mut n) };
    if text.is_null() {
        return Err(fault(n));
    }
    take(text, n)
}

/// A new state of entry `entry`'s stepper: its handle and the reply.
pub(crate) fn open(entry: u32, input: &str) -> Result<(u64, String), CallError> {
    let mut text = ptr::null_mut();
    let mut n = 0u64;
    // SAFETY: as in `call`; `text` is a valid pointer slot the shim writes.
    let handle = unsafe {
        eukhe_bend_open(
            entry,
            input.as_ptr().cast(),
            input.len() as u64,
            &raw mut text,
            &raw mut n,
        )
    };
    if handle == 0 {
        return Err(fault(n));
    }
    Ok((handle, take(text, n)?))
}

/// Feeds `input` to the state of `handle`; the reply.
pub(crate) fn step(handle: u64, input: &str) -> Result<String, CallError> {
    let mut text = ptr::null_mut();
    let mut n = 0u64;
    // SAFETY: as in `open`; the shim checks `handle` (a stale one is EB_HANDLE).
    let rc = unsafe {
        eukhe_bend_step(
            handle,
            input.as_ptr().cast(),
            input.len() as u64,
            &raw mut text,
            &raw mut n,
        )
    };
    if rc != 0 {
        return Err(fault(u64::from(rc.unsigned_abs())));
    }
    take(text, n)
}

/// Drops the state of `handle` (a stale handle is left alone).
pub(crate) fn close(handle: u64) {
    // SAFETY: the shim checks `handle`; nothing is borrowed.
    unsafe { eukhe_bend_close(handle) };
}
