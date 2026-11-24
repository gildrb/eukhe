//! Listen-only event taps on their own run-loop threads (port of the tap
//! plumbing of omp `crates/natives/src/desktop/control/macos.rs`).

use std::ffi::c_void;
use std::io;
use std::ptr::{self, NonNull};
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::{mpsc, Arc};
use std::thread::{self, JoinHandle};

use objc2_core_foundation::{
    kCFRunLoopDefaultMode, CFMachPort, CFRetained, CFRunLoop, CFRunLoopRunResult,
};
use objc2_core_graphics::{
    CGEvent, CGEventField, CGEventMask, CGEventTapLocation, CGEventTapOptions, CGEventTapPlacement,
    CGEventTapProxy, CGEventType,
};

/// One event a tap saw.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct TapEvent {
    pub(crate) kind: u32,
    pub(crate) keycode: i64,
    pub(crate) flags: u64,
    /// The process that posted it; 0 for the user's own devices.
    pub(crate) source_pid: i64,
    /// `kCGEventSourceUserData`, which this backend tags its events with.
    pub(crate) user_data: i64,
    /// The process `WindowServer` routes it to (annotated session tap).
    pub(crate) target_pid: i64,
}

/// Why a tap did not start.
#[derive(Debug)]
pub(crate) enum TapError {
    /// No event-listening access: the tap was refused.
    Refused,
    Thread(io::Error),
}

/// A running tap; dropping it stops its thread.
pub(crate) struct Tap {
    stopping: Arc<AtomicBool>,
    run_loop: RemoteLoop,
    thread: Option<JoinHandle<()>>,
}

/// A run loop another thread may stop.
struct RemoteLoop(CFRetained<CFRunLoop>);

// SAFETY: the only call made through it from another thread is
// `CFRunLoopStop`, which CoreFoundation documents as thread-safe.
unsafe impl Send for RemoteLoop {}

/// How long the tap thread runs its loop before checking for a stop that
/// came before the loop ran.
const LOOP_SLICE: f64 = 0.25;

struct Context<F> {
    on_event: F,
    port: Option<CFRetained<CFMachPort>>,
}

impl Tap {
    /// Watches events of the CG types `kinds` at the annotated session tap,
    /// calling `on_event` on the tap's thread for each.
    pub(crate) fn listen<F>(name: &str, kinds: &[u32], on_event: F) -> Result<Self, TapError>
    where
        F: FnMut(&TapEvent) + Send + 'static,
    {
        let mask: CGEventMask = kinds.iter().fold(0, |mask, kind| mask | (1 << kind));
        let stopping = Arc::new(AtomicBool::new(false));
        let (ready, started) = mpsc::sync_channel(1);
        let flag = Arc::clone(&stopping);
        let thread = thread::Builder::new()
            .name(name.to_owned())
            .spawn(move || run(mask, on_event, &flag, &ready))
            .map_err(TapError::Thread)?;
        match started.recv() {
            Ok(Ok(run_loop)) => Ok(Self {
                stopping,
                run_loop,
                thread: Some(thread),
            }),
            Ok(Err(error)) => {
                thread.join().ok();
                Err(error)
            }
            Err(_) => {
                thread.join().ok();
                Err(TapError::Refused)
            }
        }
    }
}

impl Drop for Tap {
    fn drop(&mut self) {
        self.stopping.store(true, Ordering::Release);
        self.run_loop.0.stop();
        if let Some(thread) = self.thread.take() {
            thread.join().ok();
        }
    }
}

fn run<F: FnMut(&TapEvent)>(
    mask: CGEventMask,
    on_event: F,
    stopping: &AtomicBool,
    ready: &mpsc::SyncSender<Result<RemoteLoop, TapError>>,
) {
    let mut storage = Context {
        on_event,
        port: None,
    };
    let context: *mut Context<F> = ptr::from_mut(&mut storage);
    // SAFETY: `callback::<F>` matches `CGEventTapCallBack`; `storage` lives
    // on this thread's stack until the port is invalidated below, and the
    // callback runs only inside this thread's run loop.
    let port = unsafe {
        CGEvent::tap_create(
            CGEventTapLocation::AnnotatedSessionEventTap,
            CGEventTapPlacement::HeadInsertEventTap,
            CGEventTapOptions::ListenOnly,
            mask,
            Some(callback::<F>),
            context.cast(),
        )
    };
    let Some(port) = port else {
        ready.send(Err(TapError::Refused)).ok();
        return;
    };
    // SAFETY: no callback runs before this thread runs its loop, and every
    // access after this goes through `context`.
    unsafe { (*context).port = Some(port.clone()) };
    let source = CFMachPort::new_run_loop_source(None, Some(&port), 0);
    let Some((source, run_loop)) = source.zip(CFRunLoop::current()) else {
        port.invalidate();
        ready.send(Err(TapError::Refused)).ok();
        return;
    };
    // SAFETY: the default mode constant is process-lived.
    let mode = unsafe { kCFRunLoopDefaultMode };
    run_loop.add_source(Some(&source), mode);
    CGEvent::tap_enable(&port, true);
    if ready.send(Ok(RemoteLoop(run_loop))).is_err() {
        port.invalidate();
        return;
    }
    while !stopping.load(Ordering::Acquire) {
        if CFRunLoop::run_in_mode(mode, LOOP_SLICE, false) == CFRunLoopRunResult::Finished {
            break;
        }
    }
    port.invalidate();
}

unsafe extern "C-unwind" fn callback<F: FnMut(&TapEvent)>(
    _proxy: CGEventTapProxy,
    kind: CGEventType,
    event: NonNull<CGEvent>,
    user: *mut c_void,
) -> *mut CGEvent {
    // SAFETY: `user` is the `Context<F>` `run` keeps alive on its stack for
    // as long as the tap can call back, on this same thread.
    let context = unsafe { &mut *user.cast::<Context<F>>() };
    if kind == CGEventType::TapDisabledByTimeout || kind == CGEventType::TapDisabledByUserInput {
        if let Some(port) = &context.port {
            CGEvent::tap_enable(port, true);
        }
        return event.as_ptr();
    }
    // SAFETY: the event is alive for the callback.
    let event_ref = unsafe { event.as_ref() };
    let field = |field: u32| CGEvent::integer_value_field(Some(event_ref), CGEventField(field));
    (context.on_event)(&TapEvent {
        kind: kind.0,
        keycode: field(9),
        flags: CGEvent::flags(Some(event_ref)).bits(),
        source_pid: field(41),
        user_data: field(42),
        target_pid: field(40),
    });
    event.as_ptr()
}
