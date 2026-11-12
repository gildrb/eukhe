//! UNIX related logic for terminal manipulation.

use crate::terminal::{
    sys::file_descriptor::{tty_fd, FileDesc},
    WindowSize,
};
#[cfg(feature = "libc")]
use libc::{
    cfmakeraw, ioctl, tcgetattr, tcsetattr, termios as Termios, winsize, STDOUT_FILENO, TCSANOW,
    TIOCGWINSZ,
};
use parking_lot::Mutex;
#[cfg(not(feature = "libc"))]
use rustix::{
    fd::AsFd,
    termios::{Termios, Winsize},
};

use std::{fs::File, io, process};
#[cfg(feature = "libc")]
use std::{
    mem,
    os::unix::io::{IntoRawFd, RawFd},
};

// Some(Termios) -> we're in the raw mode and this is the previous mode
// None -> we're not in the raw mode
static TERMINAL_MODE_PRIOR_RAW_MODE: Mutex<Option<Termios>> = parking_lot::const_mutex(None);

pub(crate) fn is_raw_mode_enabled() -> bool {
    TERMINAL_MODE_PRIOR_RAW_MODE.lock().is_some()
}

#[cfg(feature = "libc")]
impl From<winsize> for WindowSize {
    fn from(size: winsize) -> WindowSize {
        WindowSize {
            columns: size.ws_col,
            rows: size.ws_row,
            width: size.ws_xpixel,
            height: size.ws_ypixel,
        }
    }
}
#[cfg(not(feature = "libc"))]
impl From<Winsize> for WindowSize {
    fn from(size: Winsize) -> WindowSize {
        WindowSize {
            columns: size.ws_col,
            rows: size.ws_row,
            width: size.ws_xpixel,
            height: size.ws_ypixel,
        }
    }
}

#[allow(clippy::useless_conversion)]
#[cfg(feature = "libc")]
pub(crate) fn window_size() -> io::Result<WindowSize> {
    // http://rosettacode.org/wiki/Terminal_control/Dimensions#Library:_BSD_libc
    let mut size = winsize {
        ws_row: 0,
        ws_col: 0,
        ws_xpixel: 0,
        ws_ypixel: 0,
    };

    let file = File::open("/dev/tty").map(|file| (FileDesc::new(file.into_raw_fd(), true)));
    let fd = if let Ok(file) = &file {
        file.raw_fd()
    } else {
        // Fallback to libc::STDOUT_FILENO if /dev/tty is missing
        STDOUT_FILENO
    };

    if wrap_with_result(unsafe { ioctl(fd, TIOCGWINSZ.into(), &mut size) }).is_ok() {
        return Ok(size.into());
    }

    Err(std::io::Error::last_os_error().into())
}

#[cfg(not(feature = "libc"))]
pub(crate) fn window_size() -> io::Result<WindowSize> {
    let file = File::open("/dev/tty").map(|file| FileDesc::Owned(file.into()));
    let fd = if let Ok(file) = &file {
        file.as_fd()
    } else {
        // Fallback to libc::STDOUT_FILENO if /dev/tty is missing
        rustix::stdio::stdout()
    };
    let size = rustix::termios::tcgetwinsize(fd)?;
    Ok(size.into())
}

#[allow(clippy::useless_conversion)]
pub(crate) fn size() -> io::Result<(u16, u16)> {
    if let Ok(window_size) = window_size() {
        return Ok((window_size.columns, window_size.rows));
    }

    tput_size().ok_or_else(|| std::io::Error::last_os_error().into())
}

#[cfg(feature = "libc")]
pub(crate) fn enable_raw_mode() -> io::Result<()> {
    let mut original_mode = TERMINAL_MODE_PRIOR_RAW_MODE.lock();
    if original_mode.is_some() {
        return Ok(());
    }

    let tty = tty_fd()?;
    let fd = tty.raw_fd();
    let mut ios = get_terminal_attr(fd)?;
    let original_mode_ios = ios;
    raw_terminal_attr(&mut ios);
    set_terminal_attr(fd, &ios)?;
    // Keep it last - set the original mode only if we were able to switch to the raw mode
    *original_mode = Some(original_mode_ios);
    Ok(())
}

#[cfg(not(feature = "libc"))]
pub(crate) fn enable_raw_mode() -> io::Result<()> {
    let mut original_mode = TERMINAL_MODE_PRIOR_RAW_MODE.lock();
    if original_mode.is_some() {
        return Ok(());
    }

    let tty = tty_fd()?;
    let mut ios = get_terminal_attr(&tty)?;
    let original_mode_ios = ios.clone();
    ios.make_raw();
    set_terminal_attr(&tty, &ios)?;
    // Keep it last - set the original mode only if we were able to switch to the raw mode
    *original_mode = Some(original_mode_ios);
    Ok(())
}

/// Reset the raw mode.
///
/// More precisely, reset the whole termios mode to what it was before the first call
/// to [enable_raw_mode]. If you don't mess with termios outside of crossterm, it's
/// effectively disabling the raw mode and doing nothing else.
#[cfg(feature = "libc")]
pub(crate) fn disable_raw_mode() -> io::Result<()> {
    let mut original_mode = TERMINAL_MODE_PRIOR_RAW_MODE.lock();
    if let Some(original_mode_ios) = original_mode.as_ref() {
        let tty = tty_fd()?;
        set_terminal_attr(tty.raw_fd(), original_mode_ios)?;
        // Keep it last - remove the original mode only if we were able to switch back
        *original_mode = None;
    }
    Ok(())
}

#[cfg(not(feature = "libc"))]
pub(crate) fn disable_raw_mode() -> io::Result<()> {
    let mut original_mode = TERMINAL_MODE_PRIOR_RAW_MODE.lock();
    if let Some(original_mode_ios) = original_mode.as_ref() {
        let tty = tty_fd()?;
        set_terminal_attr(&tty, original_mode_ios)?;
        // Keep it last - remove the original mode only if we were able to switch back
        *original_mode = None;
    }
    Ok(())
}

#[cfg(not(feature = "libc"))]
fn get_terminal_attr(fd: impl AsFd) -> io::Result<Termios> {
    let result = rustix::termios::tcgetattr(fd)?;
    Ok(result)
}

#[cfg(not(feature = "libc"))]
fn set_terminal_attr(fd: impl AsFd, termios: &Termios) -> io::Result<()> {
    rustix::termios::tcsetattr(fd, rustix::termios::OptionalActions::Now, termios)?;
    Ok(())
}

/// Queries the terminal's support for progressive keyboard enhancement.
///
/// On unix systems, this function will block and possibly time out while
/// [`crossterm::event::read`](crate::event::read) or [`crossterm::event::poll`](crate::event::poll) are being called.
#[cfg(feature = "events")]
pub fn supports_keyboard_enhancement() -> io::Result<bool> {
    if is_raw_mode_enabled() {
        read_supports_keyboard_enhancement_raw()
    } else {
        read_supports_keyboard_enhancement_flags()
    }
}

#[cfg(feature = "events")]
fn read_supports_keyboard_enhancement_flags() -> io::Result<bool> {
    enable_raw_mode()?;
    let flags = read_supports_keyboard_enhancement_raw();
    disable_raw_mode()?;
    flags
}

#[cfg(feature = "events")]
pub(crate) fn read_supports_keyboard_enhancement_raw() -> io::Result<bool> {
    use std::io::Write;

    // This is the recommended method for testing support for the keyboard enhancement protocol.
    // We send a query for the flags supported by the terminal and then the primary device attributes
    // query. If we receive the primary device attributes response but not the keyboard enhancement
    // flags, none of the flags are supported.
    //
    // See <https://sw.kovidgoyal.net/kitty/keyboard-protocol/#detection-of-support-for-this-protocol>

    // ESC [ ? u        Query progressive keyboard enhancement flags (kitty protocol).
    // ESC [ c          Query primary device attributes.
    const QUERY: &[u8] = b"\x1B[?u\x1B[c";

    let result = File::open("/dev/tty").and_then(|mut file| {
        file.write_all(QUERY)?;
        file.flush()
    });
    if result.is_err() {
        let mut stdout = io::stdout();
        stdout.write_all(QUERY)?;
        stdout.flush()?;
    }

    read_keyboard_enhancement_answer()
}

/// Reads the answer to the query `read_supports_keyboard_enhancement_raw`
/// sent, within a 250ms window (diagnostic 1c5af0f for its origin).
///
/// The probe shares the process-global event-reader lock with the app's
/// input reader, and each needs it without waiting on the other:
/// - The probe never waits on the tty with the lock held. Every 1ms it
///   takes the lock, looks for the answer in the shared queue and in what
///   the tty already holds (a zero-timeout poll), and releases. The app
///   reader, which waits on the tty itself, gets the lock in between and
///   delivers early typing at its own cadence; a reply it reads lands in
///   the same queue for the probe's next look.
/// - The probe waits for the lock for the whole remaining window. The app
///   reader re-takes the lock in a loop; a probe that gave up before the
///   reader's release lost every round on a loaded box with its answer
///   already queued. A parked probe gets the lock at the reader's next
///   (fair) release, then reads the answer under that one guard.
#[cfg(feature = "events")]
fn read_keyboard_enhancement_answer() -> io::Result<bool> {
    use crate::event::{
        filter::{KeyboardEnhancementFlagsFilter, PrimaryDeviceAttributesFilter},
        try_lock_internal_event_reader_for, InternalEvent,
    };
    use parking_lot::MappedMutexGuard;
    use std::time::{Duration, Instant};

    let deadline = Instant::now() + Duration::from_millis(250);
    let between_looks = Duration::from_millis(1);
    let timed_out = || {
        io::Error::new(
            io::ErrorKind::Other,
            "The keyboard enhancement status could not be read within a normal duration",
        )
    };
    loop {
        let leftover = deadline.saturating_duration_since(Instant::now());
        if leftover.is_zero() {
            return Err(timed_out());
        }
        let mut reader = match try_lock_internal_event_reader_for(leftover) {
            Some(reader) => reader,
            None => return Err(timed_out()),
        };
        // A poll error retries inside the same window.
        if let Ok(true) = reader.poll(Some(Duration::ZERO), &KeyboardEnhancementFlagsFilter) {
            return match reader.read(&KeyboardEnhancementFlagsFilter) {
                Ok(InternalEvent::KeyboardEnhancementFlags(_current_flags)) => {
                    // Flush the PrimaryDeviceAttributes out of the event queue.
                    reader.read(&PrimaryDeviceAttributesFilter).ok();
                    Ok(true)
                }
                _ => Ok(false),
            };
        }
        // The app reader, if parked on the lock, takes the next turn.
        MappedMutexGuard::unlock_fair(reader);
        std::thread::sleep(between_looks.min(deadline.saturating_duration_since(Instant::now())));
    }
}

/// execute tput with the given argument and parse
/// the output as a u16.
///
/// The arg should be "cols" or "lines"
fn tput_value(arg: &str) -> Option<u16> {
    let output = process::Command::new("tput").arg(arg).output().ok()?;
    let value = output
        .stdout
        .into_iter()
        .filter_map(|b| char::from(b).to_digit(10))
        .fold(0, |v, n| v * 10 + n as u16);

    if value > 0 {
        Some(value)
    } else {
        None
    }
}

/// Returns the size of the screen as determined by tput.
///
/// This alternate way of computing the size is useful
/// when in a subshell.
fn tput_size() -> Option<(u16, u16)> {
    match (tput_value("cols"), tput_value("lines")) {
        (Some(w), Some(h)) => Some((w, h)),
        _ => None,
    }
}

#[cfg(feature = "libc")]
// Transform the given mode into an raw mode (non-canonical) mode.
fn raw_terminal_attr(termios: &mut Termios) {
    unsafe { cfmakeraw(termios) }
}

#[cfg(feature = "libc")]
fn get_terminal_attr(fd: RawFd) -> io::Result<Termios> {
    unsafe {
        let mut termios = mem::zeroed();
        wrap_with_result(tcgetattr(fd, &mut termios))?;
        Ok(termios)
    }
}

#[cfg(feature = "libc")]
fn set_terminal_attr(fd: RawFd, termios: &Termios) -> io::Result<()> {
    wrap_with_result(unsafe { tcsetattr(fd, TCSANOW, termios) })
}

#[cfg(feature = "libc")]
fn wrap_with_result(result: i32) -> io::Result<()> {
    if result == -1 {
        Err(io::Error::last_os_error())
    } else {
        Ok(())
    }
}

#[cfg(all(test, feature = "events"))]
mod tests {
    use super::read_keyboard_enhancement_answer;
    use crate::event::{
        filter::KeyboardEnhancementFlagsFilter, lock_internal_event_reader,
        read::InternalEventReader, reader_lock_wait, source::EventSource, InternalEvent,
        KeyboardEnhancementFlags,
    };
    use parking_lot::{MappedMutexGuard, Mutex};
    use serial_test::serial;
    use std::io;
    use std::sync::{
        atomic::{AtomicBool, Ordering},
        mpsc, Arc,
    };
    use std::time::{Duration, Instant};

    /// The app reader re-takes the event-reader lock whenever nothing is
    /// parked on it at its release. Its worst case on a loaded box: every
    /// release lands just after the probe's wait gave up. This reader
    /// models that by releasing only to a single wait that has lasted
    /// 100ms (a short wait ends before the release), well inside the
    /// probe's 250ms window, with the probe's whole answer already queued.
    #[test]
    #[serial]
    fn a_queued_answer_reaches_the_probe_past_a_reader_that_keeps_the_lock() {
        const PATIENCE: Duration = Duration::from_millis(100);
        let probe_done = Arc::new(AtomicBool::new(false));
        let (held_tx, held_rx) = mpsc::channel();
        let reader = std::thread::spawn({
            let probe_done = Arc::clone(&probe_done);
            move || {
                let mut reader = lock_internal_event_reader();
                *reader = InternalEventReader::for_test(
                    [
                        InternalEvent::KeyboardEnhancementFlags(
                            KeyboardEnhancementFlags::DISAMBIGUATE_ESCAPE_CODES,
                        ),
                        InternalEvent::PrimaryDeviceAttributes,
                    ],
                    None,
                );
                held_tx.send(()).unwrap();
                let (mut wait, mut since) = (0, Instant::now());
                while !probe_done.load(Ordering::SeqCst) {
                    let current = reader_lock_wait::current();
                    if current == 0 || current != wait {
                        (wait, since) = (current, Instant::now());
                    } else if since.elapsed() >= PATIENCE {
                        MappedMutexGuard::unlock_fair(reader);
                        return;
                    }
                    std::hint::spin_loop();
                }
            }
        });
        held_rx.recv().unwrap();

        let answer = read_keyboard_enhancement_answer();
        probe_done.store(true, Ordering::SeqCst);
        reader.join().unwrap();

        assert!(
            matches!(answer, Ok(true)),
            "the probe missed its queued answer: {answer:?}"
        );
        // The probe consumed both replies, so the app never sees them.
        assert!(!matches!(
            lock_internal_event_reader()
                .poll(Some(Duration::ZERO), &KeyboardEnhancementFlagsFilter),
            Ok(true)
        ));
    }

    /// A tty that never answers; it records how long each read was allowed
    /// to wait.
    struct SilentTty {
        waits: Arc<Mutex<Vec<Option<Duration>>>>,
    }

    impl EventSource for SilentTty {
        fn try_read(&mut self, timeout: Option<Duration>) -> io::Result<Option<InternalEvent>> {
            self.waits.lock().push(timeout);
            if let Some(timeout) = timeout {
                std::thread::sleep(timeout);
            }
            Ok(None)
        }

        #[cfg(feature = "event-stream")]
        fn waker(&self) -> crate::event::sys::Waker {
            unimplemented!();
        }
    }

    /// The app reader waits on the tty for its input; a probe that waited
    /// on it too with the reader lock held kept the app's typing out for
    /// that wait. On a silent tty the probe's every read is a zero-timeout
    /// look at what has already arrived.
    #[test]
    #[serial]
    fn a_probe_on_a_silent_tty_never_waits_on_it_with_the_reader_locked() {
        let waits = Arc::new(Mutex::new(Vec::new()));
        *lock_internal_event_reader() = InternalEventReader::for_test(
            [],
            Some(Box::new(SilentTty {
                waits: Arc::clone(&waits),
            })),
        );

        let answer = read_keyboard_enhancement_answer();
        *lock_internal_event_reader() = InternalEventReader::for_test([], None);

        assert!(answer.is_err(), "a silent tty answered: {answer:?}");
        let waits = waits.lock();
        assert!(!waits.is_empty(), "the probe never looked at the tty");
        assert!(
            waits.iter().all(|wait| *wait == Some(Duration::ZERO)),
            "the probe waited on the tty with the reader locked: {waits:?}"
        );
    }
}
