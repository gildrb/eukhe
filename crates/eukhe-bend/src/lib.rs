//! The compiled Bend core: every eukhe rule with a Bend model runs as that
//! model, compiled by Bend into `c/core.c` and called through `c/shim.c`.
//!
//! An entry is one `bend/ffi_<area>.bend` ([`Entry`]). It answers text with
//! text: a [`call`] maps one input to one reply; a [`Stepper`] keeps a state
//! in the Bend heap between inputs, so a hot path ships each event, not its
//! whole state. Every entry runs on the caller's thread under one process-wide
//! lock (one evaluation at a time); the first entry maps the runtime's heap
//! and stack (address space reserved with `MAP_NORESERVE`, touched on use:
//! a 512 MiB heap that doubles in place on demand and a 256 MiB stack, about
//! 790 MB of address space in all: a first call succeeds under a 1 GiB
//! `ulimit -v`; the runtime's own setup would reserve 10 GiB).
//!
//! A Bend run-time fail-stop (a `Nat` past 2^48-1) ends the process: entries
//! bound their inputs so a pure evaluation cannot reach one.

mod entries;
mod ffi;
pub mod rules;
pub mod wire;

pub use entries::Entry;
pub use wire::WireError;

use std::fmt;
use std::string::FromUtf8Error;

/// Why an entry of the compiled core answered no reply.
#[derive(Debug)]
pub enum CallError {
    /// The core's segments do not have the shapes `c/shim.c` expects:
    /// `c/core.c` and the shim are out of step (`make bend-core`).
    Abi,
    /// The stepper's state is gone.
    StaleHandle,
    /// The shim's state table could not grow.
    OutOfMemory,
    /// The reply was not UTF-8.
    InvalidUtf8(FromUtf8Error),
}

impl fmt::Display for CallError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            CallError::Abi => {
                f.write_str("the compiled Bend core does not match its C shim (make bend-core)")
            }
            CallError::StaleHandle => f.write_str("the Bend stepper state is gone"),
            CallError::OutOfMemory => f.write_str("the Bend stepper table could not grow"),
            CallError::InvalidUtf8(e) => write!(f, "the Bend core replied with invalid UTF-8: {e}"),
        }
    }
}

impl std::error::Error for CallError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            CallError::InvalidUtf8(e) => Some(e),
            CallError::Abi | CallError::StaleHandle | CallError::OutOfMemory => None,
        }
    }
}

/// Why a rule of the compiled core answered no decision: the call failed,
/// or the request or the reply did not fit the wire format.
#[derive(Debug)]
pub enum Error {
    Call(CallError),
    Wire(WireError),
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Error::Call(e) => e.fmt(f),
            Error::Wire(e) => e.fmt(f),
        }
    }
}

impl std::error::Error for Error {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Error::Call(e) => Some(e),
            Error::Wire(e) => Some(e),
        }
    }
}

impl From<CallError> for Error {
    fn from(e: CallError) -> Error {
        Error::Call(e)
    }
}

impl From<WireError> for Error {
    fn from(e: WireError) -> Error {
        Error::Wire(e)
    }
}

/// The reply of `entry`'s `ffi` to `input`.
///
/// # Errors
///
/// [`CallError::Abi`] when the core and the shim are out of step, and
/// [`CallError::InvalidUtf8`] when the reply is not UTF-8.
pub fn call(entry: Entry, input: &str) -> Result<String, CallError> {
    ffi::call(entry.id(), input)
}

/// The value of a core call on input eukhe itself encoded: the one place
/// eukhe panics on a failure of the compiled core.
///
/// A caller that encodes its own request (every number in range: it
/// saturates or validates first) can meet a [`CallError`] or a
/// [`WireError`] only from an inconsistent build: the Bend decoders are
/// proven on the wire round trip (`laws/wire.bend`), the Rust
/// codec is tested through the FFI against them, and `make
/// bend-core-check` keeps `c/core.c` in step with `bend/`. A caller that
/// already returns a `Result` propagates the [`Error`] instead.
///
/// # Panics
///
/// When `result` is an error: the message names `entry` and the error.
pub fn expect_core<T, E: Into<Error>>(entry: Entry, result: Result<T, E>) -> T {
    match result {
        Ok(value) => value,
        Err(error) => {
            let error: Error = error.into();
            panic!("the compiled Bend core failed on entry {entry:?}: {error}")
        }
    }
}

/// A state of an entry's stepper, kept in the Bend heap. Each input replaces
/// it with the state the entry's `step` answers; dropping it frees it.
#[derive(Debug)]
pub struct Stepper {
    handle: u64,
}

impl Stepper {
    /// Opens a state of `entry`'s stepper from `input`; answers it and the
    /// reply of the entry's `open` (a malformed `input` opens the entry's
    /// error state, and the reply is the wire error form).
    ///
    /// # Errors
    ///
    /// [`CallError::Abi`] and [`CallError::InvalidUtf8`] as for [`call`];
    /// [`CallError::OutOfMemory`] when the shim's state table cannot grow.
    pub fn open(entry: Entry, input: &str) -> Result<(Stepper, String), CallError> {
        let (handle, reply) = ffi::open(entry.id(), input)?;
        Ok((Stepper { handle }, reply))
    }

    /// Feeds `input` to the state; answers the reply of the entry's `step`.
    ///
    /// # Errors
    ///
    /// [`CallError::InvalidUtf8`] when the reply is not UTF-8 (the state has
    /// still moved on); [`CallError::StaleHandle`] if the shim lost the state.
    pub fn step(&mut self, input: &str) -> Result<String, CallError> {
        ffi::step(self.handle, input)
    }
}

impl Drop for Stepper {
    fn drop(&mut self) {
        ffi::close(self.handle);
    }
}

#[cfg(test)]
mod tests {
    use super::{call, CallError, Entry, Stepper};

    #[test]
    fn echo_round_trips() {
        for text in [
            "hello",
            "",
            "é",
            "naïve café",
            "😀 family: 👨‍👩‍👧",
            "漢字かなカナ",
            "a\nb\tc\0d",
        ] {
            assert_eq!(call(Entry::Echo, text).unwrap(), text);
        }
    }

    #[test]
    fn echo_round_trips_a_large_input() {
        let text = "ação 漢 😀 ".repeat(100_000);
        assert_eq!(call(Entry::Echo, &text).unwrap(), text);
    }

    #[test]
    fn an_unknown_entry_answers_the_error_form() {
        let unknown = Entry::ALL.iter().map(|e| e.id()).max().unwrap() + 1;
        assert_eq!(super::ffi::call(unknown, "x").unwrap(), "E unknown entry");
        let (handle, reply) = super::ffi::open(unknown, "0").unwrap();
        assert_eq!(reply, "E unknown entry");
        assert_eq!(super::ffi::step(handle, "x").unwrap(), "E unknown entry");
        super::ffi::close(handle);
    }

    #[test]
    fn ids_are_the_discriminants() {
        for (i, e) in Entry::ALL.iter().enumerate() {
            assert_eq!(e.id(), *e as u32);
            assert!(Entry::ALL[..i].iter().all(|f| f.id() < e.id()));
        }
    }

    #[test]
    fn concurrent_calls_answer_their_own_input() {
        let threads: Vec<_> = (0..4)
            .map(|t| {
                std::thread::spawn(move || {
                    for i in 0..500 {
                        let text = format!("thread {t} call {i} ✓");
                        assert_eq!(call(Entry::Echo, &text).unwrap(), text);
                    }
                })
            })
            .collect();
        for t in threads {
            t.join().unwrap();
        }
    }

    #[test]
    fn a_stepper_keeps_its_state() {
        let (mut st, reply) = Stepper::open(Entry::Echo, "5").unwrap();
        assert_eq!(reply, "5");
        assert_eq!(st.step("é").unwrap(), "6 ");
        assert_eq!(st.step("😀").unwrap(), "7 é");
        assert_eq!(st.step("").unwrap(), "8 😀");
        assert_eq!(st.step("x").unwrap(), "9 ");
    }

    #[test]
    fn a_malformed_open_opens_the_error_state() {
        let (mut st, reply) = Stepper::open(Entry::Echo, "five").unwrap();
        assert!(reply.starts_with("E "), "{reply}");
        let again = st.step("x").unwrap();
        assert!(again.starts_with("E "), "{again}");
    }

    #[test]
    fn steppers_are_independent_across_threads() {
        let threads: Vec<_> = (0..4u32)
            .map(|t| {
                std::thread::spawn(move || {
                    let (mut st, _) = Stepper::open(Entry::Echo, &(t * 1000).to_string()).unwrap();
                    let mut last = String::new();
                    for i in 1..=300u32 {
                        let ev = format!("{t}:{i}");
                        assert_eq!(st.step(&ev).unwrap(), format!("{} {last}", t * 1000 + i));
                        last = ev;
                    }
                })
            })
            .collect();
        for t in threads {
            t.join().unwrap();
        }
    }

    #[test]
    fn a_closed_handle_is_stale() {
        let (st, _) = Stepper::open(Entry::Echo, "1").unwrap();
        let handle = st.handle;
        drop(st);
        assert!(matches!(
            super::ffi::step(handle, "x"),
            Err(CallError::StaleHandle)
        ));
        // A second close of the handle is left alone.
        super::ffi::close(handle);
        // The slot is reused under a new generation; the old handle stays stale.
        let (mut again, _) = Stepper::open(Entry::Echo, "2").unwrap();
        assert!(matches!(
            super::ffi::step(handle, "x"),
            Err(CallError::StaleHandle)
        ));
        assert!(matches!(
            super::ffi::step(0, "x"),
            Err(CallError::StaleHandle)
        ));
        assert_eq!(again.step("y").unwrap(), "3 ");
    }
}
