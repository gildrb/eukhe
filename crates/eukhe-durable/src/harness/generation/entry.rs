//! The run's entry of the compiled Bend core (`bend/ffi_run.bend`): the
//! requests of the decisions of [`super::decide`] and [`super::deferred`]
//! in the wire format (`crates/eukhe-bend/WIRE.md`), and the reading of
//! their answers. The decisions are `decide.*` of `bend/run.bend`, which
//! `laws/run.bend` (H4.9) proves equal to the rules they replaced; its
//! `run_ffi` laws prove the codec. eukhe encodes every request itself, its u64
//! counts saturated at [`NAT_MAX`] (laws `run_reply_saturates_the_wait`
//! and `run_reply_saturates_the_attempt`), so a failure of the core can
//! only be an inconsistent build: [`expect_core`].

use eukhe_bend::wire::{Reader, WireError, Writer, NAT_MAX};
use eukhe_bend::{call, expect_core, Entry};

/// The decision a request asks for: the index of its constructor in
/// `Ask` of `bend/ffi_run.bend`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum Ask {
    Reply = 0,
    Ended = 1,
    Prepare = 2,
    Compact = 3,
    Round = 4,
    Recover = 5,
    Poll = 6,
}

/// The answer of the run's entry to the request `ask` with the inputs
/// that `write` writes, as `read` reads it (the whole answer).
pub(super) fn ask<T>(
    ask: Ask,
    write: impl FnOnce(&mut Writer),
    read: impl FnOnce(&mut Reader<'_>) -> Result<T, WireError>,
) -> T {
    let mut writer = Writer::new();
    writer.tag(ask as u32);
    write(&mut writer);
    let input = expect_core(Entry::Run, writer.finish());
    let answer = expect_core(Entry::Run, call(Entry::Run, &input));
    expect_core(
        Entry::Run,
        Reader::reply(&answer).and_then(|mut reader| {
            let value = read(&mut reader)?;
            reader.end()?;
            Ok(value)
        }),
    )
}

/// A u64 count as the wire carries it: saturated at its largest Nat.
pub(super) fn saturated(n: u64) -> u64 {
    n.min(NAT_MAX)
}

/// An answer that does not fit the request it answers.
pub(super) fn mismatch(expected: &'static str) -> WireError {
    WireError::Malformed { at: 0, expected }
}

/// An answer that is one Bool.
pub(super) fn bool(reader: &mut Reader<'_>) -> Result<bool, WireError> {
    reader.bool()
}
