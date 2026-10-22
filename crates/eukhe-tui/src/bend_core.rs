//! One call of the compiled Bend core (`eukhe-bend`) on a request this
//! crate writes itself: the transcript ledger, the pace, the stack and the
//! replacement verdict run as their Bend models (`bend/ffi_screen.bend`,
//! `bend/ffi_replace.bend`).

use eukhe_bend::wire::{Reader, WireError, Writer};
use eukhe_bend::{expect_core, Entry};

/// The reply of `entry` to the request `write` writes, read by `read`
/// (which must read all of it). Every caller writes its numbers saturated
/// at `eukhe_bend::wire::NAT_MAX` and its strings below
/// `eukhe_bend::wire::STR_MAX`, so a failure can only mean an inconsistent
/// build: `expect_core` reports it.
pub(crate) fn decide<T>(
    entry: Entry,
    write: impl FnOnce(&mut Writer),
    read: impl FnOnce(&mut Reader<'_>) -> Result<T, WireError>,
) -> T {
    let result = (|| -> Result<T, eukhe_bend::Error> {
        let mut writer = Writer::new();
        write(&mut writer);
        let request = writer.finish()?;
        let reply = eukhe_bend::call(entry, &request)?;
        let mut reader = Reader::reply(&reply)?;
        let value = read(&mut reader)?;
        reader.end()?;
        Ok(value)
    })();
    expect_core(entry, result)
}
