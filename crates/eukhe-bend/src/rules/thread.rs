//! Each session is its own thread (`bend/thread.bend`, entry
//! `bend/ffi_thread.bend`; `laws/thread.bend`, spec
//! `spec/memory/thread.bend`): a root turn's request carries the view lines
//! of the history that scrolled out of the verbatim transcript, then the
//! session's own transcript. Of the view lines (oldest first), it keeps the
//! leading ones that start before end = through - verbatim (0 when verbatim
//! passes through); a line that straddles end stays whole.

use crate::wire::{Reader, Writer, NAT_MAX};
use crate::{call, expect_core, Entry, Error};

/// How many leading view lines a request keeps: `through` is the messages
/// the session's chat holds, `verbatim` the ones its transcript still holds
/// before the run, `starts` the first message of each view line, oldest
/// first.
#[must_use]
pub fn history_lines(through: u64, verbatim: u64, starts: &[u64]) -> usize {
    expect_core(Entry::Thread, history_lines_call(through, verbatim, starts))
}

fn history_lines_call(through: u64, verbatim: u64, starts: &[u64]) -> Result<usize, Error> {
    let mut request = Writer::new();
    request
        .count(starts.len() + 2)
        .nat(saturated(through))
        .nat(saturated(verbatim));
    for &start in starts {
        request.nat(saturated(start));
    }
    let reply = call(Entry::Thread, &request.finish()?)?;
    let mut reader = Reader::reply(&reply)?;
    let kept = reader.count()?;
    reader.end()?;
    Ok(kept)
}

/// A message id as the wire carries it: an id past [`NAT_MAX`] is as far
/// past every end the wire carries as `NAT_MAX` itself.
fn saturated(id: u64) -> u64 {
    id.min(NAT_MAX)
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The count comes from the compiled core: 10 messages, 3 verbatim (end
    /// 7) keep the lines at 0, 4 and 6 (6 straddles end), not 7; a window
    /// past the chat keeps nothing; no window keeps every line; only
    /// leading lines count.
    #[test]
    fn the_core_keeps_the_history_before_the_transcript() {
        assert_eq!(
            [
                history_lines(10, 3, &[0, 4, 6, 7]),
                history_lines(10, 3, &[0, 8]),
                history_lines(5, 9, &[0, 1]),
                history_lines(10, 0, &[0, 4, 8]),
                history_lines(10, 3, &[8, 0]),
                history_lines(4, 0, &[]),
            ],
            [3, 1, 0, 3, 0, 0]
        );
    }
}
