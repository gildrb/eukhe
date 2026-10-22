//! The separators an edited file persists with (model `bend/doc_lines.bend`
//! `plan`, laws `persist_plan_refines` and `persist_weaves_carry` in
//! `LAWS.bend` section `documents`, F4): after each line but the last, the
//! ending of the file line it came from, else the separator written before
//! it. [`plan`] is the whole decision over runs, one call of the compiled
//! Bend core (`bend/ffi_doc_lines.bend`); `FileRead::persist`
//! (`patcher.rs`) builds the runs and writes the bytes.

use eukhe_bend::wire::{Reader, WireError, Writer};
use eukhe_bend::{expect_core, Entry};

use crate::text::LineEnding;

/// `n` lines in a row whose origin ends with `end` (`None`: a new line,
/// or a line with no ending) (model `Run`).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct EndRun {
    pub(crate) end: Option<LineEnding>,
    pub(crate) n: usize,
}

/// `n` separators in a row (model `Seps`).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct SepRun {
    pub(crate) end: LineEnding,
    pub(crate) n: usize,
}

/// The wire tag of an ending (model `End`: `Lf` 0, `CrLf` 1).
fn tag(end: LineEnding) -> u32 {
    match end {
        LineEnding::Lf => 0,
        LineEnding::CrLf => 1,
    }
}

/// The separators of the runs, with `carry` before the first line (model
/// `plan`, through `bend/ffi_doc_lines.bend`).
pub(crate) fn plan(runs: &[EndRun], carry: LineEnding) -> Vec<SepRun> {
    let mut request = Writer::new();
    request.count(runs.len());
    for run in runs {
        match run.end {
            Some(end) => request.some().tag(tag(end)),
            None => request.none(),
        };
        request.count(run.n);
    }
    request.tag(tag(carry));
    let request = expect_core(Entry::DocLines, request.finish());
    let reply = expect_core(Entry::DocLines, eukhe_bend::call(Entry::DocLines, &request));
    expect_core(Entry::DocLines, seps(&reply))
}

/// The reply of `bend/ffi_doc_lines.bend`.
fn seps(reply: &str) -> Result<Vec<SepRun>, WireError> {
    let mut reader = Reader::reply(reply)?;
    let seps = (0..reader.count()?)
        .map(|_| {
            // tag_of answers 0 or 1: Lf or CrLf.
            let end = if reader.tag_of(2, "a line ending")? == 0 {
                LineEnding::Lf
            } else {
                LineEnding::CrLf
            };
            Ok(SepRun {
                end,
                n: reader.count()?,
            })
        })
        .collect::<Result<Vec<_>, WireError>>()?;
    reader.end()?;
    Ok(seps)
}

/// The values as runs of equal neighbours.
pub(crate) fn runs(ends: impl Iterator<Item = Option<LineEnding>>) -> Vec<EndRun> {
    let mut runs = Vec::<EndRun>::new();
    for end in ends {
        match runs.last_mut() {
            Some(run) if run.end == end => run.n += 1,
            Some(_) | None => runs.push(EndRun { end, n: 1 }),
        }
    }
    runs
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn runs_group_equal_neighbours() {
        let ends = [
            Some(LineEnding::CrLf),
            Some(LineEnding::CrLf),
            None,
            Some(LineEnding::Lf),
            None,
        ];
        assert_eq!(
            runs(ends.into_iter()),
            [
                EndRun {
                    end: Some(LineEnding::CrLf),
                    n: 2
                },
                EndRun { end: None, n: 1 },
                EndRun {
                    end: Some(LineEnding::Lf),
                    n: 1
                },
                EndRun { end: None, n: 1 },
            ]
        );
    }
}
