//! The separators an edited file persists with (model `bend/doc_lines.bend`
//! `plan`, laws `persist_plan_refines` and `persist_weaves_carry` in
//! `LAWS.bend` section `documents`, F4): after each line but the last, the
//! ending of the file line it came from, else the separator written before
//! it. [`plan`] is the whole decision over runs; `FileRead::persist`
//! (`patcher.rs`) builds the runs and writes the bytes.

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

/// The separators of the runs, with `carry` before the first line (model
/// `plan`).
pub(crate) fn plan(runs: &[EndRun], mut carry: LineEnding) -> Vec<SepRun> {
    let mut seps = Vec::with_capacity(runs.len());
    for run in runs.iter().filter(|run| run.n > 0) {
        if let Some(end) = run.end {
            carry = end;
        }
        seps.push(SepRun {
            end: carry,
            n: run.n,
        });
    }
    seps
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
