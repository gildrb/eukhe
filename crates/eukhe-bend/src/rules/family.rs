//! Subagent admission (`bend/family.bend`, entry `bend/ffi_family.bend`;
//! `laws/family.bend`, spec `spec/rlm/family.bend`): a batch of spawns is
//! decided whole. Every spawn names an allowed reason (`why`: `parallel`,
//! `isolate`, `tools`, `user`), the caller is below the recursion bound,
//! and the family's running subagents plus the batch fit the cap (0: no
//! cap). Refusal order: a missing reason, the depth, the cap.

use crate::wire::{Reader, Writer, STR_MAX};
use crate::{call, expect_core, Entry, Error};

/// The facts a spawn batch is decided on.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Batch<'a> {
    /// The calling agent's recursion depth (0: a root session).
    pub depth: u32,
    /// The recursion bound (`rlmMaxDepth`).
    pub max_depth: u32,
    /// The family's subagents running or starting now.
    pub running: u32,
    /// `subagentMaxConcurrency`; 0: no cap.
    pub cap: u32,
    /// The `why` of each spawn of the batch, in order; `None`: not given.
    pub whys: &'a [Option<&'a str>],
}

/// The decision on a batch.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Admission {
    /// Every spawn of the batch admits; each child runs at `child_depth`.
    Admit { child_depth: u32 },
    /// Nothing admits; the text says why (the error the caller shows).
    Refuse(String),
}

/// The decision on `batch`, from the compiled core.
#[must_use]
pub fn admit(batch: &Batch<'_>) -> Admission {
    expect_core(Entry::Family, admit_call(batch))
}

fn admit_call(batch: &Batch<'_>) -> Result<Admission, Error> {
    let mut request = Writer::new();
    request
        .u32(batch.depth)
        .u32(batch.max_depth)
        .u32(batch.running)
        .u32(batch.cap)
        .count(batch.whys.len());
    for why in batch.whys {
        request.str(why.map_or("", wire_why));
    }
    let reply = call(Entry::Family, &request.finish()?)?;
    let mut reader = Reader::reply(&reply)?;
    let admission = if reader.tag_of(2, "a family verdict")? == 0 {
        Admission::Admit {
            child_depth: reader.u32()?,
        }
    } else {
        Admission::Refuse(reader.str()?.to_owned())
    };
    reader.end()?;
    Ok(admission)
}

/// A why as the wire carries it: its first [`STR_MAX`] chars (no reason
/// is that long, so a longer why stays refused).
fn wire_why(why: &str) -> &str {
    why.char_indices()
        .nth(STR_MAX)
        .map_or(why, |(end, _)| &why[..end])
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The decisions come from the compiled core: a spawn at the bound is
    /// refused for the depth, a batch over the cap admits none, a batch
    /// that fits admits one level deeper, a missing why is refused first.
    #[test]
    fn the_core_decides_admission() {
        let batch = |depth, running, cap, whys| Batch {
            depth,
            max_depth: 2,
            running,
            cap,
            whys,
        };
        let refused = |text: &str| Admission::Refuse(text.to_owned());
        assert_eq!(
            [
                admit(&batch(2, 0, 0, &[Some("parallel")])),
                admit(&batch(0, 1, 3, &[Some("parallel"), Some("isolate"), Some("tools")])),
                admit(&batch(1, 1, 3, &[Some("user"), Some("isolate")])),
                admit(&batch(2, 9, 1, &[Some("parallel"), None])),
            ],
            [
                refused("RLM recursion depth limit reached (RLM_DEPTH=2, RLM_MAX_DEPTH=2)"),
                refused("subagent concurrency limit 3 is already full"),
                Admission::Admit { child_depth: 2 },
                refused(
                    "rlm.spawn task 1 has no allowed why: why must be \"parallel\" (independent tasks run at once), \"isolate\" (the work would bloat this context; only a compact result comes back), \"tools\" (the task needs a tool set or instructions that conflict with this agent's) or \"user\" (the user asked for a subagent); otherwise do the work in this loop"
                ),
            ]
        );
    }
}
