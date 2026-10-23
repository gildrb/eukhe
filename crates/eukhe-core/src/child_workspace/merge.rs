//! The plan of one path of the hand-back: `plan` in `bend/sandbox.bend`
//! (`laws/sandbox.bend` S3, `cow_plan`, `cow_plan_is_merge`), run by the
//! compiled Bend core (`bend/ffi_sandbox.bend`). The plan compares the
//! parent's, the base's and the child's contents only for equality, so the
//! request carries each content as the index of the first equal one
//! (parent 0, base 0 or 1, child 0, 1 or 2); `None` is no file.

use eukhe_bend::wire::{Reader, Writer};
use eukhe_bend::{Entry, Error};

/// What the hand-back does with one path.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum Plan {
    /// The parent's content stays. `taken`: both changed the path to the
    /// same content, so the child's change is in the parent already.
    Keep { taken: bool },
    /// Both changed the path differently: the parent's content stays and
    /// the path is a conflict.
    Clash,
    /// Only the child changed the path, to a file: the child's file goes
    /// in, unless its place in the parent is blocked (then a conflict).
    Take,
    /// Only the child changed the path, by removing it: the parent's goes.
    Drop,
}

/// The plan of a path whose parent, base and child contents are these.
pub(super) fn plan<T: PartialEq>(parent: Option<&T>, base: Option<&T>, child: Option<&T>) -> Plan {
    eukhe_bend::expect_core(Entry::Sandbox, ask(parent, base, child))
}

fn ask<T: PartialEq>(
    parent: Option<&T>,
    base: Option<&T>,
    child: Option<&T>,
) -> Result<Plan, Error> {
    let contents = [parent, base, child];
    let mut request = Writer::new();
    for (index, content) in contents.iter().enumerate() {
        match content {
            None => request.none(),
            Some(content) => {
                let first = contents[..index]
                    .iter()
                    .position(|earlier| *earlier == Some(*content))
                    .unwrap_or(index);
                request.some().nat(first as u64)
            }
        };
    }
    let reply = eukhe_bend::call(Entry::Sandbox, &request.finish()?)?;
    let mut reader = Reader::reply(&reply)?;
    let plan = match reader.tag_of(4, "a hand-back plan")? {
        0 => Plan::Keep {
            taken: reader.bool()?,
        },
        1 => Plan::Clash,
        2 => Plan::Take,
        // `tag_of` answers a tag below 4: this is 3.
        _ => Plan::Drop,
    };
    reader.end()?;
    Ok(plan)
}
