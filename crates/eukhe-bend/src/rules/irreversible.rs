//! The irreversible effects (`bend/irreversible.bend`, entry
//! `bend/ffi_irreversible.bend`; `laws/irreversible.bend`): which effects
//! are irreversible, what recording one in the ledger answers, and the
//! end-of-run list. Each function encodes the facts Rust gathered, calls
//! [`Entry::Irreversible`] and decodes the decision. A ledger key crosses
//! as a number: equal keys, equal numbers.

use std::collections::HashMap;

use eukhe_types::effects::EffectClass;

use crate::wire::{Reader, Writer};
use crate::{call, expect_core, Entry as CoreEntry, Error};

/// One entry of the ledger, in ledger order. A ledger built by [`record`]
/// holds each entry at its id: the first is 1, the next 2, and so on.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Entry {
    /// The id (`e<n>`).
    pub n: u64,
    /// The effect's key: recording it again changes nothing.
    pub key: String,
    /// The run it ran in.
    pub run: u64,
}

/// What recording a key answers.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Recorded {
    /// The key is new: append it last with this id.
    New(u64),
    /// The ledger holds the key already, at this id: nothing changes.
    Known(u64),
}

/// Whether an effect of `classes` is irreversible: some class is none of
/// read, write and exec (`Ir.irreversible`).
#[must_use]
pub fn is_irreversible(classes: &[EffectClass]) -> bool {
    expect_core(CoreEntry::Irreversible, classes_call(classes))
}

fn classes_call(classes: &[EffectClass]) -> Result<bool, Error> {
    let mut request = Writer::new();
    request.tag(0).count(classes.len());
    for class in classes {
        request.nat(u64::from(class.code()));
    }
    let reply = call(CoreEntry::Irreversible, &request.finish()?)?;
    let mut reader = Reader::reply(&reply)?;
    let irreversible = reader.bool()?;
    reader.end()?;
    Ok(irreversible)
}

/// What recording `key` on `ledger` answers (`Ir.record`): the id of the
/// entry that holds it, or the id a new last entry gets.
///
/// # Errors
///
/// A number past the wire (a run or a ledger past `wire::NAT_MAX`) or a
/// failure of the compiled core.
pub fn record(ledger: &[Entry], key: &str) -> Result<Recorded, Error> {
    let mut keys = Keys::default();
    let mut request = Writer::new();
    request.tag(1);
    entries(&mut request, &mut keys, ledger);
    request.nat(keys.id(key));
    let reply = call(CoreEntry::Irreversible, &request.finish()?)?;
    let mut reader = Reader::reply(&reply)?;
    let recorded = match reader.tag_of(2, "what recording answers")? {
        0 => Recorded::New(reader.nat()?),
        // `tag_of` answers a tag below 2: this is 1.
        _ => Recorded::Known(reader.nat()?),
    };
    reader.end()?;
    Ok(recorded)
}

/// The ids of the entries of `ledger` that ran in `run`, in ledger order:
/// the end-of-run list (`Ir.report`).
///
/// # Errors
///
/// A number past the wire (a run or a ledger past `wire::NAT_MAX`) or a
/// failure of the compiled core.
pub fn this_run(ledger: &[Entry], run: u64) -> Result<Vec<u64>, Error> {
    let mut keys = Keys::default();
    let mut request = Writer::new();
    request.tag(2);
    entries(&mut request, &mut keys, ledger);
    request.nat(run);
    let reply = call(CoreEntry::Irreversible, &request.finish()?)?;
    let mut reader = Reader::reply(&reply)?;
    let ids = (0..reader.count()?)
        .map(|_| reader.nat())
        .collect::<Result<Vec<u64>, _>>()?;
    reader.end()?;
    Ok(ids)
}

/// Interns keys: each distinct key is one number.
#[derive(Default)]
struct Keys<'a> {
    ids: HashMap<&'a str, u64>,
}

impl<'a> Keys<'a> {
    fn id(&mut self, key: &'a str) -> u64 {
        let next = u64::try_from(self.ids.len()).unwrap_or(u64::MAX);
        *self.ids.entry(key).or_insert(next)
    }
}

/// The ledger as the list of each entry's key and run.
fn entries<'a>(request: &mut Writer, keys: &mut Keys<'a>, ledger: &'a [Entry]) {
    request.count(2 * ledger.len());
    for entry in ledger {
        request.nat(keys.id(&entry.key)).nat(entry.run);
    }
}

#[cfg(test)]
mod tests {
    use eukhe_types::effects::EffectClass;

    use super::{is_irreversible, record, this_run, Entry, Recorded};

    fn entry(n: u64, key: &str, run: u64) -> Entry {
        Entry {
            n,
            key: key.to_owned(),
            run,
        }
    }

    #[test]
    fn an_effect_is_irreversible_past_read_write_and_exec() {
        assert_eq!(
            (
                is_irreversible(&[]),
                is_irreversible(&[EffectClass::Read, EffectClass::Write, EffectClass::Exec]),
                is_irreversible(&[EffectClass::Exec, EffectClass::Net]),
                is_irreversible(&[EffectClass::Unknown]),
            ),
            (false, false, true, true)
        );
    }

    #[test]
    fn recording_answers_the_known_id_or_the_next_one() {
        let ledger = [entry(1, "s:a:0", 1), entry(2, "s:b:0", 2)];
        assert_eq!(
            (
                record(&[], "s:a:0").unwrap(),
                record(&ledger, "s:b:0").unwrap(),
                record(&ledger, "s:c:1").unwrap(),
            ),
            (Recorded::New(1), Recorded::Known(2), Recorded::New(3))
        );
    }

    #[test]
    fn the_end_list_is_the_runs_entries_in_order() {
        let ledger = [
            entry(1, "s:a:0", 1),
            entry(2, "s:b:0", 2),
            entry(3, "s:c:0", 1),
        ];
        assert_eq!(
            (
                this_run(&ledger, 1).unwrap(),
                this_run(&ledger, 2).unwrap(),
                this_run(&ledger, 3).unwrap(),
            ),
            (vec![1, 3], vec![2], vec![])
        );
    }
}
