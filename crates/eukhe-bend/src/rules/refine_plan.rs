//! The decisions of the /refine planner (`bend/refine_plan.bend`, entry
//! `bend/ffi_refine_plan.bend`; `laws/refine_plan/`): the id an edit names,
//! which edit of a proposal applies with its row and message, the change
//! lines, the edits that roll a result back, a proposal's default texts,
//! whether a JSON candidate was cut off, and one step of fitting a
//! refinement request into the model's context window. Rust reads the JSON
//! and gives the facts; it keeps the state and mutates it as the plan says.

use crate::wire::{Reader, WireError, Writer, NAT_MAX};
use crate::{call, expect_core, Entry, Error};

/// An edit's action.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Verb {
    Create,
    Update,
    Delete,
}

/// A continual harness component.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Comp {
    Prompt,
    Memory,
    Skill,
    Subagent,
    Factory,
}

/// A factory spec key's JSON value (`dag`, `machine`).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Val {
    Missing,
    Null,
    Object,
    Other,
}

/// The string fields of a skill reference (none: absent or not a JSON
/// string).
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct Pyref {
    pub ty: Option<String>,
    pub import: Option<String>,
    pub python_import: Option<String>,
    pub callable: Option<String>,
    pub call_pattern: Option<String>,
}

/// The factory spec keys of an edit's arguments.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Args {
    pub dag: Val,
    pub machine: Val,
}

/// One proposed edit and the facts of its entry.
#[derive(Debug, Clone, PartialEq, Eq)]
#[allow(clippy::struct_excessive_bools)] // the independent facts of the wire's edit record
pub struct Ed {
    pub verb: Option<Verb>,
    pub comp: Option<Comp>,
    pub id: Option<String>,
    pub title: Option<String>,
    /// Whether the edit has content.
    pub content: bool,
    pub pyref: Option<Pyref>,
    pub args: Option<Args>,
    /// Whether its entry is stored (the state the proposal starts from).
    pub exists: bool,
    /// Whether the stored entry differs from the planning baseline's.
    pub differs: bool,
    /// Whether the session's memory holds its kind.
    pub held: bool,
}

/// The options of an apply.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Opts {
    /// The factory opt-in.
    pub factory: bool,
    /// A planning baseline is given.
    pub baseline: bool,
}

/// What an edit does.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Out {
    /// Refused by validation: no entry shown.
    Invalid(String),
    /// Refused after validation: the entry before it is shown.
    Refused(String),
    /// The entry is removed.
    Removed,
    /// The entry is written.
    Written,
}

/// One edit's row of the result.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Row {
    pub verb: Verb,
    pub comp: Comp,
    pub id: String,
    pub out: Out,
}

/// A proposal's rows and change lines.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Plan {
    pub rows: Vec<Row>,
    pub changes: Vec<String>,
}

/// A row of the result rolled back.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Was {
    pub applied: bool,
    pub before: bool,
    pub after: bool,
}

/// A rollback edit: the row it reverts and its action.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Pick {
    pub at: usize,
    pub verb: Verb,
}

/// A rollback proposal.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Back {
    pub summary: String,
    pub rationale: String,
    pub outcome: String,
    /// Every rollback edit's reason.
    pub reason: String,
    pub picks: Vec<Pick>,
}

/// A proposal's texts.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Texts {
    pub summary: String,
    pub rationale: String,
    pub outcome: String,
}

/// A model's window, in tokens (the system prompt's length in UTF-8
/// bytes, one token each).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Win {
    pub window: u64,
    pub max: u64,
    pub reserve: u64,
    pub system: u64,
}

/// Where the fit's walk is: the full prompt measured, a trimmed one
/// measured, the final one measured.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Search {
    Full,
    Probe { low: u64, high: u64, len: u64 },
    Final,
}

/// The fit's next step.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Step {
    /// Build and measure the prompt of the conversation's last `len`
    /// bytes, then ask again with `next`.
    Try { len: u64, next: Search },
    /// The request's max output tokens.
    Fits(u64),
    /// No room for output: the refusal text.
    NoRoom(String),
}

/// The question tags of the entry.
const IDS: u32 = 0;
const PLAN: u32 = 1;
const BACK: u32 = 2;
const NORM: u32 = 3;
const SCAN: u32 = 4;
const FIT: u32 = 5;

/// The id each edit names: its id, else a create's slug of its title.
#[must_use]
pub fn ids(eds: &[Ed]) -> Vec<Option<String>> {
    expect_core(Entry::RefinePlan, ids_call(eds))
}

/// The rows and change lines of a proposal's edits, in order.
#[must_use]
pub fn plan(opts: Opts, eds: &[Ed]) -> Plan {
    expect_core(Entry::RefinePlan, plan_call(opts, eds))
}

/// The rollback of a result with id `id` and these rows.
#[must_use]
pub fn back(id: &str, was: &[Was]) -> Back {
    expect_core(Entry::RefinePlan, back_call(id, was))
}

/// A proposal's texts: each given one, else its default.
#[must_use]
pub fn norm(summary: Option<&str>, rationale: Option<&str>, outcome: Option<&str>) -> Texts {
    expect_core(Entry::RefinePlan, norm_call(summary, rationale, outcome))
}

/// Whether a JSON candidate ends mid-value (in a string, or with brackets
/// left open).
#[must_use]
pub fn incomplete(text: &str) -> bool {
    expect_core(Entry::RefinePlan, scan_call(text))
}

/// One step of fitting a refinement request: the window, the
/// conversation's length, where the walk is and the length of the prompt
/// last built (lengths in UTF-8 bytes). Every number saturates at the
/// wire's largest Nat ([`NAT_MAX`], about 10^14 tokens).
#[must_use]
pub fn fit(win: Win, conv: u64, search: Search, plen: u64) -> Step {
    expect_core(Entry::RefinePlan, fit_call(win, conv, search, plen))
}

fn maybe_str(writer: &mut Writer, value: Option<&str>) {
    match value {
        Some(value) => writer.some().str(value),
        None => writer.none(),
    };
}

fn put_ed(writer: &mut Writer, ed: &Ed) {
    match ed.verb {
        Some(verb) => writer.some().tag(verb_tag(verb)),
        None => writer.none(),
    };
    match ed.comp {
        Some(comp) => writer.some().tag(comp_tag(comp)),
        None => writer.none(),
    };
    maybe_str(writer, ed.id.as_deref());
    maybe_str(writer, ed.title.as_deref());
    writer.bool(ed.content);
    match &ed.pyref {
        Some(pyref) => {
            writer.some();
            maybe_str(writer, pyref.ty.as_deref());
            maybe_str(writer, pyref.import.as_deref());
            maybe_str(writer, pyref.python_import.as_deref());
            maybe_str(writer, pyref.callable.as_deref());
            maybe_str(writer, pyref.call_pattern.as_deref());
        }
        None => {
            writer.none();
        }
    }
    match ed.args {
        Some(args) => writer
            .some()
            .tag(val_tag(args.dag))
            .tag(val_tag(args.machine)),
        None => writer.none(),
    };
    writer.bool(ed.exists).bool(ed.differs).bool(ed.held);
}

fn put_eds(writer: &mut Writer, eds: &[Ed]) {
    writer.count(eds.len());
    for ed in eds {
        put_ed(writer, ed);
    }
}

fn verb_tag(verb: Verb) -> u32 {
    match verb {
        Verb::Create => 0,
        Verb::Update => 1,
        Verb::Delete => 2,
    }
}

fn comp_tag(comp: Comp) -> u32 {
    match comp {
        Comp::Prompt => 0,
        Comp::Memory => 1,
        Comp::Skill => 2,
        Comp::Subagent => 3,
        Comp::Factory => 4,
    }
}

fn val_tag(val: Val) -> u32 {
    match val {
        Val::Missing => 0,
        Val::Null => 1,
        Val::Object => 2,
        Val::Other => 3,
    }
}

fn read_verb(reader: &mut Reader<'_>) -> Result<Verb, WireError> {
    Ok(match reader.tag_of(3, "an action (0 to 2)")? {
        0 => Verb::Create,
        1 => Verb::Update,
        // `tag_of` answers a tag below 3: this is 2.
        _ => Verb::Delete,
    })
}

fn read_comp(reader: &mut Reader<'_>) -> Result<Comp, WireError> {
    Ok(match reader.tag_of(5, "a kind (0 to 4)")? {
        0 => Comp::Prompt,
        1 => Comp::Memory,
        2 => Comp::Skill,
        3 => Comp::Subagent,
        // `tag_of` answers a tag below 5: this is 4.
        _ => Comp::Factory,
    })
}

fn read_search(reader: &mut Reader<'_>) -> Result<Search, WireError> {
    Ok(match reader.tag_of(3, "a fit walk (0 to 2)")? {
        0 => Search::Full,
        1 => Search::Probe {
            low: reader.nat()?,
            high: reader.nat()?,
            len: reader.nat()?,
        },
        // `tag_of` answers a tag below 3: this is 2.
        _ => Search::Final,
    })
}

fn read_strs(reader: &mut Reader<'_>) -> Result<Vec<String>, WireError> {
    let n = reader.count()?;
    let mut out = Vec::with_capacity(n);
    for _ in 0..n {
        out.push(reader.str()?.to_string());
    }
    Ok(out)
}

fn ids_call(eds: &[Ed]) -> Result<Vec<Option<String>>, Error> {
    let mut writer = Writer::new();
    writer.tag(IDS);
    put_eds(&mut writer, eds);
    let reply = call(Entry::RefinePlan, &writer.finish()?)?;
    let mut reader = Reader::reply(&reply)?;
    let n = reader.count()?;
    let mut out = Vec::with_capacity(n);
    for _ in 0..n {
        out.push(if reader.maybe()? {
            Some(reader.str()?.to_string())
        } else {
            None
        });
    }
    reader.end()?;
    Ok(out)
}

fn plan_call(opts: Opts, eds: &[Ed]) -> Result<Plan, Error> {
    let mut writer = Writer::new();
    writer.tag(PLAN).bool(opts.factory).bool(opts.baseline);
    put_eds(&mut writer, eds);
    let reply = call(Entry::RefinePlan, &writer.finish()?)?;
    let mut reader = Reader::reply(&reply)?;
    let n = reader.count()?;
    let mut rows = Vec::with_capacity(n);
    for _ in 0..n {
        let verb = read_verb(&mut reader)?;
        let comp = read_comp(&mut reader)?;
        let id = reader.str()?.to_string();
        let out = match reader.tag_of(4, "an edit's outcome (0 to 3)")? {
            0 => Out::Invalid(reader.str()?.to_string()),
            1 => Out::Refused(reader.str()?.to_string()),
            2 => Out::Removed,
            // `tag_of` answers a tag below 4: this is 3.
            _ => Out::Written,
        };
        rows.push(Row {
            verb,
            comp,
            id,
            out,
        });
    }
    let changes = read_strs(&mut reader)?;
    reader.end()?;
    Ok(Plan { rows, changes })
}

fn back_call(id: &str, was: &[Was]) -> Result<Back, Error> {
    let mut writer = Writer::new();
    writer.tag(BACK).str(id).count(was.len());
    for row in was {
        writer.bool(row.applied).bool(row.before).bool(row.after);
    }
    let reply = call(Entry::RefinePlan, &writer.finish()?)?;
    let mut reader = Reader::reply(&reply)?;
    let summary = reader.str()?.to_string();
    let rationale = reader.str()?.to_string();
    let outcome = reader.str()?.to_string();
    let reason = reader.str()?.to_string();
    let n = reader.count()?;
    let mut picks = Vec::with_capacity(n);
    for _ in 0..n {
        let at = reader.count()?;
        if at >= was.len() {
            return Err(WireError::Malformed {
                at: 0,
                expected: "a rollback row index below the row count",
            }
            .into());
        }
        picks.push(Pick {
            at,
            verb: read_verb(&mut reader)?,
        });
    }
    reader.end()?;
    Ok(Back {
        summary,
        rationale,
        outcome,
        reason,
        picks,
    })
}

fn norm_call(
    summary: Option<&str>,
    rationale: Option<&str>,
    outcome: Option<&str>,
) -> Result<Texts, Error> {
    let mut writer = Writer::new();
    writer.tag(NORM);
    maybe_str(&mut writer, summary);
    maybe_str(&mut writer, rationale);
    maybe_str(&mut writer, outcome);
    let reply = call(Entry::RefinePlan, &writer.finish()?)?;
    let mut reader = Reader::reply(&reply)?;
    let texts = Texts {
        summary: reader.str()?.to_string(),
        rationale: reader.str()?.to_string(),
        outcome: reader.str()?.to_string(),
    };
    reader.end()?;
    Ok(texts)
}

fn scan_call(text: &str) -> Result<bool, Error> {
    let reply = call(
        Entry::RefinePlan,
        &Writer::new().tag(SCAN).str(text).finish()?,
    )?;
    let mut reader = Reader::reply(&reply)?;
    let cut = reader.bool()?;
    reader.end()?;
    Ok(cut)
}

fn fit_call(win: Win, conv: u64, search: Search, plen: u64) -> Result<Step, Error> {
    let mut writer = Writer::new();
    writer
        .tag(FIT)
        .nat(win.window.min(NAT_MAX))
        .nat(win.max.min(NAT_MAX))
        .nat(win.reserve.min(NAT_MAX))
        .nat(win.system.min(NAT_MAX))
        .nat(conv.min(NAT_MAX));
    match search {
        Search::Full => writer.tag(0),
        Search::Probe { low, high, len } => writer
            .tag(1)
            .nat(low.min(NAT_MAX))
            .nat(high.min(NAT_MAX))
            .nat(len.min(NAT_MAX)),
        Search::Final => writer.tag(2),
    };
    writer.nat(plen.min(NAT_MAX));
    let reply = call(Entry::RefinePlan, &writer.finish()?)?;
    let mut reader = Reader::reply(&reply)?;
    let step = match reader.tag_of(3, "a fit step (0 to 2)")? {
        0 => Step::Try {
            len: reader.nat()?,
            next: read_search(&mut reader)?,
        },
        1 => Step::Fits(reader.nat()?),
        // `tag_of` answers a tag below 3: this is 2.
        _ => Step::NoRoom(reader.str()?.to_string()),
    };
    reader.end()?;
    Ok(step)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn memory(verb: Verb, id: &str, exists: bool) -> Ed {
        Ed {
            verb: Some(verb),
            comp: Some(Comp::Memory),
            id: Some(id.to_string()),
            title: Some("Fact".to_string()),
            content: true,
            pyref: None,
            args: None,
            exists,
            differs: false,
            held: true,
        }
    }

    /// Each question reaches the compiled core: ids, a plan that sees its
    /// own earlier edits, a rollback, the default texts, a cut-off reply
    /// and one fit step.
    #[test]
    fn the_core_plans_a_refinement() {
        let mut slugged = memory(Verb::Create, "", false);
        slugged.id = None;
        slugged.title = Some("Build Notes!".to_string());
        assert_eq!(
            ids(&[memory(Verb::Update, "m1", true), slugged]),
            vec![Some("m1".to_string()), Some("build_notes".to_string())]
        );
        let planned = plan(
            Opts {
                factory: false,
                baseline: false,
            },
            &[
                memory(Verb::Create, "m1", false),
                memory(Verb::Create, "m1", false),
            ],
        );
        assert_eq!(
            planned.rows.iter().map(|row| &row.out).collect::<Vec<_>>(),
            vec![
                &Out::Written,
                &Out::Refused("entry already exists".to_string())
            ]
        );
        assert_eq!(planned.changes, vec!["create memory:m1".to_string()]);
        let rollback = back(
            "r1",
            &[Was {
                applied: true,
                before: false,
                after: true,
            }],
        );
        assert_eq!(
            rollback.picks,
            vec![Pick {
                at: 0,
                verb: Verb::Delete
            }]
        );
        assert_eq!(rollback.reason, "Rollback r1");
        assert_eq!(
            norm(None, Some("r"), None).summary,
            "Refined continual harness state"
        );
        assert!(incomplete(r#"{"edits":[{"action":"cre"#));
        assert!(!incomplete(r#"{"edits":[]}"#));
        assert_eq!(
            fit(
                Win {
                    window: u64::MAX,
                    max: 32_000,
                    reserve: 32_000,
                    system: 10
                },
                0,
                Search::Full,
                100
            ),
            Step::Fits(32_000)
        );
    }
}
