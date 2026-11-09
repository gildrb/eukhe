//! The Directors at a candidate stop (omp2 ADR 0015; the model
//! `bend/stop.bend`, entry `bend/ffi_stop.bend`, laws `laws/stop.bend`): a
//! reply that ends the model's turn with no tool call is walked through
//! `LengthStop`, `EmptyStop`, `MarkupStop` and `PendingWork`, inside to
//! outside. The first that does not pass decides: a Director that
//! continues the run is the recovery [`super::decide::recover`] caps
//! ([`Stuck`]); `PendingWork` yields, so a stop while the session owns
//! running work is a pause that their ends wake. With every Director
//! passing, the reply is the answer, whatever its text says. Rust gathers
//! the facts; the compiled core picks, writes the reminders, and the round
//! cap's note.

use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::Arc;

use eukhe_bend::wire::{Reader, WireError, Writer, NAT_MAX};
use eukhe_bend::{call, expect_core, Entry};
use eukhe_chord::context::Context;

use super::decide::Stuck;
use super::entry::mismatch;
use super::Runtime;
use crate::harness::types::GenerationHooks;
use crate::session::SessionResult;

/// What a candidate stop holds (`Facts` of `bend/stop.bend`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[expect(
    clippy::struct_excessive_bools,
    reason = "the four independent facts of `Facts` in bend/stop.bend, as the entry reads them"
)]
pub(crate) struct Facts {
    /// The reply hit the output limit.
    pub(crate) cut: bool,
    /// The reply has a text block that is not blank.
    pub(crate) text: bool,
    /// Tool-call markup in the text that the harness could not read.
    pub(crate) broken: bool,
    /// The session owns running work whose end wakes it.
    pub(crate) pending: bool,
}

/// Whether the session owns running work whose end wakes it (the
/// `PendingWork` Director's fact): a `pending_work` hook says so. A hook
/// that cannot tell fails the generation, as any read of its facts does.
pub(super) async fn pending(runtime: &Runtime, cx: &Context) -> SessionResult<bool> {
    let pending = Arc::new(AtomicBool::new(false));
    let api = runtime.hook_api();
    runtime
        .hooks()
        .each_required(
            |hooks: &GenerationHooks| hooks.pending_work.clone(),
            |hook| {
                let asked = hook(&api, cx);
                let pending = Arc::clone(&pending);
                async move {
                    if asked.await? {
                        pending.store(true, Ordering::Relaxed);
                    }
                    Ok(())
                }
            },
        )
        .await?;
    Ok(pending.load(Ordering::Relaxed))
}

/// The reminder the stop Directors write (`Note` of `bend/stop.bend`): a
/// length stop with text, its limit (`tokens`, 0: not reported) and the
/// length note `row` of `cap`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct Note {
    pub(crate) tokens: u64,
    pub(crate) row: u32,
    pub(crate) cap: u32,
}

/// The answer of the stop entry to the request `write` writes, as `read`
/// reads it (the whole answer). eukhe encodes every request itself, within
/// the wire's bounds, so a failure can only be an inconsistent build.
fn ask<T>(
    write: impl FnOnce(&mut Writer),
    read: impl FnOnce(&mut Reader<'_>) -> Result<T, WireError>,
) -> T {
    let mut writer = Writer::new();
    write(&mut writer);
    let input = expect_core(Entry::Stop, writer.finish());
    let answer = expect_core(Entry::Stop, call(Entry::Stop, &input));
    expect_core(
        Entry::Stop,
        Reader::reply(&answer).and_then(|mut reader| {
            let value = read(&mut reader)?;
            reader.end()?;
            Ok(value)
        }),
    )
}

/// The Director that continues the run at the stop `facts`, as the
/// recovery that caps it; `None`: the stop stands (laws
/// `stop_walk_refines`, `stop_pending_never_continues`).
pub(crate) fn walk(facts: Facts) -> Option<Stuck> {
    ask(
        |w| {
            w.tag(0)
                .bool(facts.cut)
                .bool(facts.text)
                .bool(facts.broken)
                .bool(facts.pending);
        },
        |r| match r.tag_of(5, "a stop pick")? {
            0 => Ok(None),
            1 => Ok(Some(Stuck::Length)),
            2 => Ok(Some(Stuck::Empty)),
            3 => Ok(Some(Stuck::Leak)),
            4..=u32::MAX => Err(mismatch("a Director that continues")),
        },
    )
}

/// The text of `note` at the end of the request of `attempt` (laws
/// `stop_note_names_the_attempt`, `stop_texts_rust_example`).
pub(crate) fn note_text(attempt: u64, note: Note) -> String {
    ask(
        |w| {
            w.tag(1)
                .nat(attempt.min(NAT_MAX))
                .nat(note.tokens.min(NAT_MAX))
                .nat(u64::from(note.row))
                .nat(u64::from(note.cap));
        },
        |r| Ok(r.str()?.to_owned()),
    )
}

/// The note that ends a request after `done` tool rounds of the run's
/// `max` (`maxToolRounds`): the rounds left, once few remain (laws
/// `stop_rounds_quiet_while_many_left`, `stop_rounds_note_near_the_cap`).
pub(crate) fn rounds_note(max: u32, done: u32) -> Option<String> {
    ask(
        |w| {
            w.tag(2).nat(u64::from(max)).nat(u64::from(done));
        },
        |r| {
            if r.maybe()? {
                Ok(Some(r.str()?.to_owned()))
            } else {
                Ok(None)
            }
        },
    )
}
