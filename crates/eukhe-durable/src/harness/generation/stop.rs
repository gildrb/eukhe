//! The Directors at a candidate stop (omp2 ADR 0015; the model
//! `bend/stop.bend`, entry `bend/ffi_stop.bend`, laws `laws/stop.bend`): a
//! reply that ends the model's turn with no tool call is walked through
//! `LengthStop`, `EmptyStop`, `MarkupStop` and `PendingWork`, inside to
//! outside. The first that does not pass decides: a Director that
//! continues the run is the recovery [`super::decide::recover`] caps
//! ([`Stuck`]); `PendingWork` yields, so a stop while the session owns
//! running work is a pause that their ends wake, and `LengthStop` yields
//! at a reply cut at the output limit with text and room left in the
//! window, so the truncated reply is kept as the answer. With every
//! Director passing, the reply is the answer, whatever its text says.
//! Rust gathers the facts; the compiled core picks, and writes the round
//! cap's note.

use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::Arc;

use eukhe_bend::wire::{Reader, WireError, Writer};
use eukhe_bend::{call, expect_core, Entry};
use eukhe_chord::context::Context;

use super::decide::Stuck;
use super::entry::{mismatch, saturated};
use super::Runtime;
use crate::harness::types::GenerationHooks;
use crate::session::SessionResult;

/// What a candidate stop holds, as the stop entry reads it (`AskWalk` of
/// `bend/ffi_stop.bend`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct Facts {
    /// The reply hit the output limit: what the walk and the ladder of a
    /// length stop read about its window.
    pub(crate) cut: Option<Cut>,
    /// The reply has a text block that is not blank.
    pub(crate) text: bool,
    /// Tool-call markup in the text that the harness could not read.
    pub(crate) broken: bool,
    /// The session owns running work whose end wakes it.
    pub(crate) pending: bool,
}

/// The window at a reply that hit the output limit: the model's context
/// window (0 when unknown) and catalog max output, the reply's prompt and
/// output tokens, whether a compaction can run (`cuttable`: compaction on,
/// a cut, the generation has not compacted) and whether a thinking level
/// below the agent's exists (`lower`). The walk reads from it whether the
/// window is what ran out and a compaction makes room (`full` of
/// `bend/stop.bend`); the ladder reads the same facts ([`Stuck::Thought`]).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct Cut {
    pub(crate) window: u64,
    pub(crate) catalog: u64,
    pub(crate) prompt: u64,
    pub(crate) output: u64,
    pub(crate) cuttable: bool,
    pub(crate) lower: bool,
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
/// `stop_walk_refines`, `stop_pending_never_continues`, and for a reply
/// that hit the output limit `stop_cut_empty_never_stands`,
/// `stop_cut_text_stands_unless_full`). A reply that was not cut has no
/// window: the entry reads 0s.
pub(crate) fn walk(facts: Facts) -> Option<Stuck> {
    let window = facts.cut.unwrap_or(Cut {
        window: 0,
        catalog: 0,
        prompt: 0,
        output: 0,
        cuttable: false,
        lower: false,
    });
    ask(
        |w| {
            w.tag(0)
                .bool(facts.cut.is_some())
                .bool(facts.text)
                .bool(facts.broken)
                .bool(facts.pending)
                .nat(saturated(window.window))
                .nat(saturated(window.catalog))
                .nat(saturated(window.prompt))
                .nat(saturated(window.output))
                .bool(window.cuttable);
        },
        |r| match r.tag_of(5, "a stop pick")? {
            0 => Ok(None),
            1 => facts
                .cut
                .map(|cut| {
                    Some(Stuck::Thought {
                        window: cut.window,
                        catalog: cut.catalog,
                        prompt: cut.prompt,
                        output: cut.output,
                        cuttable: cut.cuttable,
                        lower: cut.lower,
                    })
                })
                .ok_or_else(|| mismatch("no LengthStop at a reply that was not cut")),
            2 => Ok(Some(Stuck::Empty)),
            3 => Ok(Some(Stuck::Leak)),
            4..=u32::MAX => Err(mismatch("a Director that continues")),
        },
    )
}

/// The note that ends a request after `done` tool rounds of the run's
/// `max` (`maxToolRounds`): the rounds left, once few remain (law
/// `stop_rounds_exact`).
pub(crate) fn rounds_note(max: u32, done: u32) -> Option<String> {
    ask(
        |w| {
            w.tag(1).nat(u64::from(max)).nat(u64::from(done));
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
