//! The Director stack: its layers, verdicts and loop, and one step of the
//! loop ([`Loop::tick`]), which runs as the compiled model
//! (`bend/director.bend`, whose laws `PROOF.bend` proves; entry
//! `bend/ffi_director.bend`).

use eukhe_bend::wire::{Reader, WireError, Writer, NAT_MAX};
use eukhe_bend::{call, expect_core, Entry};
use serde::{Deserialize, Serialize};

/// What a layer is (the model's `kind`).
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "type", rename_all = "camelCase")]
pub enum LayerKind {
    /// The conversation's goal (`eukhe.goal`).
    Goal,
    /// The conversation's autonomous run (`eukhe.autonomous`).
    Autonomous,
    /// A reminder: its text leads the next continuation, then it leaves.
    /// While no continuation comes, it stays.
    Reminder { text: String },
    /// A forced tool call: the requests force `tool` (with `tries`
    /// requests after the first, `stream.forceTool`) until the model calls
    /// it.
    #[serde(rename_all = "camelCase")]
    ForceTool {
        tool: String,
        tries: u32,
        /// A response called `tool` after the layer came on the stack.
        #[serde(default)]
        called: bool,
        /// The forced requests whose responses did not call `tool`.
        #[serde(default)]
        missed: u32,
    },
}

impl LayerKind {
    /// The kind's number in the model's tree encoding.
    #[must_use]
    pub fn code(&self) -> u64 {
        match self {
            Self::Goal => 0,
            Self::Autonomous => 1,
            Self::Reminder { .. } => 2,
            Self::ForceTool { .. } => 3,
        }
    }

    /// Whether a push puts the kind on the stack (a reminder, a forced
    /// call), not the goal or autonomous state.
    #[must_use]
    pub fn is_pushed(&self) -> bool {
        match self {
            Self::Reminder { .. } | Self::ForceTool { .. } => true,
            Self::Goal | Self::Autonomous => false,
        }
    }
}

/// One Director: its kind and the loop steps it may still ask for.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct Layer {
    pub kind: LayerKind,
    pub budget: u64,
}

impl Layer {
    /// A reminder of `text`. It never asks for a step, so it has no
    /// budget.
    #[must_use]
    pub fn reminder(text: String) -> Self {
        Self {
            kind: LayerKind::Reminder { text },
            budget: 0,
        }
    }

    /// A forced call of `tool`, with `tries` retries per forced run and
    /// one forced continuation when a run ends before a request forced it.
    #[must_use]
    pub fn force_tool(tool: String, tries: u32) -> Self {
        Self {
            kind: LayerKind::ForceTool {
                tool,
                tries,
                called: false,
                missed: 0,
            },
            budget: 1,
        }
    }
}

/// What one layer says at one step.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Verdict {
    /// The next layer down decides.
    Defer,
    /// The loop goes on; it costs the layer one unit of budget (with none
    /// left, the loop yields).
    Again,
    /// The loop stops and hands back to the user.
    Yield,
    /// The layer puts a layer on top of itself and the loop goes on; it
    /// costs one unit of budget. A stack with no room fails.
    Stack(Layer),
    /// The layer removes itself; the next layer down decides.
    Leave,
    /// The loop stops with a failure.
    Abort,
    /// A reminder that leads the next continuation: it leaves with the
    /// continuation (the loop goes on), and stays when the loop ends. Either
    /// way the next layer down decides.
    Lead,
}

/// How a loop ended.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub enum End {
    /// It handed back to the user.
    Hand,
    /// It failed.
    Failed,
}

/// The loop: the global budget of steps left, the stack (bottom first),
/// and how it ended (`None` while it runs).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Loop {
    pub left: u64,
    pub stack: Vec<Layer>,
    pub end: Option<End>,
}

impl Loop {
    /// One step: the stack decides on `verdicts` (top first; a layer with
    /// no verdict defers), with room for `cap` layers. The step is
    /// `bend/director.bend` `tick`, run as the compiled core: the layers'
    /// kinds cross as numbers (each layer of the stack, then each layer a
    /// verdict pushes, numbered in turn), and `left`, the budgets and `cap`
    /// are counts saturated at [`NAT_MAX`] (a count that large never runs
    /// out). A continue with a step left goes on (a layer that leads leaves
    /// with it); a continue with no step left yields; a hand back or a
    /// failure ends the loop, and the layers that lead stay. An ended loop
    /// stays as it ended.
    #[must_use]
    pub fn tick(self, verdicts: &[Verdict], cap: usize) -> Self {
        let count = |n: u64| n.min(NAT_MAX);
        let mut kinds: Vec<&LayerKind> = self.stack.iter().map(|layer| &layer.kind).collect();
        let mut w = Writer::new();
        w.nat(u64::try_from(cap).map_or(NAT_MAX, count));
        w.nat(count(self.left)).count(self.stack.len());
        for (at, layer) in self.stack.iter().enumerate().rev() {
            w.count(at).nat(count(layer.budget));
        }
        match self.end {
            None => w.none(),
            Some(End::Hand) => w.some().tag(1),
            Some(End::Failed) => w.some().tag(2),
        };
        w.count(verdicts.len());
        for verdict in verdicts {
            match verdict {
                Verdict::Defer => w.tag(0),
                Verdict::Again => w.tag(1),
                Verdict::Yield => w.tag(2),
                Verdict::Stack(pushed) => {
                    let at = kinds.len();
                    kinds.push(&pushed.kind);
                    w.tag(3).count(at).nat(count(pushed.budget))
                }
                Verdict::Leave => w.tag(4),
                Verdict::Abort => w.tag(5),
                Verdict::Lead => w.tag(6),
            };
        }
        let request = expect_core(Entry::Director, w.finish());
        let reply = expect_core(Entry::Director, call(Entry::Director, &request));
        expect_core(Entry::Director, read_loop(&reply, &kinds))
    }
}

/// The loop a reply holds, its layers' kinds numbered as in `kinds`.
fn read_loop(reply: &str, kinds: &[&LayerKind]) -> Result<Loop, WireError> {
    let mut r = Reader::reply(reply)?;
    let left = r.nat()?;
    let layers = r.count()?;
    let mut stack = Vec::with_capacity(layers);
    for _ in 0..layers {
        let kind = r.count()?;
        let budget = r.nat()?;
        let kind = kinds.get(kind).ok_or(WireError::Malformed {
            at: 0,
            expected: "the number of a layer's kind",
        })?;
        stack.push(Layer {
            kind: (*kind).clone(),
            budget,
        });
    }
    // The model's stack is top first.
    stack.reverse();
    let end = if r.maybe()? {
        // The model ends a loop only by handing back (1) or failing (2).
        let at = reply.len();
        match r.tag_of(3, "an outcome")? {
            1 => Some(End::Hand),
            2 => Some(End::Failed),
            _ => {
                return Err(WireError::Malformed {
                    at,
                    expected: "the end of a loop (a hand back or a failure)",
                })
            }
        }
    } else {
        None
    };
    r.end()?;
    Ok(Loop { left, stack, end })
}
