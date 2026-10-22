//! The Director stack as pure functions, rule for rule as its model
//! (`bend/director.bend`, whose laws `PROOF.bend` proves): [`decide`] is
//! one decision of the stack, [`Loop::tick`] one step of the loop. The
//! bridge (`bridge.rs`) runs both on the same scenarios as the model.

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

/// What a decision gives the loop.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub enum Outcome {
    /// The loop goes on.
    Continue,
    /// The loop stops; the user has control.
    Hand,
    /// The loop stops with a failure.
    Failed,
}

/// One decision: what the loop does, and the stack after it (bottom
/// first).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Decision {
    pub outcome: Outcome,
    pub stack: Vec<Layer>,
}

/// One decision of `stack` (bottom first) on `verdicts` (top first; a
/// layer with no verdict defers), with room for `cap` layers, when the
/// loop goes on: a layer that leads leaves ([`Verdict::Lead`]).
#[must_use]
pub fn decide(stack: &[Layer], verdicts: &[Verdict], cap: usize) -> Decision {
    decide_as(stack, verdicts, cap, false)
}

/// One decision of `stack`. The top layer decides first; a layer that
/// defers stays, a layer that leaves goes, a layer that leads stays when
/// `stay` holds (the loop ends) and goes otherwise, and the first other
/// verdict decides. A push needs room in the whole stack: the layers above
/// the pushing one (those that deferred, left or led included), itself,
/// and the layers below.
fn decide_as(stack: &[Layer], verdicts: &[Verdict], cap: usize, stay: bool) -> Decision {
    let room = stack.len() < cap;
    // The layers above the deciding one that stayed, top first.
    let mut kept: Vec<&Layer> = Vec::new();
    for (above, layer) in stack.iter().rev().enumerate() {
        let rest = &stack[..stack.len() - 1 - above];
        let decided = match verdicts.get(above).unwrap_or(&Verdict::Defer) {
            Verdict::Defer => {
                kept.push(layer);
                continue;
            }
            Verdict::Lead => {
                if stay {
                    kept.push(layer);
                }
                continue;
            }
            Verdict::Leave => continue,
            Verdict::Yield => (Outcome::Hand, vec![layer.clone()]),
            Verdict::Abort => (Outcome::Failed, vec![layer.clone()]),
            Verdict::Again => match layer.budget {
                0 => (Outcome::Hand, vec![layer.clone()]),
                budget => (
                    Outcome::Continue,
                    vec![Layer {
                        kind: layer.kind.clone(),
                        budget: budget - 1,
                    }],
                ),
            },
            Verdict::Stack(pushed) => match layer.budget {
                0 => (Outcome::Hand, vec![layer.clone()]),
                budget => {
                    let spent = Layer {
                        kind: layer.kind.clone(),
                        budget: budget - 1,
                    };
                    if room {
                        (Outcome::Continue, vec![spent, pushed.clone()])
                    } else {
                        (Outcome::Failed, vec![spent])
                    }
                }
            },
        };
        let (outcome, top) = decided;
        let stack = rest
            .iter()
            .cloned()
            .chain(top)
            .chain(kept.into_iter().rev().cloned())
            .collect();
        return Decision { outcome, stack };
    }
    Decision {
        outcome: Outcome::Hand,
        stack: kept.into_iter().rev().cloned().collect(),
    }
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
    /// One step: the stack decides on `verdicts`. A continue with a step
    /// left goes on (a layer that leads leaves with it); a continue with no
    /// step left yields; a hand back or a failure ends the loop. A loop that
    /// ends keeps the layers that lead. An ended loop stays as it ended.
    #[must_use]
    pub fn tick(self, verdicts: &[Verdict], cap: usize) -> Self {
        if self.end.is_some() {
            return self;
        }
        let Decision { outcome, stack } = decide(&self.stack, verdicts, cap);
        let kept = || decide_as(&self.stack, verdicts, cap, true).stack;
        match (outcome, self.left) {
            (Outcome::Continue, 0) => Self {
                left: 0,
                stack: kept(),
                end: Some(End::Hand),
            },
            (Outcome::Continue, left) => Self {
                left: left - 1,
                stack,
                end: None,
            },
            (Outcome::Hand, left) => Self {
                left,
                stack: kept(),
                end: Some(End::Hand),
            },
            (Outcome::Failed, left) => Self {
                left,
                stack: kept(),
                end: Some(End::Failed),
            },
        }
    }
}
