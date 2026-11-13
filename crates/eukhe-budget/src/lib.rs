//! Budgets as hard guarantees (spec/README.md B1-B11).
//!
//! A task tree's budget limits money, tokens, tool calls and model
//! requests, which are spent, and wall-clock time, a deadline for the
//! whole tree that survives restarts. Its [`Ledger`] is an append-only
//! file per account that every process of the tree reaches under a file
//! lock. The tree's root owns an account; a child without a budget of its
//! own draws from the account of the agent above it (a member of it, with
//! its own phase), so the tree's total never passes the budget and no
//! child takes the final-answer reserve of an agent above it. A child
//! given a budget of its own gets an account carved out of its parent's,
//! and what it leaves returns when it ends.
//!
//! Nothing is spent before its worst case is reserved and written to the
//! ledger; the actual spend settles the reservation afterwards; a
//! reservation left open by a crash is settled at its held amount.
//!
//! Every decision (does it fit and end by the deadline, which reduced
//! offer, what returns, which phase follows) is made by the compiled Bend
//! core (`eukhe_bend::rules::budget`, model `bend/budget.bend`, laws
//! `laws/budget.bend`). This crate gathers the facts, keeps the files and
//! does the IO.

mod amounts;
mod ledger;
mod record;
mod worst;

pub use amounts::{limits_of, mask};
pub use ledger::{
    Audit, CarveOutcome, Ledger, LedgerError, ReclaimOutcome, Refusal, Reservation, Reserved, Use,
    FINAL_MIN_MS, REQUEST_MIN_MS, TOOL_MIN_MS,
};
pub use record::{
    Account, ChildCarve, HoldRecord, Member, Op, Outcome, ParentRef, Record, RefusalRecord,
    RunRecord, State, UseRecord, PROGRAM_LABEL,
};
pub use worst::{actual_spend, micros_ceil, worst_case_cost_micros, RequestBound};
