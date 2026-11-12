//! A child's budget (spec/README.md B4). A child spawned without a budget
//! draws from its parent's account as a shared member: it joins the
//! account when its session opens (`BudgetGate::open`), nothing moves at
//! the spawn, and the account's total and the reserves of the agents above
//! it bound it. A spawn that names a `budget` carves that allotment out of
//! the parent's account for the child (a parent without a budget gives the
//! child an account of exactly that budget).
//!
//! The ledger and its decisions are `eukhe-budget`'s and the compiled
//! core's; this module says when: a spawn batch's named budgets are carved
//! all or none in the commit that admits it ([`allot`]), a child prompted
//! again after its last task ended joins the account again before the
//! prompt goes out ([`relend`]), a child task that ends gives its budget
//! back ([`give_back`]: a carved allotment is reclaimed, a shared member is
//! released), and a parent that opens gives back what a child no task
//! serves still holds ([`reconcile`]: a crash between a carve and its spawn
//! commit, or between a child's end and its give-back). A parent with no
//! budget passes through: one file lookup, no ledger appears.

use std::collections::HashSet;
use std::sync::Arc;

use anyhow::{anyhow, bail};
use eukhe_budget::{CarveOutcome, Ledger, LedgerError, Refusal};
use eukhe_chord::context::Context;
use eukhe_durable::harness::Harness;
use eukhe_durable::session::{SessionError, SessionResult};
use eukhe_durable::types::{ConversationQuery, Cursor};
use eukhe_types::budget::{BudgetDimension, BudgetLimits, BudgetReport, BUDGET_AMOUNT_MAX};
use serde_json::{Map, Value};

use super::registry::read_children;
use crate::durable::budget::BudgetGate;

/// Conversations per page of the open's scan.
const SCAN_PAGE_SIZE: usize = 256;
/// The keys of a spawn's `budget` argument.
const BUDGET_KEYS: [&str; 5] = ["cost_usd", "tokens", "time_s", "tool_calls", "requests"];

/// One child its spawner named a budget for: it gets that allotment before
/// it runs.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) struct Allotment {
    /// The child's durable session id: its ledger's name.
    pub(super) session_id: String,
    /// The budget its spawner named.
    pub(super) limits: BudgetLimits,
}

/// `value` times `scale` as a whole amount of a budget; `None` when it is
/// no number, negative, or past a budget's range.
#[expect(
    clippy::cast_precision_loss,
    clippy::cast_possible_truncation,
    clippy::cast_sign_loss,
    reason = "a whole amount from 0 to a budget's largest (13 digits, below 2^53)"
)]
fn scaled(value: &Value, scale: f64) -> Option<u64> {
    let amount = (value.as_f64()? * scale).round();
    (0.0..=BUDGET_AMOUNT_MAX as f64)
        .contains(&amount)
        .then_some(amount as u64)
}

/// The `budget` argument of a spawn (`{cost_usd?, tokens?, time_s?,
/// tool_calls?, requests?}`) as the limits of the child's allotment;
/// `None` when the spawn names none (the child draws from its parent's
/// account).
///
/// # Errors
///
/// `budget` is no object, has another key, or holds a value that is no
/// amount.
pub(super) fn named_budget(
    kwargs: &Map<String, Value>,
    operation: &str,
) -> anyhow::Result<Option<BudgetLimits>> {
    let budget = match kwargs.get("budget") {
        None | Some(Value::Null) => return Ok(None),
        Some(Value::Object(budget)) => budget,
        Some(_) => bail!(
            "{operation} budget must be an object {{cost_usd?, tokens?, time_s?, tool_calls?, requests?}}"
        ),
    };
    let mut unsupported: Vec<&str> = budget
        .keys()
        .map(String::as_str)
        .filter(|key| !BUDGET_KEYS.contains(key))
        .collect();
    if !unsupported.is_empty() {
        unsupported.sort_unstable();
        bail!(
            "Unsupported {operation} budget keys: {}",
            unsupported.join(", ")
        );
    }
    // A scale reads a number in the caller's unit (dollars, seconds);
    // none reads a whole count.
    let amount = |key: &str, scale: Option<f64>| match budget.get(key) {
        None | Some(Value::Null) => Ok(None),
        Some(value) => match scale {
            Some(scale) => scaled(value, scale),
            None => value.as_u64().filter(|count| *count <= BUDGET_AMOUNT_MAX),
        }
        .map(Some)
        .ok_or_else(|| match scale {
            Some(_) => anyhow!("{operation} budget {key} must be a non-negative number"),
            None => anyhow!("{operation} budget {key} must be a non-negative integer"),
        }),
    };
    let limits = BudgetLimits {
        cost_micros: amount("cost_usd", Some(1_000_000.0))?,
        tokens: amount("tokens", None)?,
        time_ms: amount("time_s", Some(1_000.0))?,
        tool_calls: amount("tool_calls", None)?,
        requests: amount("requests", None)?,
    };
    Ok((!limits.is_unlimited()).then_some(limits))
}

/// The refusal a spawn batch gets when its allotments do not fit.
fn refusal_text(refusal: Refusal, report: &BudgetReport) -> String {
    let short = match refusal {
        Refusal::Short(dimension) => dimension.label(),
        Refusal::Stopped => report
            .short
            .map_or("the budget is used up", BudgetDimension::label),
    };
    format!("Budget: the children's allotments do not fit what is left ({short})")
}

/// The blocking part of [`allot`]: the ledger's answers are on disk when
/// it returns. `Err` is the text the spawner reads.
fn carve_all(gate: &BudgetGate, children: &[Allotment]) -> Result<Vec<String>, String> {
    if !gate.ledger().exists() {
        // No account to carve from: each child gets an account of exactly
        // the budget its spawner named.
        let own = gate.ledger().path();
        let dir = own.parent().unwrap_or_else(|| std::path::Path::new("."));
        for child in children {
            match Ledger::of(dir, &child.session_id).open_root(child.limits) {
                // A child that already has its own budget keeps it.
                Ok(_) | Err(LedgerError::AlreadyOpen(_)) => {}
                Err(error) => return Err(error.to_string()),
            }
        }
        return Ok(Vec::new());
    }
    let lent = gate.lent_children().map_err(|error| error.to_string())?;
    let mut carved = Vec::with_capacity(children.len());
    let all = children
        .iter()
        .filter(|child| !lent.contains(&child.session_id))
        .try_for_each(|child| match gate.carve(&child.session_id, child.limits) {
            Ok(CarveOutcome::Carved { .. }) => {
                carved.push(child.session_id.clone());
                Ok(())
            }
            Ok(CarveOutcome::Refused { refusal, report }) => Err(refusal_text(refusal, &report)),
            Err(error) => Err(error.to_string()),
        });
    let Err(refused) = all else {
        return Ok(carved);
    };
    // All or none: what this batch already took goes back.
    for child in &carved {
        if let Err(error) = gate.reclaim(child, /*force*/ true) {
            tracing::warn!(%child, %error, "returning the allotment of a refused spawn batch");
        }
    }
    Err(refused)
}

/// Makes sure every child of `children` (each one its spawner named a
/// budget for) holds that allotment before it runs: each one this session
/// lends nothing to yet is carved its named budget, all of them or none.
/// Answers the children it carved.
///
/// # Errors
///
/// The allotments do not fit (`Budget: the children's allotments do not
/// fit what is left (<dimension>)`), a named budget leaves out a dimension
/// the account limits, or the ledger failed: nothing stays carved, and the
/// children must not start.
#[tracing::instrument(level = "debug", skip_all)]
pub(super) async fn allot(
    gate: &Arc<BudgetGate>,
    children: Vec<Allotment>,
) -> SessionResult<Vec<String>> {
    if children.is_empty() {
        return Ok(Vec::new());
    }
    let gate = Arc::clone(gate);
    match tokio::task::spawn_blocking(move || carve_all(&gate, &children)).await {
        Ok(Ok(carved)) => Ok(carved),
        Ok(Err(refused)) => Err(SessionError::error(refused)),
        Err(error) => Err(SessionError::error(format!(
            "the budget ledger task ended: {error}"
        ))),
    }
}

/// Before a prompt or a message reaches the existing child
/// `child_session_id`: a child that holds no allotment of this account and
/// is not one of its members (its last task ended and gave its budget
/// back) joins this session's account as a shared member, so the work the
/// words start has a budget. A child that still holds its allotment or its
/// membership, one with a live account of its own, and a session with no
/// budget change nothing.
///
/// # Errors
///
/// The ledger failed: the child has no budget, and the words must not be
/// sent as work.
pub async fn relend(gate: &Arc<BudgetGate>, child_session_id: &str) -> SessionResult<()> {
    let gate = Arc::clone(gate);
    let child = child_session_id.to_owned();
    let joined = tokio::task::spawn_blocking(move || {
        if !gate.ledger().exists() {
            return Ok(());
        }
        if gate.lent_children()?.contains(&child) || gate.members()?.contains_key(&child) {
            return Ok(());
        }
        match gate.admit_child(&child) {
            Ok(()) | Err(LedgerError::AlreadyOpen(_)) => Ok(()),
            Err(error) => Err(error),
        }
    })
    .await;
    match joined {
        Ok(Ok(())) => Ok(()),
        Ok(Err(error)) => Err(SessionError::error(format!(
            "the child session {child_session_id} did not join this task's budget: {error}"
        ))),
        Err(error) => Err(SessionError::error(format!(
            "the budget ledger task ended: {error}"
        ))),
    }
}

/// The child `child_session_id`'s work ended: it gives back what it holds
/// of this session's budget. A carved allotment is reclaimed (what it has
/// free returns, its spend becomes this account's, what it left in flight
/// is charged at what it held); a shared member is released (what it holds
/// settles at what it held, and it leaves the account). A child that holds
/// neither, and a session with no budget, change nothing.
///
/// # Errors
///
/// The ledger failed; the open's [`reconcile`] asks again.
#[tracing::instrument(level = "debug", skip(gate))]
pub(super) async fn give_back(gate: &Arc<BudgetGate>, child_session_id: &str) -> SessionResult<()> {
    let gate = Arc::clone(gate);
    let child = child_session_id.to_owned();
    let given = tokio::task::spawn_blocking(move || {
        if !gate.ledger().exists() {
            return Ok(());
        }
        if gate.lent_children()?.contains(&child) {
            return gate.reclaim(&child, /*force*/ true).map(drop);
        }
        let shared = gate
            .members()?
            .get(&child)
            .is_some_and(|member| member.parent.as_deref() == Some(gate.agent()));
        if shared {
            gate.release(&child)?;
        }
        Ok(())
    })
    .await;
    match given {
        Ok(Ok(())) => Ok(()),
        Ok(Err(error)) => Err(SessionError::error(format!(
            "giving back the budget of child session {child_session_id}: {error}"
        ))),
        Err(error) => Err(SessionError::error(format!(
            "the budget ledger task ended: {error}"
        ))),
    }
}

/// At a session's open, after its Harness is set and before it resumes:
/// gives back ([`give_back`]) the budget of every child of this session
/// that no task serves (no registry row of any conversation names it as
/// spawning or running): a child carved for a spawn whose commit never
/// landed, and a child that ended while its parent was down or crashed
/// before its give-back. A child with a live row keeps its budget: its
/// task's end gives it back. It must run before the Harness resumes: a
/// spawn admitted meanwhile is carved before its row exists.
///
/// # Errors
///
/// A ledger, storage or document read failure. What stayed out is asked
/// for again at the next open.
#[tracing::instrument(level = "debug", skip_all)]
pub async fn reconcile(
    gate: &Arc<BudgetGate>,
    harness: &Harness,
    cx: &Context,
) -> SessionResult<()> {
    let children = {
        let gate = Arc::clone(gate);
        tokio::task::spawn_blocking(move || {
            if !gate.ledger().exists() {
                return Ok(Vec::new());
            }
            let mut children = gate.lent_children()?;
            children.extend(
                gate.members()?
                    .into_iter()
                    .filter(|(_, member)| member.parent.as_deref() == Some(gate.agent()))
                    .map(|(child, _)| child),
            );
            Ok::<_, LedgerError>(children)
        })
        .await
        .map_err(|error| SessionError::error(format!("the budget ledger task ended: {error}")))?
        .map_err(|error| SessionError::error(error.to_string()))?
    };
    if children.is_empty() {
        return Ok(());
    }
    let mut live: HashSet<String> = HashSet::new();
    let mut cursor: Option<Cursor> = None;
    loop {
        let storage = Arc::clone(harness.storage());
        let line_cx = cx.clone();
        let after = cursor.take();
        let page = harness
            .read_on_line(async move {
                Ok(storage
                    .scan_conversations(
                        &ConversationQuery::default(),
                        SCAN_PAGE_SIZE,
                        after.as_ref(),
                        &line_cx,
                    )
                    .await?)
            })
            .await?;
        for conversation in &page.items {
            live.extend(
                read_children(harness, conversation.id, cx)
                    .await?
                    .children
                    .into_values()
                    .filter(|row| !row.is_deleted() && !row.status.is_terminal())
                    .map(|row| row.session_id),
            );
        }
        match page.next {
            Some(next) => cursor = Some(next),
            None => break,
        }
    }
    for child in children.iter().filter(|child| !live.contains(*child)) {
        give_back(gate, child).await?;
    }
    Ok(())
}
