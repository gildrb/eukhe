//! The `pi.usage` document: one conversation's own spend
//! (`harness/usage.ts`).

use eukhe_chord::delta::{Draft, DraftItem};
use eukhe_chord::json::{to_json, JsonValue};
use eukhe_types::pi_ai::{IndexMap, Usage};
use serde::{Deserialize, Serialize};

use crate::documents::{ConversationDoc, DocDefinition};
use crate::session::{SessionError, SessionResult, Tx};
use crate::types::{ConversationId, LatestFork};

/// Ledger of one conversation's own spend: its entries, and compaction
/// summarization attempts, which have none.
///
/// TS keeps each bucket as a JSON object whose key order the document
/// preserves; the sum [`add_usage_state`] builds keeps first-seen key order,
/// and its `Usage` values serialize in the struct's field order.
#[derive(Debug, Clone, Default, PartialEq, Serialize, Deserialize)]
pub struct UsageState {
    /// Assistant entries and summarization attempts, keyed
    /// `provider/modelId`.
    pub models: IndexMap<String, Usage>,
    /// Tool results, keyed by tool name; their usage has no model identity.
    pub tools: IndexMap<String, Usage>,
}

/// One bucket of [`UsageState`].
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum UsageBucket {
    /// `models`.
    Models,
    /// `tools`.
    Tools,
}

impl UsageBucket {
    /// The document key.
    #[must_use]
    pub fn key(self) -> &'static str {
        match self {
            Self::Models => "models",
            Self::Tools => "tools",
        }
    }
}

pub static USAGE_DOC: ConversationDoc<UsageState> = match ConversationDoc::define(
    DocDefinition {
        kind: "pi.usage",
        version: 1,
        initial: UsageState::default,
        migrate: None,
        checkpoint_when: Some(|_, _, _| true),
    },
    LatestFork::Initial,
) {
    Ok(token) => token,
    Err(_) => panic!("pi.usage has a valid version"),
};

/// Add `usage` to one bucket of the conversation's `pi.usage`, in the commit
/// that records the response.
///
/// # Errors
///
/// Document access or draft failures.
pub async fn record_usage(
    tx: &Tx,
    conversation_id: ConversationId,
    bucket: UsageBucket,
    key: &str,
    usage: &Usage,
) -> SessionResult<()> {
    let totals = tx
        .doc(&USAGE_DOC, conversation_id)
        .await?
        .child(bucket.key())?;
    // Own keys only: a tool may be called `toString`.
    match totals.get(key)?.and_then(DraftItem::into_draft) {
        // Optional counters are omitted; drafts take strict JSON.
        None => totals.set(key, to_json(usage)?)?,
        Some(total) => add_usage_to_draft(&total, usage)?,
    }
    Ok(())
}

fn number(value: f64) -> SessionResult<JsonValue> {
    JsonValue::try_from(value).map_err(SessionError::from)
}

fn add_counter(draft: &Draft, key: &str, amount: f64) -> SessionResult<()> {
    let current = draft
        .get(key)?
        .and_then(|item| item.as_value().and_then(JsonValue::as_f64))
        .unwrap_or(0.0);
    draft.set(key, number(current + amount)?)?;
    Ok(())
}

#[expect(
    clippy::cast_precision_loss,
    reason = "token counts are JS numbers, far below 2^53"
)]
fn tokens(count: u64) -> f64 {
    count as f64
}

/// `addUsage` over a draft total: every counter of `usage` added; optional
/// counters added once either side reports them.
fn add_usage_to_draft(total: &Draft, usage: &Usage) -> SessionResult<()> {
    add_counter(total, "input", tokens(usage.input))?;
    add_counter(total, "output", tokens(usage.output))?;
    add_counter(total, "cacheRead", tokens(usage.cache_read))?;
    add_counter(total, "cacheWrite", tokens(usage.cache_write))?;
    add_counter(total, "totalTokens", tokens(usage.total_tokens))?;
    if let Some(value) = usage.cache_write_1h {
        add_counter(total, "cacheWrite1h", tokens(value))?;
    }
    if let Some(value) = usage.reasoning {
        add_counter(total, "reasoning", tokens(value))?;
    }
    let cost = total.child("cost")?;
    add_counter(&cost, "input", usage.cost.input)?;
    add_counter(&cost, "output", usage.cost.output)?;
    add_counter(&cost, "cacheRead", usage.cost.cache_read)?;
    add_counter(&cost, "cacheWrite", usage.cost.cache_write)?;
    add_counter(&cost, "total", usage.cost.total)?;
    Ok(())
}

/// Add every counter of `usage` to `total`; optional counters are added
/// once either side reports them.
pub fn add_usage(total: &mut Usage, usage: &Usage) {
    total.input += usage.input;
    total.output += usage.output;
    total.cache_read += usage.cache_read;
    total.cache_write += usage.cache_write;
    total.total_tokens += usage.total_tokens;
    if let Some(value) = usage.cache_write_1h {
        total.cache_write_1h = Some(total.cache_write_1h.unwrap_or(0) + value);
    }
    if let Some(value) = usage.reasoning {
        total.reasoning = Some(total.reasoning.unwrap_or(0) + value);
    }
    total.cost.input += usage.cost.input;
    total.cost.output += usage.cost.output;
    total.cost.cache_read += usage.cost.cache_read;
    total.cost.cache_write += usage.cost.cache_write;
    total.cost.total += usage.cost.total;
}

/// Add every bucket of `state` into `sum`.
pub fn add_usage_state(sum: &mut UsageState, state: &UsageState) {
    for (totals, bucket) in [
        (&mut sum.models, &state.models),
        (&mut sum.tools, &state.tools),
    ] {
        for (key, usage) in bucket {
            match totals.get_mut(key) {
                Some(total) => add_usage(total, usage),
                None => {
                    totals.insert(key.clone(), *usage);
                }
            }
        }
    }
}
