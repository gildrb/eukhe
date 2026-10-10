//! Goal operations over a conversation: reads, the `/goal` actions (start,
//! pause, resume, clear), the CLI `--goal` seed, the legacy import seed, and
//! the shared commit helpers of the hooks and host requests.
//!
//! The old engine admitted a minted goal context as the next turn's primary
//! record; here a context that starts a run is submitted as user input with
//! a request id (a rerun never queues it twice), and its `goal_context` row
//! is a display/audit [`CUSTOM_ENTRY`] without model (the user entry the
//! submission or the `on_yield` continuation appends carries the text).

use eukhe_chord::context::Context;
use eukhe_durable::entries::{ASSISTANT_ENTRY, TOOL_RESULT_ENTRY, USER_ENTRY};
use eukhe_durable::harness::types::{InputSubmissionDraft, WhenBusy};
use eukhe_durable::harness::{
    Conversation, ConversationEntryQuery, Harness, InboxItem, InboxState, INBOX_DOC,
};
use eukhe_durable::session::{SessionError, SessionResult, Tx};
use eukhe_durable::types::{ConversationId, DocumentReader, EntryDraft, TypedEntryDraft};
use eukhe_types::pi_ai::{UserContent, UserContentBlock};

use super::docs::{open_doc, read_doc, write_doc, GOAL_DOC};
use super::state::{completed, mint_after_backoff, new_goal, paused, resumed, served, stamp, Mint};
use crate::autonomous::now_millis;
use crate::durable::entries::{CustomEntryData, CUSTOM_ENTRY};
use crate::goals::{
    create_goal_context_message, is_persisted_goal_state, normalize_goal_state,
    stale_active_goal_failure, GoalContextKind, GoalState, GoalStatus, GOAL_STATE_CUSTOM_TYPE,
};

/// The goal-context prefixes (`[goal: <kind>]`, `crate::goals`' context
/// message format) of every kind.
const GOAL_NUDGE_PREFIXES: [&str; 3] = [
    "[goal: continuation]",
    "[goal: budget-limit]",
    "[goal: objective-updated]",
];

/// Whether `text` is a goal-context nudge (a continuation, budget-limit, or
/// objective-updated context): harness text, not the user's words.
#[must_use]
pub fn is_goal_nudge(text: &str) -> bool {
    GOAL_NUDGE_PREFIXES
        .iter()
        .any(|prefix| text.starts_with(prefix))
}

/// The concatenated text blocks of user content.
pub(crate) fn user_text(content: &UserContent) -> String {
    match content {
        UserContent::Text(text) => text.clone(),
        UserContent::Blocks(blocks) => blocks
            .iter()
            .filter_map(|block| match block {
                UserContentBlock::Text(text) => Some(text.text.as_str()),
                UserContentBlock::Image(_) => None,
            })
            .collect(),
    }
}

/// The served goal of `conversation_id` (the empty state when none): its
/// `time_used_seconds` is the goal's age now.
///
/// # Errors
///
/// Read failures.
pub async fn goal_state(
    reader: &(impl DocumentReader + ?Sized),
    conversation_id: ConversationId,
    cx: &Context,
) -> SessionResult<GoalState> {
    let stored = read_doc(reader, &GOAL_DOC, conversation_id, cx)
        .await?
        .unwrap_or_default();
    Ok(served(&stored, now_millis()))
}

/// The text of a goal context of `kind` and its display/audit row.
///
/// # Errors
///
/// The goal has no objective, or the details do not encode.
pub(crate) fn goal_context(
    state: &GoalState,
    kind: GoalContextKind,
) -> SessionResult<(String, EntryDraft)> {
    let message = create_goal_context_message(state, kind)
        .map_err(|error| SessionError::error(format!("{error:#}")))?;
    let text = message.content.text();
    let draft = CUSTOM_ENTRY.draft(&TypedEntryDraft {
        model: None,
        data: CustomEntryData {
            custom_type: message.custom_type,
            content: Some(UserContent::Text(text.clone())),
            display: message.display,
            details: message.details,
            input: false,
        },
        head: None,
        edits: None,
    })?;
    Ok((text, draft))
}

/// The conversation `conversation_id` of `harness`.
///
/// # Errors
///
/// Read failures, or no such conversation.
pub(crate) async fn conversation_of(
    harness: &Harness,
    conversation_id: ConversationId,
    cx: &Context,
) -> SessionResult<Conversation> {
    harness
        .conversation(conversation_id, cx)
        .await?
        .ok_or_else(|| {
            SessionError::error(format!("Conversation {conversation_id} does not exist"))
        })
}

/// Apply `change` to the goal in one commit: `change` maps the current goal
/// to the next one (`None` writes nothing) and an optional context kind
/// whose row is appended. Returns the written (or unchanged) goal and the
/// context text.
///
/// # Errors
///
/// `change`'s error, or commit failures.
pub(crate) async fn update_goal<F>(
    conversation: &Conversation,
    change: F,
    cx: &Context,
) -> SessionResult<(GoalState, Option<String>)>
where
    F: FnOnce(&GoalState, u64) -> SessionResult<Option<(GoalState, Option<GoalContextKind>)>>
        + Send
        + 'static,
{
    let conversation_id = conversation.id();
    conversation
        .commit(
            move |tx| async move {
                let now = now_millis();
                let (draft, current) = open_doc(&tx, &GOAL_DOC, conversation_id).await?;
                let Some((next, context)) = change(&current, now)? else {
                    return Ok((served(&current, now), None));
                };
                let written = stamp(next, now);
                write_doc(&draft, &written)?;
                let mut text = None;
                if let Some(kind) = context {
                    let (context_text, row) = goal_context(&written, kind)?;
                    tx.append_entry(conversation_id, row).await?;
                    text = Some(context_text);
                }
                Ok((written, text))
            },
            cx,
        )
        .await
}

/// Submit a goal context as user input; `request_id` keeps a rerun from
/// queueing it twice.
///
/// # Errors
///
/// Submission failures.
pub(crate) async fn submit_goal_context(
    conversation: &Conversation,
    request_id: String,
    text: String,
    when_busy: WhenBusy,
    cx: &Context,
) -> SessionResult<()> {
    conversation
        .submit(
            InputSubmissionDraft {
                request_id: Some(request_id),
                content: UserContent::Text(text),
                when_busy: Some(when_busy),
            },
            cx,
        )
        .await?;
    Ok(())
}

/// Whether queued user input owns the next boundary (old
/// `session_input_queued`).
///
/// # Errors
///
/// Read failures.
pub(crate) async fn user_input_queued(
    reader: &(impl DocumentReader + ?Sized),
    conversation_id: ConversationId,
    cx: &Context,
) -> SessionResult<bool> {
    let inbox: InboxState = read_doc(reader, &INBOX_DOC, conversation_id, cx)
        .await?
        .unwrap_or_default();
    Ok(inbox.items.iter().any(|item| match item {
        InboxItem::Steer { .. } | InboxItem::FollowUp { .. } => true,
        InboxItem::Write { .. } => false,
    }))
}

/// Withdraw queued goal contexts (old `purge_queued_goal_contexts`): a
/// state change never lets a stale context run behind it.
///
/// # Errors
///
/// Read or abort failures.
pub async fn withdraw_queued_goal_contexts(
    harness: &Harness,
    conversation_id: ConversationId,
    cx: &Context,
) -> SessionResult<()> {
    let inbox: InboxState = read_doc(harness, &INBOX_DOC, conversation_id, cx)
        .await?
        .unwrap_or_default();
    for item in inbox.items {
        let queued = match &item {
            InboxItem::Steer { content, .. } | InboxItem::FollowUp { content, .. } => {
                is_goal_nudge(&user_text(content))
            }
            InboxItem::Write { .. } => false,
        };
        if queued {
            harness
                .abort_submission(item.id(), Some(conversation_id), cx)
                .await?;
        }
    }
    Ok(())
}

/// `/goal <objective>`: start a goal (replacing any previous one) and submit
/// its first continuation context as a follow-up.
///
/// # Errors
///
/// The objective or budget fails validation, or read/commit failures.
pub async fn start_goal(
    harness: &Harness,
    conversation_id: ConversationId,
    objective: &str,
    token_budget: Option<u64>,
    cx: &Context,
) -> SessionResult<GoalState> {
    let conversation = conversation_of(harness, conversation_id, cx).await?;
    withdraw_queued_goal_contexts(harness, conversation_id, cx).await?;
    let objective = objective.to_owned();
    let (goal, text) = update_goal(
        &conversation,
        move |_, now| {
            let goal = new_goal(&objective, token_budget, now)
                .map_err(|error| SessionError::error(format!("{error:#}")))?;
            Ok(Some((goal, Some(GoalContextKind::Continuation))))
        },
        cx,
    )
    .await?;
    if let (Some(text), Some(goal_id)) = (text, goal.goal_id.clone()) {
        submit_goal_context(
            &conversation,
            format!("goal:{goal_id}:start"),
            text,
            WhenBusy::FollowUp,
            cx,
        )
        .await?;
    }
    Ok(goal)
}

/// `/goal pause`: pause an active goal (no-op otherwise).
///
/// # Errors
///
/// Read or commit failures.
pub async fn pause_goal(
    harness: &Harness,
    conversation_id: ConversationId,
    cx: &Context,
) -> SessionResult<GoalState> {
    let conversation = conversation_of(harness, conversation_id, cx).await?;
    withdraw_queued_goal_contexts(harness, conversation_id, cx).await?;
    let (goal, _) = update_goal(
        &conversation,
        |current, _| Ok(paused(current, "Paused by user").map(|goal| (goal, None))),
        cx,
    )
    .await?;
    Ok(goal)
}

/// `/goal resume`: resume a paused or budget-limited goal; an active result
/// submits its continuation context as a follow-up.
///
/// # Errors
///
/// Read, commit, or submission failures.
pub async fn resume_goal(
    harness: &Harness,
    conversation_id: ConversationId,
    cx: &Context,
) -> SessionResult<GoalState> {
    let conversation = conversation_of(harness, conversation_id, cx).await?;
    let (goal, text) = update_goal(
        &conversation,
        |current, _| {
            Ok(resumed(current).map(|goal| {
                let context =
                    (goal.status == GoalStatus::Active).then_some(GoalContextKind::Continuation);
                (goal, context)
            }))
        },
        cx,
    )
    .await?;
    if let (Some(text), Some(goal_id), Some(updated_at)) =
        (text, goal.goal_id.clone(), goal.updated_at)
    {
        submit_goal_context(
            &conversation,
            format!("goal:{goal_id}:resume:{updated_at}"),
            text,
            WhenBusy::FollowUp,
            cx,
        )
        .await?;
    }
    Ok(goal)
}

/// The post-compaction goal continuation (old
/// `mint_post_compaction_goal_continuation`; TS `compact()`'s `didCompact`
/// and active-goal branch): the manual compaction aborted the running
/// turn, which ends an active goal's in-run loop, so the compaction mints
/// one continuation slot and submits its context as a follow-up. Writes
/// nothing when the goal does not own the wakeup or queued user input owns
/// the next boundary. Returns the minted goal.
///
/// # Errors
///
/// Read, commit, or submission failures.
pub async fn continue_goal_after_compaction(
    harness: &Harness,
    conversation_id: ConversationId,
    cx: &Context,
) -> SessionResult<Option<GoalState>> {
    if user_input_queued(harness, conversation_id, cx).await? {
        return Ok(None);
    }
    let conversation = conversation_of(harness, conversation_id, cx).await?;
    withdraw_queued_goal_contexts(harness, conversation_id, cx).await?;
    let (goal, text) = update_goal(
        &conversation,
        |current, _| {
            Ok(match mint_after_backoff(current) {
                Mint::Continue(next) => Some((next, Some(GoalContextKind::Continuation))),
                Mint::Refuse(change) => change.map(|next| (next, None)),
                Mint::Backoff { state, .. } => Some((state, None)),
            })
        },
        cx,
    )
    .await?;
    let (Some(text), Some(goal_id), Some(updated_at)) =
        (text, goal.goal_id.clone(), goal.updated_at)
    else {
        return Ok(None);
    };
    submit_goal_context(
        &conversation,
        format!("goal:{goal_id}:compaction:{updated_at}"),
        text,
        WhenBusy::FollowUp,
        cx,
    )
    .await?;
    Ok(Some(goal))
}

/// `/goal clear`: drop the goal. Returns whether a goal was cleared.
///
/// # Errors
///
/// Read or commit failures.
pub async fn clear_goal(
    harness: &Harness,
    conversation_id: ConversationId,
    cx: &Context,
) -> SessionResult<bool> {
    let conversation = conversation_of(harness, conversation_id, cx).await?;
    withdraw_queued_goal_contexts(harness, conversation_id, cx).await?;
    let cleared = std::sync::Arc::new(std::sync::atomic::AtomicBool::new(false));
    let flag = std::sync::Arc::clone(&cleared);
    update_goal(
        &conversation,
        move |current, _| {
            flag.store(
                current.objective.is_some() && current.status != GoalStatus::Idle,
                std::sync::atomic::Ordering::SeqCst,
            );
            Ok(Some((GoalState::default(), None)))
        },
        cx,
    )
    .await?;
    Ok(cleared.load(std::sync::atomic::Ordering::SeqCst))
}

/// `goal.complete()` / completion: complete the goal; `None` when there is
/// no goal.
///
/// # Errors
///
/// Read or commit failures.
pub async fn complete_goal(
    conversation: &Conversation,
    cx: &Context,
) -> SessionResult<Option<GoalState>> {
    let (goal, _) = update_goal(
        conversation,
        |current, _| Ok(completed(current).map(|goal| (goal, None))),
        cx,
    )
    .await?;
    Ok((goal.status == GoalStatus::Complete).then_some(goal))
}

/// The CLI `--goal` seed: start the goal only on a conversation that has no
/// transcript yet and no goal (old `seed_initial_goal`). Returns whether the
/// seed landed.
///
/// # Errors
///
/// The objective or budget fails validation, or read/commit failures.
pub async fn seed_initial_goal(
    harness: &Harness,
    conversation_id: ConversationId,
    objective: &str,
    token_budget: Option<u64>,
    cx: &Context,
) -> SessionResult<bool> {
    let conversation = conversation_of(harness, conversation_id, cx).await?;
    let existing = read_doc(harness, &GOAL_DOC, conversation_id, cx).await?;
    if existing.is_some_and(|goal| goal.status != GoalStatus::Idle || goal.objective.is_some()) {
        return Ok(false);
    }
    let mut cursor = None;
    loop {
        let page = conversation
            .entries(ConversationEntryQuery::default(), 64, cursor, cx)
            .await?;
        let transcript = page.items.iter().any(|entry| {
            [
                USER_ENTRY.kind(),
                ASSISTANT_ENTRY.kind(),
                TOOL_RESULT_ENTRY.kind(),
            ]
            .contains(&entry.kind.as_str())
        });
        if transcript {
            return Ok(false);
        }
        match page.next {
            Some(next) => cursor = Some(next),
            None => break,
        }
    }
    start_goal(harness, conversation_id, objective, token_budget, cx).await?;
    Ok(true)
}

/// Seed `eukhe.goal` from a legacy session's active branch (file order):
/// the newest valid `thread_goal_state` row, normalized; an active row with
/// a terminal provider failure settled after it adopts the failure (the old
/// restore-resurrection guard). Writes nothing when the branch has no goal
/// row.
///
/// # Errors
///
/// Transaction failures.
pub async fn import_legacy_goal(
    tx: &Tx,
    conversation_id: ConversationId,
    entries: &[eukhe_types::session::FileEntry],
) -> SessionResult<()> {
    let latest = entries.iter().rev().find_map(|entry| match entry {
        eukhe_types::session::FileEntry::Custom { payload, .. }
            if payload.custom_type == GOAL_STATE_CUSTOM_TYPE =>
        {
            payload
                .data
                .as_ref()
                .filter(|data| is_persisted_goal_state(data))
                .and_then(|data| serde_json::from_value::<GoalState>(data.clone()).ok())
        }
        _ => None,
    });
    let Some(state) = latest else {
        return Ok(());
    };
    let mut state = normalize_goal_state(state);
    if state.status == GoalStatus::Active {
        if let Some(error) = stale_active_goal_failure(entries) {
            state = GoalState {
                active: false,
                status: GoalStatus::Error,
                last_reason: Some(error.clone()),
                last_error: Some(error),
                ..state
            };
        }
    }
    let draft = tx.doc(&GOAL_DOC, conversation_id).await?;
    write_doc(&draft, &state)
}
