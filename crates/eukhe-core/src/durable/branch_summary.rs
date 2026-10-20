//! Branch summarization for tree navigation: the entry collection, the
//! summarizer request and its window estimate, and the final summary text.
//! Port of core/compaction/branch-summarization.ts.

use std::collections::HashSet;

use eukhe_types::session::{AgentMessage, CompactionSummaryMessage, FileEntry};
use eukhe_types::token_estimate::estimate_text_tokens;

use crate::durable::compaction::summary_request::{estimate_tokens, summarizer_request_tokens};
use crate::durable::compaction::utils::{
    compute_file_lists, extract_file_ops_from_message, format_file_operations,
    serialize_conversation, FileOperations, SUMMARIZATION_SYSTEM_PROMPT,
};
use crate::durable::messages::{convert_to_llm, BRANCH_SUMMARY_PREFIX, BRANCH_SUMMARY_SUFFIX};

/// Details stored on a branch summary entry.
#[derive(Debug, Default, Clone, PartialEq, serde::Serialize, serde::Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct BranchSummaryDetails {
    pub read_files: Vec<String>,
    pub modified_files: Vec<String>,
}

/// The result of generating a branch summary.
#[derive(Debug, Default, Clone)]
pub struct BranchSummaryResult {
    pub summary: Option<String>,
    pub read_files: Vec<String>,
    pub modified_files: Vec<String>,
    pub aborted: bool,
    pub error: Option<String>,
    pub usage: Option<eukhe_types::ai::Usage>,
    /// The model that served the summary call (TS #2411's routed
    /// auxiliary model, or the session model when no auxiliary is
    /// configured): the caller persists it on the entry so the per-model
    /// cost fold bills the spend on the model that billed it, not the
    /// branch's `model_change` timeline.
    pub model: Option<(String, String)>,
}

/// Prepared summarization inputs.
#[derive(Debug, Default)]
pub struct BranchPreparation {
    pub messages: Vec<AgentMessage>,
    pub file_ops: FileOperations,
    pub total_tokens: u64,
}

/// Entry-path info between two tree positions.
#[derive(Debug, Default)]
pub struct CollectEntriesResult {
    pub entries: Vec<FileEntry>,
    pub common_ancestor_id: Option<String>,
}

fn parent_path(entries: &[FileEntry], leaf_id: &str) -> Vec<String> {
    let mut path = Vec::new();
    let mut current = Some(leaf_id.to_string());
    while let Some(id) = current {
        let Some(entry) = entries.iter().find(|entry| entry.id() == Some(id.as_str())) else {
            break;
        };
        path.push(id.clone());
        current = entry.parent_id().map(str::to_string);
    }
    path
}

/// Entries to summarize when navigating old-leaf -> target: the old path back
/// to (excluding) the common ancestor with the target path.
pub fn collect_entries_for_branch_summary(
    entries: &[FileEntry],
    old_leaf_id: Option<&str>,
    target_id: &str,
) -> CollectEntriesResult {
    let Some(old_leaf_id) = old_leaf_id else {
        return CollectEntriesResult::default();
    };
    let old_path: HashSet<String> = parent_path(entries, old_leaf_id).into_iter().collect();
    let target_path = parent_path(entries, target_id);
    let common_ancestor_id = target_path
        .iter()
        .rev()
        .find(|id| old_path.contains(*id))
        .cloned();
    let mut collected: Vec<FileEntry> = Vec::new();
    let mut current = Some(old_leaf_id.to_string());
    while let Some(id) = current {
        if Some(&id) == common_ancestor_id.as_ref() {
            break;
        }
        let Some(entry) = entries
            .iter()
            .find(|entry| entry.id() == Some(id.as_str()))
            .cloned()
        else {
            break;
        };
        current = entry.parent_id().map(str::to_string);
        collected.push(entry);
    }
    collected.reverse();
    CollectEntriesResult {
        entries: collected,
        common_ancestor_id,
    }
}

/// The message an entry contributes to summarizer input (compaction entries
/// become their summary message; bookkeeping entries contribute nothing).
fn get_message_from_entry(entry: &FileEntry) -> Option<AgentMessage> {
    match entry {
        FileEntry::Message { message, .. } => match message {
            // Tool results stay attached to their assistant tool call.
            AgentMessage::ToolResult(_) => None,
            _ => Some(message.clone()),
        },
        FileEntry::CustomMessage { payload, .. } => {
            if payload.custom_type == "harness_digest" {
                return None;
            }
            Some(AgentMessage::Custom(eukhe_types::session::CustomMessage {
                custom_type: payload.custom_type.clone(),
                content: payload.content.clone(),
                display: payload.display,
                details: payload.details.clone(),
                timestamp: crate::session::timestamp_to_millis(entry.timestamp()),
                rest: serde_json::Map::default(),
            }))
        }
        FileEntry::BranchSummary { payload, .. } => Some(AgentMessage::BranchSummary(
            eukhe_types::session::BranchSummaryMessage {
                summary: payload.summary.clone(),
                from_id: payload.from_id.clone(),
                timestamp: crate::session::timestamp_to_millis(entry.timestamp()),
            },
        )),
        FileEntry::Compaction { payload, .. } => {
            Some(AgentMessage::CompactionSummary(CompactionSummaryMessage {
                summary: payload.summary.clone(),
                tokens_before: payload.tokens_before,
                retained_message_count: None,
                custom_instructions: payload.custom_instructions.clone(),
                harness_digest: payload.harness_digest.clone(),
                harness_state_fingerprint: payload.harness_state_fingerprint.clone(),
                timestamp: crate::session::timestamp_to_millis(entry.timestamp()),
            }))
        }
        _ => None,
    }
}

/// Prepare entries under a token budget: newest-to-oldest until the budget
/// is hit. File ops are collected from ALL entries (cumulative tracking).
#[must_use]
pub fn prepare_branch_entries(entries: &[FileEntry], token_budget: u64) -> BranchPreparation {
    let mut file_ops = FileOperations::default();
    // Cumulative tracking from prior branch summaries (never hooked ones).
    for entry in entries {
        if let FileEntry::BranchSummary { payload, .. } = entry {
            if payload.from_hook != Some(true) {
                if let Some(details) = payload.details.clone() {
                    if let Ok(details) = serde_json::from_value::<BranchSummaryDetails>(details) {
                        file_ops.read.extend(details.read_files);
                        file_ops.edited.extend(details.modified_files);
                    }
                }
            }
        }
    }
    let mut messages: Vec<AgentMessage> = Vec::new();
    let mut total_tokens = 0u64;
    for entry in entries.iter().rev() {
        let Some(message) = get_message_from_entry(entry) else {
            continue;
        };
        extract_file_ops_from_message(&message, &mut file_ops);
        let tokens = estimate_tokens(&message);
        if token_budget > 0 && total_tokens + tokens > token_budget {
            // Compaction/branch summaries squeeze in under 90% budget.
            let boundary = matches!(
                entry,
                FileEntry::Compaction { .. } | FileEntry::BranchSummary { .. }
            );
            if boundary && total_tokens < token_budget * 9 / 10 {
                messages.insert(0, message);
                total_tokens += tokens;
            }
            break;
        }
        messages.insert(0, message);
        total_tokens += tokens;
    }
    BranchPreparation {
        messages,
        file_ops,
        total_tokens,
    }
}

const BRANCH_SUMMARY_PREAMBLE: &str = "The user explored a different conversation branch before returning here.\nSummary of that exploration:\n\n";

const BRANCH_SUMMARY_PROMPT: &str = "Create a structured summary of this conversation branch for context when returning later.\n\nUse this EXACT format:\n\n## Goal\n[What was the user trying to accomplish in this branch?]\n\n## Constraints & Preferences\n- [Any constraints, preferences, or requirements mentioned]\n- [Or \"(none)\" if none were mentioned]\n\n## Progress\n### Done\n- [x] [Completed tasks/changes]\n\n### In Progress\n- [ ] [Work that was started but not finished]\n\n### Blocked\n- [Issues preventing progress, if any]\n\n## Key Decisions\n- **[Decision]**: [Brief rationale]\n\n## Next Steps\n1. [What should happen next to continue this work]\n\nKeep each section concise. Preserve exact file paths, function names, and error messages.";

/// Build the branch-summary request messages for the model.
#[must_use]
pub fn build_branch_summary_request(
    entries: &[FileEntry],
    token_budget: u64,
    custom_instructions: Option<&str>,
    replace_instructions: bool,
) -> (Vec<AgentMessage>, BranchPreparation) {
    let preparation = prepare_branch_entries(entries, token_budget);
    let messages = if preparation.messages.is_empty() {
        Vec::new()
    } else {
        let llm_messages = convert_to_llm(&preparation.messages);
        let conversation_text = serialize_conversation(&llm_messages);
        let instructions = match (replace_instructions, custom_instructions) {
            (true, Some(custom)) => custom.to_string(),
            (false, Some(custom)) => {
                format!("{BRANCH_SUMMARY_PROMPT}\n\nAdditional focus: {custom}")
            }
            _ => BRANCH_SUMMARY_PROMPT.to_string(),
        };
        let prompt_text =
            format!("<conversation>\n{conversation_text}\n</conversation>\n\n{instructions}");
        vec![AgentMessage::User(eukhe_types::ai::UserMessage {
            content: eukhe_types::ai::UserContent::Text(prompt_text),
            timestamp: 0,
            rest: serde_json::Map::default(),
        })]
    };
    (messages, preparation)
}

/// Assemble the final summary text from a model response.
#[must_use]
pub fn finalize_branch_summary(
    response_text: &str,
    preparation: &BranchPreparation,
) -> BranchSummaryResult {
    let (read_files, modified_files) = compute_file_lists(&preparation.file_ops);
    let mut summary = format!("{BRANCH_SUMMARY_PREAMBLE}{response_text}");
    summary.push_str(&format_file_operations(&read_files, &modified_files));
    BranchSummaryResult {
        summary: Some(if summary.is_empty() {
            "No summary generated".to_string()
        } else {
            summary
        }),
        read_files,
        modified_files,
        aborted: false,
        error: None,
        usage: None,
        model: None,
    }
}

/// The TS default reserve budget (`reserveTokens`).
pub const DEFAULT_BRANCH_RESERVE_TOKENS: u64 = 16_384;

/// The summarizer call cap (TS `maxTokens: 2048`).
pub(crate) const BRANCH_SUMMARY_MAX_TOKENS: u64 = 2048;

/// Estimate the context window the branch-summary request needs (TS
/// #2411's `estimateBranchSummaryRequestTokens`), using the same
/// entry-slicing budget and prompt builder as the wire call, so the
/// estimate cannot drift from the request. `context_window` is the window
/// of the model the session would run the summary on (the fallback): a
/// resolved auxiliary model must hold two things — the request body
/// (the summary call builds: the system prompt, the serialized
/// branch inside its `<conversation>` wrapper, and the completion
/// budget) and the reserve the branch call subtracts from its window —
/// the larger of the two decides whether the model fits. A branch that
/// slices to nothing issues no wire request, but a window at or below the
/// reserve would slice with a non-positive budget that
/// [`prepare_branch_entries`] treats as unlimited, so the empty-slice
/// shape still requires a window above the reserve.
#[must_use]
pub fn estimate_branch_summary_request_tokens(
    entries: &[FileEntry],
    context_window: u64,
    reserve_tokens: u64,
    custom_instructions: Option<&str>,
    replace_instructions: bool,
) -> u64 {
    // Mirrors the summary call: the same budget decides which
    // entries fit.
    let window = if context_window > 0 {
        context_window
    } else {
        128_000
    };
    let token_budget = window.saturating_sub(reserve_tokens);
    let (request, _) = build_branch_summary_request(
        entries,
        token_budget,
        custom_instructions,
        replace_instructions,
    );
    if request.is_empty() {
        return reserve_tokens.saturating_add(1);
    }
    let system_prompt_tokens = estimate_text_tokens(SUMMARIZATION_SYSTEM_PROMPT);
    let prompt_tokens = summarizer_request_tokens(&request);
    // The completion budget and the input-slice reserve are separate
    // draws on the same window, so the larger of the two decides whether
    // the model fits.
    (system_prompt_tokens + prompt_tokens + BRANCH_SUMMARY_MAX_TOKENS)
        .max(prompt_tokens.saturating_add(reserve_tokens))
}

/// The presentation message users see for a branch summary.
#[must_use]
pub fn branch_summary_presentation(summary: &str) -> String {
    format!("{BRANCH_SUMMARY_PREFIX}{summary}{BRANCH_SUMMARY_SUFFIX}")
}

#[cfg(test)]
mod tests {
    use super::*;
    use eukhe_types::session::EntryBase;

    fn entry(id: &str, parent: Option<&str>, message: AgentMessage) -> FileEntry {
        FileEntry::Message {
            message,
            base: EntryBase {
                id: Some(id.to_string()),
                parent_id: parent.map(str::to_string),
                timestamp: Some("2024-01-01T00:00:00.000Z".to_string()),
                rest: serde_json::Map::default(),
            },
        }
    }

    fn user(text: &str) -> AgentMessage {
        AgentMessage::User(eukhe_types::ai::UserMessage {
            content: eukhe_types::ai::UserContent::Text(text.to_string()),
            timestamp: 0,
            rest: serde_json::Map::default(),
        })
    }

    #[test]
    fn collects_old_branch_to_common_ancestor() {
        // root -> u1 -> a1 -> u2 (old leaf)
        //        \\-> u3 (target, sibling of a1's subtree? no: sibling of u1's children)
        let entries = vec![
            entry("u1", None, user("start")),
            entry("a1", Some("u1"), user("assistant turn")),
            entry("u2", Some("a1"), user("old leaf")),
            entry("u3", Some("u1"), user("target")),
        ];
        let result = collect_entries_for_branch_summary(&entries, Some("u2"), "u3");
        assert_eq!(result.common_ancestor_id.as_deref(), Some("u1"));
        // u2 and a1 are collected (target ancestor excluded).
        assert_eq!(result.entries.len(), 2);
        assert_eq!(result.entries[0].id(), Some("a1"));
        assert_eq!(result.entries[1].id(), Some("u2"));
    }

    #[test]
    fn preparation_respects_budget_and_keeps_boundaries() {
        let mut entries = Vec::new();
        for i in 0..10 {
            entries.push(entry(
                &format!("e{i}"),
                None,
                user(&format!("message {i} with padding")),
            ));
        }
        // Each 22-char message estimates to 7 tokens at 3.5 chars per
        // token (6 at chars/4): a 7-token budget keeps only the newest one
        // before the walk breaks, and a 6-token budget keeps nothing.
        let preparation = prepare_branch_entries(&entries, 7);
        assert_eq!(preparation.messages.len(), 1);
        let tight = prepare_branch_entries(&entries, 6);
        assert_eq!(tight.messages.len(), 0);
        let unlimited = prepare_branch_entries(&entries, 0);
        assert_eq!(unlimited.messages.len(), 10);
    }

    #[test]
    fn request_and_finalize() {
        let entries = vec![entry("e0", None, user("explore the widget"))];
        let (messages, preparation) =
            build_branch_summary_request(&entries, 0, Some("focus on x"), false);
        assert_eq!(messages.len(), 1);
        match &messages[0] {
            AgentMessage::User(user) => {
                let text = user.content.text();
                assert!(text.starts_with("<conversation>"));
                assert!(text.contains("Additional focus: focus on x"));
            }
            _ => panic!("expected user"),
        }
        let result = finalize_branch_summary("## Goal\nexplore", &preparation);
        let summary = result.summary.unwrap();
        assert!(summary.contains("The user explored a different conversation branch"));
        assert!(summary.contains("## Goal"));
        // Presentation wraps in the branch envelope.
        assert!(branch_summary_presentation("s").contains("[branch-summary]"));
    }

    #[test]
    fn compaction_entries_become_summary_messages() {
        let compaction = FileEntry::Compaction {
            payload: eukhe_types::session::CompactionEntry {
                summary: "prior state".to_string(),
                first_kept_entry_id: "x".to_string(),
                tokens_before: 10,
                details: None,
                from_hook: None,
                custom_instructions: None,
                usage: None,
                harness_digest: None,
                harness_state_fingerprint: None,
            },
            base: EntryBase {
                id: Some("c0".to_string()),
                parent_id: None,
                timestamp: Some("2024-01-01T00:00:00.000Z".to_string()),
                rest: serde_json::Map::default(),
            },
        };
        let message = get_message_from_entry(&compaction).unwrap();
        match message {
            AgentMessage::CompactionSummary(summary) => {
                assert_eq!(summary.summary, "prior state");
                assert_eq!(summary.tokens_before, 10);
            }
            _ => panic!("expected compaction summary"),
        }
    }

    /// The window estimate mirrors the summary call's slicing and
    /// prompt exactly (TS #2411's `estimateBranchSummaryRequestTokens`).
    #[test]
    fn branch_window_estimate_shapes() {
        // An entry too large for the window's slice budget: no wire request
        // is issued, but the estimate still requires a window above the
        // reserve (a window at or below it would slice with a non-positive
        // budget that `prepare_branch_entries` treats as unlimited).
        let big = vec![entry("e0", None, user(&"x".repeat(100_000)))];
        assert_eq!(
            estimate_branch_summary_request_tokens(
                &big,
                20_000,
                DEFAULT_BRANCH_RESERVE_TOKENS,
                None,
                false
            ),
            DEFAULT_BRANCH_RESERVE_TOKENS + 1
        );
        // A fitting branch estimates the request body (system prompt +
        // serialized branch + completion budget) and the reserve draw; the
        // larger of the two wins, so a bigger reserve grows the estimate.
        let entries = vec![entry("e0", None, user("explore the widget"))];
        let big_reserve = estimate_branch_summary_request_tokens(
            &entries,
            200_000,
            DEFAULT_BRANCH_RESERVE_TOKENS,
            Some("focus on x"),
            false,
        );
        let small_reserve = estimate_branch_summary_request_tokens(
            &entries,
            200_000,
            100,
            Some("focus on x"),
            false,
        );
        assert!(big_reserve > small_reserve);
        // A window that slices entries away shrinks the request the model
        // must hold, so the estimate shrinks with it.
        let wide = vec![
            entry("e0", None, user(&"y".repeat(400_000))),
            entry("e1", Some("e0"), user(&"y".repeat(400_000))),
            entry("e2", Some("e1"), user(&"y".repeat(400_000))),
        ];
        let big_window =
            estimate_branch_summary_request_tokens(&wide, 200_000, 16_384, None, false);
        let small_window =
            estimate_branch_summary_request_tokens(&wide, 100_000, 16_384, None, false);
        assert!(big_window > small_window);
    }
}
