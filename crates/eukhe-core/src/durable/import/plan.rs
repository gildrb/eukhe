//! Legacy session -> import plan: the active branch of an old `<id>.jsonl`
//! session as durable entry drafts, plus the agent state it ends with.
//!
//! Each entry's `model` is exactly what the old engine sent the model for
//! that row (`build_session_context` + `convert_to_llm`), so the imported
//! conversation's model context equals the old session's active context.

use std::borrow::Cow;
use std::collections::{HashMap, HashSet};

use eukhe_durable::entries::{
    CompactionData, ToolResultData, ASSISTANT_ENTRY, COMPACTION_ENTRY, TOOL_RESULT_ENTRY,
    USER_ENTRY,
};
use eukhe_durable::harness::types::{CompactionReason, ModelRef};
use eukhe_durable::types::{EntryDraft, TypedEntryDraft};
use eukhe_types::ai::AssistantContentBlock;
use eukhe_types::pi_ai::{Message, ModelThinkingLevel, UserContent};
use eukhe_types::session::{
    AgentMessage, BranchSummaryMessage, CompactionEntry, CompactionSummaryMessage, FileEntry,
};
use serde::de::DeserializeOwned;
use serde::Serialize;

use super::ImportError;
use crate::durable::entries::{
    bash_entry_draft, custom_entry_draft, BashEntryData, BranchSummaryData, CustomEntryData,
    CustomStateData, BRANCH_SUMMARY_ENTRY, COMPACTION_SUMMARY_ENTRY, CUSTOM_ENTRY,
    CUSTOM_STATE_ENTRY,
};
use crate::session::tree::SessionTree;
use crate::session::{migrate_to_current_version, parse_session_entries, timestamp_to_millis};
use crate::session_engine::headless::HARNESS_DIGEST_CUSTOM_TYPE;
use crate::session_engine::messages::convert_to_llm;

/// Where an imported entry's context range starts (`EntryRecord.head`).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum PlannedHead {
    /// Not a head marker.
    None,
    /// The range starts at the entry itself.
    SelfEntry,
    /// The range starts at the planned entry with this index.
    Planned(usize),
}

/// One durable entry to append; `draft.head` is unset, see `head`.
#[derive(Debug, Clone)]
pub(super) struct PlannedEntry {
    pub(super) draft: EntryDraft,
    pub(super) head: PlannedHead,
}

/// What the import writes.
#[derive(Debug, Clone)]
pub(super) struct ImportPlan {
    pub(super) session_id: String,
    pub(super) cwd: String,
    pub(super) model: Option<ModelRef>,
    pub(super) thinking_level: Option<ModelThinkingLevel>,
    pub(super) leaf_id: Option<String>,
    /// The active branch's rows, root first (migrated, attributions folded).
    pub(super) branch: Vec<FileEntry>,
    pub(super) entries: Vec<PlannedEntry>,
    /// Branch rows neither imported as entries nor applied to agent state.
    pub(super) skipped_rows: usize,
}

/// Plan the import of a legacy session file's content.
///
/// # Errors
///
/// The content has no session header, the branch's thinking level is not a
/// known level, or a row does not convert to the durable shapes.
pub(super) fn plan_import(content: &str) -> Result<ImportPlan, ImportError> {
    let mut entries = parse_session_entries(content);
    if !matches!(entries.first(), Some(FileEntry::Header { .. })) {
        return Err(ImportError::MissingHeader);
    }
    migrate_to_current_version(&mut entries);
    let (session_id, cwd) = match entries.first() {
        Some(FileEntry::Header { header }) => (header.id.clone(), header.cwd.clone()),
        _ => return Err(ImportError::MissingHeader),
    };
    // A header-only file has no entries, so no leaf (the header is not one).
    let leaf_id = SessionTree::build(&entries)
        .default_leaf(&entries)
        .filter(|_| !matches!(entries.last(), Some(FileEntry::Header { .. })));
    let path = branch_path(&entries, leaf_id.as_deref());
    let branch: Vec<FileEntry> = path.iter().map(|&index| entries[index].clone()).collect();

    let mut planner = Planner::new(&branch);
    for position in 0..branch.len() {
        planner.plan_row(position)?;
    }
    let thinking_level = planner
        .thinking_level
        .map(|level| {
            ModelThinkingLevel::parse(level).ok_or_else(|| ImportError::ThinkingLevel {
                level: level.to_owned(),
            })
        })
        .transpose()?;
    let (model, entries, skipped_rows) = (planner.model, planner.entries, planner.skipped_rows);
    Ok(ImportPlan {
        session_id,
        cwd,
        model,
        thinking_level,
        leaf_id,
        branch,
        entries,
        skipped_rows,
    })
}

/// File indices from the root down to `leaf_id`, following `parentId`; a
/// parent cycle in a corrupt file ends the walk (as `build_session_context`).
fn branch_path(entries: &[FileEntry], leaf_id: Option<&str>) -> Vec<usize> {
    let Some(leaf_id) = leaf_id else {
        return Vec::new();
    };
    let by_id: HashMap<&str, usize> = entries
        .iter()
        .enumerate()
        .filter_map(|(index, entry)| entry.id().map(|id| (id, index)))
        .collect();
    let mut path = Vec::new();
    let mut visited = HashSet::new();
    let mut current = by_id.get(leaf_id).copied();
    while let Some(index) = current {
        if !visited.insert(index) {
            break;
        }
        path.push(index);
        current = entries[index]
            .parent_id()
            .and_then(|parent_id| by_id.get(parent_id).copied());
    }
    path.reverse();
    path
}

/// Which harness digests reach the model (`build_session_context`, TS
/// #2394/#2400): only the newest digest custom message, unless the latest
/// compaction's snapshot is newer; a digest after the latest compaction
/// takes the place of the summary's snapshot.
struct DigestPolicy {
    /// Branch position of the latest compaction.
    compaction: Option<usize>,
    /// Branch position of the one digest custom message that is kept.
    kept_digest: Option<usize>,
    /// The latest compaction's summary drops its digest block.
    summary_yields_snapshot: bool,
}

impl DigestPolicy {
    fn new(branch: &[FileEntry]) -> Self {
        let compaction = branch
            .iter()
            .rposition(|entry| matches!(entry, FileEntry::Compaction { .. }));
        let newest_digest = branch.iter().rposition(|entry| {
            matches!(entry, FileEntry::CustomMessage { payload, .. }
                if payload.custom_type == HARNESS_DIGEST_CUSTOM_TYPE)
        });
        let snapshot_outranks_digest = compaction.is_some_and(|compaction| {
            matches!(&branch[compaction], FileEntry::Compaction { payload, .. }
                if payload.harness_digest.is_some())
                && newest_digest.is_none_or(|digest| digest < compaction)
        });
        Self {
            compaction,
            kept_digest: if snapshot_outranks_digest {
                None
            } else {
                newest_digest
            },
            summary_yields_snapshot: matches!(
                (newest_digest, compaction),
                (Some(digest), Some(compaction)) if digest > compaction
            ),
        }
    }
}

struct Planner<'a> {
    branch: &'a [FileEntry],
    digests: DigestPolicy,
    model: Option<ModelRef>,
    thinking_level: Option<&'a str>,
    entries: Vec<PlannedEntry>,
    /// Branch position of each planned entry.
    positions: Vec<usize>,
    skipped_rows: usize,
    /// Tool name of each assistant tool call planned so far, by call id.
    tool_names: HashMap<String, String>,
}

impl<'a> Planner<'a> {
    fn new(branch: &'a [FileEntry]) -> Self {
        Self {
            branch,
            digests: DigestPolicy::new(branch),
            model: None,
            thinking_level: None,
            entries: Vec::new(),
            positions: Vec::new(),
            skipped_rows: 0,
            tool_names: HashMap::new(),
        }
    }

    fn push(&mut self, position: usize, draft: EntryDraft, head: PlannedHead) {
        self.entries.push(PlannedEntry { draft, head });
        self.positions.push(position);
    }

    fn plan_row(&mut self, position: usize) -> Result<(), ImportError> {
        let branch = self.branch;
        let entry = &branch[position];
        let id = entry.id().unwrap_or_default();
        let timestamp = timestamp_to_millis(entry.timestamp());
        match entry {
            FileEntry::Header { .. } => {}
            FileEntry::Message { message, .. } => {
                let message = self.named_tool_result(message);
                let draft = message_draft(&message, id)?;
                self.push(position, draft, PlannedHead::None);
            }
            FileEntry::ThinkingLevelChange { payload, .. } => {
                self.thinking_level = Some(payload.thinking_level.as_str());
            }
            FileEntry::ModelChange { payload, .. } => {
                self.model = Some(ModelRef {
                    provider: payload.provider.clone(),
                    model_id: payload.model_id.clone(),
                });
            }
            FileEntry::Compaction { payload, .. } => {
                let (draft, head) = self.compaction(position, payload, id, timestamp)?;
                self.push(position, draft, head);
            }
            FileEntry::BranchSummary { payload, .. } => {
                let model = if payload.summary.is_empty() {
                    None
                } else {
                    llm_view(
                        &AgentMessage::BranchSummary(BranchSummaryMessage {
                            summary: payload.summary.clone(),
                            from_id: payload.from_id.clone(),
                            timestamp,
                        }),
                        id,
                    )?
                };
                let data = BranchSummaryData {
                    summary: payload.summary.clone(),
                    from_id: payload.from_id.clone(),
                    details: payload.details.clone(),
                    from_hook: payload.from_hook,
                    timestamp,
                };
                let draft = BRANCH_SUMMARY_ENTRY.draft(&typed(model, data))?;
                self.push(position, draft, PlannedHead::None);
            }
            FileEntry::Custom { payload, .. } => {
                let data = CustomStateData {
                    custom_type: payload.custom_type.clone(),
                    data: payload.data.clone(),
                };
                let draft = CUSTOM_STATE_ENTRY.draft(&typed(None, data))?;
                self.push(position, draft, PlannedHead::None);
            }
            FileEntry::CustomMessage { payload, .. } => {
                let content: UserContent = convert(&payload.content, id)?;
                // Older harness digests stay out of context, as in the old
                // engine; their content then rides in data, like a
                // display-only row's.
                let draft = if payload.custom_type == HARNESS_DIGEST_CUSTOM_TYPE
                    && self.digests.kept_digest != Some(position)
                {
                    CUSTOM_ENTRY.draft(&typed(
                        None,
                        CustomEntryData {
                            custom_type: payload.custom_type.clone(),
                            content: Some(content),
                            display: payload.display,
                            details: payload.details.clone(),
                            input: false,
                        },
                    ))?
                } else {
                    custom_entry_draft(
                        payload.custom_type.as_str(),
                        content,
                        payload.display,
                        payload.details.clone(),
                        timestamp,
                    )?
                };
                self.push(position, draft, PlannedHead::None);
            }
            // Service tiers have no durable agent field; child usage is
            // already folded into its assistant message by the parser.
            FileEntry::ServiceTierChange { .. }
            | FileEntry::ChildUsageAttributed { .. }
            | FileEntry::Label { .. }
            | FileEntry::SessionInfo { .. }
            | FileEntry::SessionState { .. }
            | FileEntry::GitState { .. }
            | FileEntry::Unknown { .. } => self.skipped_rows += 1,
        }
        Ok(())
    }

    /// `message`, with a legacy tool result's missing `toolName` taken from
    /// the assistant tool call it answers; records assistant tool calls.
    fn named_tool_result<'m>(&mut self, message: &'m AgentMessage) -> Cow<'m, AgentMessage> {
        match message {
            AgentMessage::Assistant(assistant) => {
                for block in &assistant.content {
                    if let AssistantContentBlock::ToolCall(call) = block {
                        self.tool_names.insert(call.id.clone(), call.name.clone());
                    }
                }
                Cow::Borrowed(message)
            }
            AgentMessage::ToolResult(result) if result.tool_name.is_empty() => {
                match self.tool_names.get(&result.tool_call_id) {
                    Some(name) => {
                        let mut result = result.clone();
                        result.tool_name.clone_from(name);
                        Cow::Owned(AgentMessage::ToolResult(result))
                    }
                    None => Cow::Borrowed(message),
                }
            }
            _ => Cow::Borrowed(message),
        }
    }

    /// A `pi.compaction` entry whose range starts at the first imported
    /// entry from `firstKeptEntryId` up to the compaction, or at itself when
    /// nothing before it is kept. Legacy rows do not record why they ran:
    /// rows with custom instructions came from `/compact` (`manual`), the
    /// rest are recorded as `threshold`.
    fn compaction(
        &self,
        position: usize,
        payload: &CompactionEntry,
        id: &str,
        timestamp: u64,
    ) -> Result<(EntryDraft, PlannedHead), ImportError> {
        let first_kept = self.branch[..position]
            .iter()
            .position(|entry| entry.id() == Some(payload.first_kept_entry_id.as_str()));
        let head = first_kept
            .and_then(|first_kept| {
                self.positions
                    .iter()
                    .position(|&planned| planned >= first_kept)
            })
            .map_or(PlannedHead::SelfEntry, PlannedHead::Planned);
        let harness_digest =
            if self.digests.compaction == Some(position) && self.digests.summary_yields_snapshot {
                None
            } else {
                payload.harness_digest.clone()
            };
        let harness_state_fingerprint = if harness_digest.is_some() {
            payload.harness_state_fingerprint.clone()
        } else {
            None
        };
        let summary = AgentMessage::CompactionSummary(CompactionSummaryMessage {
            summary: payload.summary.clone(),
            tokens_before: payload.tokens_before,
            retained_message_count: None,
            custom_instructions: payload.custom_instructions.clone(),
            harness_digest,
            harness_state_fingerprint,
            timestamp,
        });
        let reason = if payload.custom_instructions.is_some() {
            CompactionReason::Manual
        } else {
            CompactionReason::Threshold
        };
        let draft =
            COMPACTION_ENTRY.draft(&typed(llm_view(&summary, id)?, CompactionData { reason }))?;
        Ok((draft, head))
    }
}

/// The durable entry of one `message` row.
fn message_draft(message: &AgentMessage, id: &str) -> Result<EntryDraft, ImportError> {
    let model = llm_view(message, id)?;
    Ok(match message {
        AgentMessage::User(_) => untyped(USER_ENTRY.kind(), model),
        AgentMessage::Assistant(_) => untyped(ASSISTANT_ENTRY.kind(), model),
        AgentMessage::ToolResult(_) => TOOL_RESULT_ENTRY.draft(&typed(
            model,
            ToolResultData {
                diagnostics: Vec::new(),
            },
        ))?,
        AgentMessage::BashExecution(bash) => bash_entry_draft(
            BashEntryData {
                command: bash.command.clone(),
                output: bash.output.clone(),
                exit_code: bash.exit_code,
                cancelled: bash.cancelled,
                truncated: bash.truncated,
                full_output_path: bash.full_output_path.clone(),
                exclude_from_context: bash.exclude_from_context,
            },
            bash.timestamp,
        )?,
        AgentMessage::Custom(custom) => custom_entry_draft(
            custom.custom_type.as_str(),
            convert(&custom.content, id)?,
            custom.display,
            custom.details.clone(),
            custom.timestamp,
        )?,
        AgentMessage::BranchSummary(summary) => BRANCH_SUMMARY_ENTRY.draft(&typed(
            model,
            BranchSummaryData {
                summary: summary.summary.clone(),
                from_id: summary.from_id.clone(),
                details: None,
                from_hook: None,
                timestamp: summary.timestamp,
            },
        ))?,
        AgentMessage::CompactionSummary(summary) => {
            COMPACTION_SUMMARY_ENTRY.draft(&typed(model, summary.clone()))?
        }
    })
}

fn untyped(kind: &str, model: Option<Vec<Message>>) -> EntryDraft {
    EntryDraft {
        kind: kind.to_owned(),
        model,
        data: None,
        head: None,
        edits: None,
    }
}

fn typed<D>(model: Option<Vec<Message>>, data: D) -> TypedEntryDraft<D> {
    TypedEntryDraft {
        model,
        data,
        head: None,
        edits: None,
    }
}

/// What the old engine sent the model for `message`, in pi-ai shapes;
/// `None` when it sent nothing.
fn llm_view(message: &AgentMessage, id: &str) -> Result<Option<Vec<Message>>, ImportError> {
    let converted = convert_to_llm(std::slice::from_ref(message));
    if converted.is_empty() {
        return Ok(None);
    }
    converted
        .iter()
        .map(|message| match message {
            // A nameless tool result went out with an empty name; the old
            // shape omits an empty name, the pi-ai shape requires it.
            AgentMessage::ToolResult(result) if result.tool_name.is_empty() => {
                let mut value = to_value(message, id)?;
                if let Some(object) = value.as_object_mut() {
                    object.insert("toolName".to_owned(), serde_json::Value::from(""));
                }
                serde_json::from_value(value).map_err(|source| ImportError::Convert {
                    entry_id: id.to_owned(),
                    source,
                })
            }
            _ => convert(message, id),
        })
        .collect::<Result<Vec<Message>, _>>()
        .map(Some)
}

fn to_value<T: Serialize>(value: &T, id: &str) -> Result<serde_json::Value, ImportError> {
    serde_json::to_value(value).map_err(|source| ImportError::Convert {
        entry_id: id.to_owned(),
        source,
    })
}

/// Old-engine (`eukhe_types::ai`/`session`) JSON into its pi-ai shape: both
/// use the same camelCase wire form.
fn convert<T: Serialize, U: DeserializeOwned>(value: &T, id: &str) -> Result<U, ImportError> {
    serde_json::to_value(value)
        .and_then(serde_json::from_value)
        .map_err(|source| ImportError::Convert {
            entry_id: id.to_owned(),
            source,
        })
}
