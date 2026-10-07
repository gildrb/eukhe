//! The session tree of a durable session, projected onto the wire tree the
//! `/tree` view reads (TS `getFlatTree` / `getLeafId` /
//! `getUserMessagesForForking`).
//!
//! A durable session has no entry tree: its user-facing conversations (the
//! root and the ownerless forks that tree moves and forks create) each hold
//! a linear history, and a fork inherits its parent's history through its
//! fork point. Entry ids are session-global, so the tree is the union of
//! every conversation's own entries, each parented on the previous shown
//! entry of its conversation (the first one on the shown entry its fork
//! inherited through). Only entries the transcript shows become nodes
//! (messages, custom rows, bash runs, compactions, branch summaries);
//! bookkeeping entries are skipped and their children re-parent on the
//! nearest shown ancestor. The leaf is the main conversation's newest shown
//! entry.

use std::collections::HashMap;
use std::sync::Arc;

use eukhe_chord::context::Context;
use eukhe_core::durable::{BranchSummaryData, BRANCH_SUMMARY_ENTRY, CUSTOM_ENTRY};
use eukhe_durable::entries::{COMPACTION_ENTRY, USER_ENTRY};
use eukhe_durable::harness::Harness;
use eukhe_durable::session::SessionResult;
use eukhe_durable::types::{
    ConversationId, ConversationParent, ConversationQuery, ConversationRecord, Cursor, EntryId,
    EntryQuery, EntryRecord, Storage,
};
use eukhe_types::pi_ai::{ContentBlockText, Message, UserContent, UserContentBlock};
use serde_json::{json, Map, Value};

use crate::worker::durable_host::wire_messages::{
    assistant_context_tokens, entry_wire_message_with,
};

/// Records read per storage scan.
const PAGE_SIZE: usize = 256;

/// One shown entry of the tree.
#[derive(Debug, Clone)]
pub(crate) struct TreeEntry {
    pub(crate) record: EntryRecord,
    /// The nearest shown ancestor (`parentId`); `None` at a root.
    pub(crate) parent: Option<EntryId>,
    /// The context size the answer before it measured (a compaction's
    /// `tokensBefore`).
    tokens_before: u64,
}

/// One user-facing conversation: where its own history starts and where it
/// ends.
#[derive(Debug, Clone, Copy)]
pub(crate) struct ConversationTip {
    pub(crate) id: ConversationId,
    /// Its newest visible entry (own, else the inherited fork point);
    /// `None` for an empty conversation without a parent.
    pub(crate) tip: Option<EntryId>,
}

/// The projected tree of one session.
#[derive(Debug, Default)]
pub(crate) struct SessionTree {
    /// Shown entries in id (creation) order.
    entries: Vec<TreeEntry>,
    by_id: HashMap<EntryId, usize>,
    /// The user-facing conversations, ascending.
    conversations: Vec<ConversationTip>,
    /// The main conversation's newest shown entry.
    leaf: Option<EntryId>,
}

/// Per conversation: its own entries with the shown leaf and context size
/// through each, and where it inherits from.
struct Lineage {
    parent: Option<ConversationParent>,
    own: Vec<(EntryId, Option<EntryId>, u64)>,
}

/// The shown leaf and context size through `at`, an entry visible to
/// `conversation` (its own, or inherited through its ancestry).
fn through(
    lineages: &HashMap<ConversationId, Lineage>,
    conversation: ConversationId,
    at: EntryId,
) -> (Option<EntryId>, u64) {
    let mut current = conversation;
    while let Some(lineage) = lineages.get(&current) {
        let index = lineage.own.partition_point(|(id, _, _)| *id <= at);
        if let Some(index) = index.checked_sub(1) {
            return (lineage.own[index].1, lineage.own[index].2);
        }
        match lineage.parent {
            Some(parent) => current = parent.conversation_id,
            None => break,
        }
    }
    (None, 0)
}

impl SessionTree {
    /// Read the tree of `harness` with `main` as the main conversation.
    ///
    /// # Errors
    ///
    /// The storage cannot be scanned.
    pub(crate) async fn load(
        harness: &Harness,
        main: ConversationId,
        cx: &Context,
    ) -> SessionResult<Self> {
        let storage = Arc::clone(harness.storage());
        let cx = cx.clone();
        harness
            .read_on_line(async move { Self::scan(storage.as_ref(), main, &cx).await })
            .await
    }

    async fn scan(
        storage: &dyn Storage,
        main: ConversationId,
        cx: &Context,
    ) -> SessionResult<Self> {
        let conversations = user_conversations(storage, cx).await?;
        let mut lineages: HashMap<ConversationId, Lineage> = HashMap::new();
        let mut tree = Self::default();
        for conversation in conversations {
            let (base, base_tokens) = conversation.parent.map_or((None, 0), |parent| {
                through(&lineages, parent.conversation_id, parent.at)
            });
            let mut lineage = Lineage {
                parent: conversation.parent,
                own: Vec::new(),
            };
            let (mut leaf, mut tokens) = (base, base_tokens);
            for record in own_entries(storage, &conversation, cx).await? {
                let id = record.id;
                if entry_wire_message_with(&record, tokens).is_some() {
                    let next_tokens = assistant_context_tokens(&record).unwrap_or(tokens);
                    tree.entries.push(TreeEntry {
                        record,
                        parent: leaf,
                        tokens_before: tokens,
                    });
                    leaf = Some(id);
                    tokens = next_tokens;
                }
                lineage.own.push((id, leaf, tokens));
            }
            let tip = lineage
                .own
                .last()
                .map(|(id, _, _)| *id)
                .or_else(|| conversation.parent.map(|parent| parent.at));
            tree.conversations.push(ConversationTip {
                id: conversation.id,
                tip,
            });
            if conversation.id == main {
                tree.leaf = leaf;
            }
            lineages.insert(conversation.id, lineage);
        }
        tree.entries.sort_by_key(|entry| entry.record.id);
        tree.by_id = tree
            .entries
            .iter()
            .enumerate()
            .map(|(index, entry)| (entry.record.id, index))
            .collect();
        Ok(tree)
    }

    /// The main conversation's newest shown entry.
    pub(crate) fn leaf(&self) -> Option<EntryId> {
        self.leaf
    }

    pub(crate) fn entry(&self, id: EntryId) -> Option<&TreeEntry> {
        self.by_id.get(&id).map(|index| &self.entries[*index])
    }

    pub(crate) fn conversations(&self) -> &[ConversationTip] {
        &self.conversations
    }

    /// `get_session_tree`'s `flatNodes`: every shown entry in creation
    /// order with its label (`labels(id)` answers `(label, timestamp)`).
    pub(crate) fn flat_nodes(
        &self,
        labels: impl Fn(&str) -> Option<(String, String)>,
    ) -> Vec<Value> {
        self.entries
            .iter()
            .filter_map(|entry| {
                let id = entry.record.id.to_string();
                let mut node = json!({ "entry": entry_json(entry)? });
                if let Some((label, timestamp)) = labels(&id) {
                    node["label"] = json!(label);
                    node["labelTimestamp"] = json!(timestamp);
                }
                Some(node)
            })
            .collect()
    }

    /// The wire entry of one shown entry.
    pub(crate) fn entry_json(&self, id: EntryId) -> Option<Value> {
        self.entry(id).and_then(entry_json)
    }

    /// Every shown entry as typed session entries (the branch-summary
    /// collection input).
    pub(crate) fn file_entries(&self) -> Vec<eukhe_types::session::FileEntry> {
        self.entries
            .iter()
            .filter_map(entry_json)
            .filter_map(|entry| serde_json::from_value(entry).ok())
            .collect()
    }

    /// `get_user_messages_for_forking`: the user messages with text, in
    /// creation order (`{ entryId, text }`).
    pub(crate) fn user_messages_for_forking(&self) -> Vec<Value> {
        self.entries
            .iter()
            .filter_map(|entry| {
                let text = user_entry_text(&entry.record)?;
                Some(json!({ "entryId": entry.record.id.to_string(), "text": text }))
            })
            .collect()
    }
}

/// The text of a user-message entry (TS `_extractUserMessageText`: the
/// string content, or the text blocks joined); `None` for other entries
/// and for user messages without text.
pub(crate) fn user_entry_text(record: &EntryRecord) -> Option<String> {
    if record.kind != USER_ENTRY.kind() {
        return None;
    }
    let Some(Message::User(message)) = record.model.as_deref().and_then(<[Message]>::first) else {
        return None;
    };
    let text = match &message.content {
        UserContent::Text(text) => text.clone(),
        UserContent::Blocks(blocks) => blocks
            .iter()
            .filter_map(UserContentBlock::text_block)
            .collect::<String>(),
    };
    (!text.is_empty()).then_some(text)
}

/// Whether the entry is a custom message (TS `custom_message`).
pub(crate) fn is_custom_entry(record: &EntryRecord) -> bool {
    record.kind == CUSTOM_ENTRY.kind()
}

/// The text a custom-message entry re-enters in the editor (TS: the string
/// content, or the concatenated text blocks); `None` without text.
pub(crate) fn custom_entry_text(record: &EntryRecord) -> Option<String> {
    let message = entry_wire_message_with(record, 0)?;
    match message.get("content") {
        Some(Value::String(text)) => Some(text.clone()),
        Some(Value::Array(blocks)) => {
            let text: String = blocks
                .iter()
                .filter(|block| block.get("type").and_then(Value::as_str) == Some("text"))
                .filter_map(|block| block.get("text").and_then(Value::as_str))
                .collect();
            Some(text).filter(|text| !text.is_empty())
        }
        _ => None,
    }
}

/// The TS `SessionEntry` of one shown entry: `{type, id, parentId,
/// timestamp, ...payload}`.
fn entry_json(entry: &TreeEntry) -> Option<Value> {
    let record = &entry.record;
    let message = entry_wire_message_with(record, entry.tokens_before)?;
    let timestamp = message
        .get("timestamp")
        .and_then(Value::as_u64)
        .unwrap_or(0);
    let kind = record.kind.as_str();
    let mut object = Map::new();
    let entry_type = if kind == COMPACTION_ENTRY.kind() {
        "compaction"
    } else if kind == CUSTOM_ENTRY.kind() {
        "custom_message"
    } else if kind == BRANCH_SUMMARY_ENTRY.kind() {
        "branch_summary"
    } else {
        "message"
    };
    object.insert("type".to_owned(), json!(entry_type));
    object.insert("id".to_owned(), json!(record.id.to_string()));
    object.insert(
        "parentId".to_owned(),
        entry
            .parent
            .map_or(Value::Null, |parent| json!(parent.to_string())),
    );
    object.insert(
        "timestamp".to_owned(),
        json!(crate::util::iso_from_unix_ms(timestamp)),
    );
    match entry_type {
        "compaction" => {
            object.insert("summary".to_owned(), message["summary"].clone());
            let first_kept = record.head.unwrap_or(record.id);
            object.insert("firstKeptEntryId".to_owned(), json!(first_kept.to_string()));
            object.insert("tokensBefore".to_owned(), json!(entry.tokens_before));
        }
        "custom_message" => {
            for key in ["customType", "content", "details", "display"] {
                if let Some(value) = message.get(key) {
                    object.insert(key.to_owned(), value.clone());
                }
            }
        }
        "branch_summary" => {
            let data: BranchSummaryData =
                serde_json::from_value(Value::from(record.data.as_ref()?)).ok()?;
            object.insert("fromId".to_owned(), json!(data.from_id));
            object.insert("summary".to_owned(), json!(data.summary));
            if let Some(details) = data.details {
                object.insert("details".to_owned(), details);
            }
            if let Some(from_hook) = data.from_hook {
                object.insert("fromHook".to_owned(), json!(from_hook));
            }
        }
        _ => {
            object.insert("message".to_owned(), message);
        }
    }
    Some(Value::Object(object))
}

/// The user-facing conversations (the root and the ownerless forks), in
/// ascending id order; task-owned conversations are internal.
async fn user_conversations(
    storage: &dyn Storage,
    cx: &Context,
) -> SessionResult<Vec<ConversationRecord>> {
    let query = ConversationQuery::default();
    let mut conversations = Vec::new();
    let mut cursor: Option<Cursor> = None;
    loop {
        let page = storage
            .scan_conversations(&query, PAGE_SIZE, cursor.as_ref(), cx)
            .await?;
        conversations.extend(
            page.items
                .into_iter()
                .filter(|record| record.owner.is_none()),
        );
        match page.next {
            Some(next) => cursor = Some(next),
            None => break,
        }
    }
    Ok(conversations)
}

/// The conversation's own entries, oldest first (its inherited history
/// ends at the fork point, so the scan starts after it).
async fn own_entries(
    storage: &dyn Storage,
    conversation: &ConversationRecord,
    cx: &Context,
) -> SessionResult<Vec<EntryRecord>> {
    let query = EntryQuery {
        conversation_id: conversation.id,
        min_entry_id: conversation
            .parent
            .map(|parent| EntryId::from_number(parent.at.get() + 1)),
        max_entry_id: None,
    };
    let mut entries = Vec::new();
    let mut cursor: Option<Cursor> = None;
    loop {
        let page = storage
            .scan_entries(&query, PAGE_SIZE, cursor.as_ref(), cx)
            .await?;
        entries.extend(
            page.items
                .into_iter()
                .filter(|entry| entry.conversation_id == conversation.id),
        );
        match page.next {
            Some(next) => cursor = Some(next),
            None => break,
        }
    }
    entries.reverse();
    Ok(entries)
}
