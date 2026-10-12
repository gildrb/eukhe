//! The append concern (moved with its concern): the in-memory append
//! family - messages, changes, compactions, customs, attributions, session
//! info/state - and the leaf/label mutators. Appends never touch the disk.

use super::{
    format_iso_now, generate_id, AgentMessage, ChildUsageOrigin, EntryBase, FileEntry,
    SessionManager, SessionState, SessionStateStatus,
};

impl SessionManager {
    /// Push one entry onto the chain as the new leaf; returns its id.
    pub(crate) fn append_entry(&mut self, entry: FileEntry) -> String {
        if let Some(window) = &mut self.window {
            window.append_entry(entry.clone());
        }
        let id = entry.id().map(str::to_string).unwrap_or_default();
        self.file_entries.push(entry);
        if !id.is_empty() {
            self.by_id.insert(id.clone(), self.file_entries.len() - 1);
            self.leaf_id = Some(id.clone());
        }
        id
    }

    pub(crate) fn next_base(&self) -> EntryBase {
        EntryBase {
            id: Some(if self.window.is_some() {
                uuid::Uuid::new_v4().to_string()
            } else {
                generate_id(&self.by_id)
            }),
            parent_id: self.leaf_id.clone(),
            timestamp: Some(format_iso_now()),
            rest: eukhe_types::JsonMap::new(),
        }
    }

    /// Append a conversation message; returns the new entry id.
    pub fn append_message(&mut self, message: AgentMessage) -> String {
        let base = self.next_base();
        self.append_entry(FileEntry::Message { message, base })
    }

    /// Append a thinking-level change; returns the new entry id.
    pub fn append_thinking_level_change(&mut self, thinking_level: &str) -> String {
        let base = self.next_base();
        self.append_entry(FileEntry::ThinkingLevelChange {
            payload: eukhe_types::session::ThinkingLevelChangeEntry {
                thinking_level: thinking_level.to_string(),
            },
            base,
        })
    }

    /// Append a service-tier change; returns the new entry id.
    pub fn append_service_tier_change(
        &mut self,
        service_tier: Option<eukhe_types::ai::ServiceTier>,
    ) -> String {
        let base = self.next_base();
        self.append_entry(FileEntry::ServiceTierChange {
            payload: eukhe_types::session::ServiceTierChangeEntry { service_tier },
            base,
        })
    }

    /// Append a model change; returns the new entry id.
    pub fn append_model_change(&mut self, provider: &str, model_id: &str) -> String {
        let base = self.next_base();
        self.append_entry(FileEntry::ModelChange {
            payload: eukhe_types::session::ModelChangeEntry {
                provider: provider.to_string(),
                model_id: model_id.to_string(),
            },
            base,
        })
    }

    /// `appendCompaction`: record the compaction. The full typed payload is
    /// kept (TS keeps `details`, `fromHook`, `customInstructions`, `usage`,
    /// and `harnessDigest` on the row; later compactions and branch
    /// summarization read them back).
    pub fn append_compaction(&mut self, payload: eukhe_types::session::CompactionEntry) -> String {
        let base = self.next_base();
        self.append_entry(FileEntry::Compaction { payload, base })
    }

    /// Append a custom entry; returns the new entry id.
    pub fn append_custom_entry(
        &mut self,
        custom_type: &str,
        data: Option<serde_json::Value>,
    ) -> String {
        let base = self.next_base();
        self.append_entry(FileEntry::Custom {
            payload: eukhe_types::session::CustomEntry {
                custom_type: custom_type.to_string(),
                data,
                rest: serde_json::Map::default(),
            },
            base,
        })
    }

    /// Append a custom message entry (compaction/refine notices, prompts).
    pub fn append_custom_message(
        &mut self,
        custom_type: &str,
        content: eukhe_types::ai::UserContent,
        display: bool,
        details: Option<serde_json::Value>,
    ) -> String {
        let base = self.next_base();
        self.append_entry(FileEntry::CustomMessage {
            payload: eukhe_types::session::CustomMessageEntry {
                custom_type: custom_type.to_string(),
                content,
                details,
                display,
                rest: serde_json::Map::default(),
            },
            base,
        })
    }

    /// Fold child usage into the target assistant message and record the
    /// attribution entry.
    ///
    /// # Errors
    ///
    /// Returns an invalid-input error when the target assistant message
    /// entry is missing.
    pub fn append_child_usage_attribution(
        &mut self,
        target_id: &str,
        child_usage: eukhe_types::ai::Usage,
        aggregate_usage: eukhe_types::ai::Usage,
        origin: Option<ChildUsageOrigin>,
    ) -> std::io::Result<String> {
        let target_index = self.by_id.get(target_id).copied().filter(|&index| {
            matches!(
                self.file_entries[index],
                FileEntry::Message {
                    message: AgentMessage::Assistant(_),
                    ..
                }
            )
        });
        let target_index = target_index.ok_or_else(|| {
            // TS `appendChildUsageAttribution` throws the same text; the
            // caller treats a failed append as recoverable bookkeeping.
            std::io::Error::new(
                std::io::ErrorKind::InvalidInput,
                format!("Assistant message entry {target_id} not found"),
            )
        })?;
        let base = self.next_base();
        let id = self.append_entry(FileEntry::ChildUsageAttributed {
            payload: eukhe_types::session::ChildUsageAttributionEntry {
                target_id: target_id.to_string(),
                child_usage,
                aggregate_usage,
                origin,
            },
            base,
        });
        if let FileEntry::Message {
            message: AgentMessage::Assistant(assistant),
            ..
        } = &mut self.file_entries[target_index]
        {
            assistant.usage = aggregate_usage;
        }
        Ok(id)
    }

    /// Append a session-info row (the session name); returns the new entry
    /// id.
    pub fn append_session_info(&mut self, name: &str) -> String {
        let base = self.next_base();
        self.append_entry(FileEntry::SessionInfo {
            payload: eukhe_types::session::SessionInfoEntry {
                name: Some(name.trim().to_string()),
            },
            base,
        })
    }

    /// Move the leaf (used by branch/branchWithSummary).
    ///
    /// # Panics
    ///
    /// Asserts that the manager holds no windowed store: hydrate the full
    /// session history first.
    pub(crate) fn set_leaf_id(&mut self, leaf_id: Option<&str>) {
        assert!(
            self.window.is_none(),
            "hydrate full session history before this operation"
        );
        self.leaf_id = leaf_id.map(str::to_string);
    }

    /// Apply a label entry to the label index (last label wins).
    pub(crate) fn apply_label_entry(
        &mut self,
        target_id: &str,
        label: Option<&str>,
        timestamp: &str,
    ) {
        if let Some(label) = label {
            self.labels_by_id
                .insert(target_id.to_string(), label.to_string());
            self.label_timestamps_by_id
                .insert(target_id.to_string(), timestamp.to_string());
        } else {
            self.labels_by_id.remove(target_id);
            self.label_timestamps_by_id.remove(target_id);
        }
    }

    /// Append a session-state row; returns the new entry id.
    pub fn append_session_state(&mut self, status: SessionStateStatus) -> String {
        let base = self.next_base();
        self.append_entry(FileEntry::SessionState {
            payload: eukhe_types::session::SessionStateEntry {
                state: SessionState { status },
            },
            base,
        })
    }
}
