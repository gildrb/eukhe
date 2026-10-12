//! `SessionManager` part 2: queries, branches, labels, status entries.
//! Port of the tail of core/session-manager.ts (getBranch/getTree/branch*).

use eukhe_types::session::{AgentMessage, FileEntry, GitContext, GitStateEntry, LabelEntry};

use super::manager::SessionManager;
use super::CONTENT_ENTRY_TYPES;

impl SessionManager {
    /// True when the session holds user-meaningful content beyond the default
    /// creation prefix (`model_change`, `thinking_level_change`, `service_tier_change`).
    #[must_use]
    pub fn has_user_content(&self) -> bool {
        let owned_entries = self.get_entries();
        let content_entries: Vec<&FileEntry> = owned_entries
            .iter()
            .filter(|entry| CONTENT_ENTRY_TYPES.contains(&entry_type(entry)))
            .collect();
        let mut start = 0usize;
        if matches!(
            content_entries.get(start),
            Some(FileEntry::ModelChange { .. })
        ) {
            start += 1;
        }
        if matches!(
            content_entries.get(start),
            Some(FileEntry::ThinkingLevelChange { .. })
        ) {
            start += 1;
        }
        if matches!(
            content_entries.get(start),
            Some(FileEntry::ServiceTierChange { .. })
        ) {
            start += 1;
        }
        content_entries.len() > start
    }

    /// Append a `git_state` row; returns the new entry id.
    pub fn append_git_state(&mut self, git: GitContext) -> String {
        let base = self.next_base();
        self.append_entry(FileEntry::GitState {
            payload: GitStateEntry { git },
            base,
        })
    }

    /// Append `git` as a `git_state` row when it differs from the nearest
    /// git context on the active branch (or the header); returns the new id.
    pub fn record_git_state_if_changed(&mut self, git: GitContext) -> Option<String> {
        if self.active_git_context().as_ref() == Some(&git) {
            return None;
        }
        Some(self.append_git_state(git))
    }

    fn active_git_context(&self) -> Option<GitContext> {
        if let Some(context) = self.latest_git_context() {
            return Some(context);
        }
        match self.get_header() {
            Some(header) => header.git.clone(),
            None => None,
        }
    }

    /// Append a label change for a target entry.
    ///
    /// # Panics
    ///
    /// Asserts that the target entry exists.
    pub fn append_label_change(&mut self, target_id: &str, label: Option<&str>) -> String {
        assert!(
            self.get_entry_by_id(target_id).is_some(),
            "Entry {target_id} not found"
        );
        let base = self.next_base();
        let timestamp = base.timestamp.clone().unwrap_or_default();
        let id = self.append_entry(FileEntry::Label {
            payload: LabelEntry {
                target_id: target_id.to_string(),
                label: label.map(str::to_string),
            },
            base,
        });
        self.apply_label_entry(target_id, label, &timestamp);
        id
    }

    /// `getUserMessagesForForking`: user messages with their text, in file
    /// order (TS `AgentSession.getUserMessagesForForking`).
    #[must_use]
    pub fn get_user_messages_for_forking(&self) -> Vec<(String, String)> {
        self.get_entries()
            .iter()
            .filter_map(|entry| match entry {
                FileEntry::Message {
                    message: AgentMessage::User(user),
                    ..
                } => {
                    let text = user.content.text();
                    let id = entry.id().map(str::to_string)?;
                    (!text.is_empty()).then_some((id, text))
                }
                _ => None,
            })
            .collect()
    }

    /// The ancestor path (file order) ending at `from_id` (default: leaf).
    pub fn get_branch(&self, from_id: Option<&str>) -> Vec<&FileEntry> {
        let start = from_id
            .map(str::to_string)
            .or_else(|| self.get_leaf_id().map(str::to_string));
        let mut path = Vec::new();
        let mut current = start;
        while let Some(id) = current {
            let Some(entry) = self.get_entry_by_id(&id) else {
                break;
            };
            path.push(entry);
            current = entry.parent_id().map(str::to_string);
        }
        path.reverse();
        path
    }

    /// Move the leaf to `branch_from_id` (the session keeps its file).
    ///
    /// # Panics
    ///
    /// Asserts that the target entry exists.
    pub fn branch(&mut self, branch_from_id: &str) {
        assert!(
            self.get_entry_by_id(branch_from_id).is_some(),
            "Entry {branch_from_id} not found"
        );
        self.set_leaf_id(Some(branch_from_id));
    }

    /// Branch with a summary message describing what the abandoned branch held.
    ///
    /// # Panics
    ///
    /// Asserts that the given branch target entry exists.
    pub fn branch_with_summary(
        &mut self,
        branch_from_id: Option<&str>,
        summary: &str,
        details: Option<serde_json::Value>,
        from_hook: Option<bool>,
        usage: Option<eukhe_types::ai::Usage>,
    ) -> String {
        if let Some(branch_from_id) = branch_from_id {
            assert!(
                self.get_entry_by_id(branch_from_id).is_some(),
                "Entry {branch_from_id} not found"
            );
        }
        self.set_leaf_id(branch_from_id);
        let base = self.next_base();
        self.append_entry(FileEntry::BranchSummary {
            payload: eukhe_types::session::BranchSummaryEntry {
                from_id: branch_from_id.map_or_else(|| "root".to_string(), str::to_string),
                summary: summary.to_string(),
                details,
                from_hook,
                usage,
            },
            base,
        })
    }
}

fn entry_type(entry: &FileEntry) -> &'static str {
    match entry {
        FileEntry::Header { .. } => "session",
        FileEntry::Message { .. } => "message",
        FileEntry::ThinkingLevelChange { .. } => "thinking_level_change",
        FileEntry::ServiceTierChange { .. } => "service_tier_change",
        FileEntry::ModelChange { .. } => "model_change",
        FileEntry::Compaction { .. } => "compaction",
        FileEntry::BranchSummary { .. } => "branch_summary",
        FileEntry::Custom { .. } => "custom",
        FileEntry::ChildUsageAttributed { .. } => "child_usage_attributed",
        FileEntry::CustomMessage { .. } => "custom_message",
        FileEntry::Label { .. } => "label",
        FileEntry::SessionInfo { .. } => "session_info",
        FileEntry::SessionState { .. } => "session_state",
        FileEntry::GitState { .. } => "git_state",
        FileEntry::Unknown { .. } => "unknown",
    }
}

#[cfg(test)]
mod tests {
    use crate::session::manager::SessionManager;
    use eukhe_types::session::AgentMessage;

    fn assistant() -> AgentMessage {
        AgentMessage::Assistant(eukhe_types::ai::AssistantMessage {
            content: vec![],
            api: "openai-completions".to_string(),
            provider: "openai".to_string(),
            model: "m".to_string(),
            response_model: None,
            response_id: None,
            diagnostics: None,
            usage: eukhe_types::ai::Usage::default(),
            stop_reason: eukhe_types::ai::StopReason::Stop,
            stop_reason_raw: None,
            error_message: None,
            timestamp: 0,
            rest: serde_json::Map::default(),
        })
    }

    fn user(text: &str) -> AgentMessage {
        AgentMessage::User(eukhe_types::ai::UserMessage {
            content: eukhe_types::ai::UserContent::Text(text.to_string()),
            timestamp: 0,
            rest: serde_json::Map::default(),
        })
    }

    #[test]
    fn branch_and_summary() {
        let tmp = tempfile::tempdir().unwrap();
        let mut manager = SessionManager::in_memory(tmp.path());
        let a = manager.append_message(user("first"));
        let b = manager.append_message(assistant());
        assert_eq!(manager.get_branch(None).len(), 2);
        // Branch from a: the path is just [a].
        manager.branch(&a);
        assert_eq!(manager.get_branch(None).len(), 1);
        // Append after branching creates a sibling of b.
        let summary_id = manager.branch_with_summary(Some(&a), "went back", None, None, None);
        assert!(manager.get_entry_by_id(&summary_id).is_some());
        // b still exists (sibling branch).
        assert!(manager.get_entry_by_id(&b).is_some());
    }

    #[test]
    fn user_content_detection() {
        let tmp = tempfile::tempdir().unwrap();
        let mut manager = SessionManager::in_memory(tmp.path());
        // Creation prefix only: no user content.
        manager.append_model_change("openai", "m");
        manager.append_thinking_level_change("medium");
        assert!(!manager.has_user_content());
        manager.append_message(user("real content"));
        assert!(manager.has_user_content());
    }

    #[test]
    fn labels_on_active_branch() {
        let tmp = tempfile::tempdir().unwrap();
        let mut manager = SessionManager::in_memory(tmp.path());
        let a = manager.append_message(user("first"));
        let label_entry = manager.append_label_change(&a, Some("checkpoint"));
        assert!(manager.get_entry_by_id(&label_entry).is_some());
        assert_eq!(manager.get_label(&a).as_deref(), Some("checkpoint"));
        // Clear the label.
        manager.append_label_change(&a, None);
        assert_eq!(manager.get_label(&a), None);
    }
}
