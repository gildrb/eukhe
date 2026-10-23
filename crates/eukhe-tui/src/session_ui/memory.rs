//! The chat memory in the interactive client: `/memory` opens the memory
//! tree (dated, labelled, expandable lines fetched level by level in the
//! background), every live `memory_update` lands as one transcript row,
//! and both keep the status line's `mem` gauge current. All of it is
//! display only.

use eukhe_types::daemon::{MemoryTreeReply, MemoryUpdate, MemoryZoom, MEMORY_TREE_CAPABILITY};

use super::chat_view::fetch;
use super::{key_event_to_id, AgentView, DaemonCommand, KeyEvent, Map, Result, SessionUi};
use crate::memory_block::{MemoryGauge, UpdateTiming};
use crate::memory_tree::{MemoryTreeAction, MemoryTreeFetch, MemoryTreeView};

/// One landed `get_memory_tree` level for the tree opened under `epoch`.
pub(crate) struct MemoryTreeUpdate {
    pub epoch: u64,
    pub fetch: MemoryTreeFetch,
}

impl SessionUi {
    /// `/memory` (`/memory view`): open the memory tree at once and fetch its top level
    /// (the view's lines) in the background. Arguments keep the text in
    /// the editor with the usage; a daemon without the `memory_tree` lane
    /// says so.
    pub(super) fn handle_memory_command(&mut self, args: &str, text: &str, view: &mut AgentView) {
        if !args.trim().is_empty() {
            view.editor.set_text(text);
            self.error_row("Usage: /memory [view|model]", view);
            return;
        }
        if !self
            .client
            .supports_server_capability(MEMORY_TREE_CAPABILITY)
        {
            self.error_row(
                "this daemon does not serve the memory tree; restart it to update",
                view,
            );
            return;
        }
        self.memory_tree_epoch += 1;
        view.memory_tree = Some(MemoryTreeView::new());
        self.spawn_memory_tree_fetch(/*node*/ None);
        self.dirty = true;
    }

    /// Fetch one level of the open tree (`None`: the view's lines) off the
    /// key path; the run loop folds the answer in.
    fn spawn_memory_tree_fetch(&self, node: Option<MemoryZoom>) {
        let epoch = self.memory_tree_epoch;
        let updates = self.memory_tree_updates.clone();
        let client = self.client.clone();
        let request = DaemonCommand::GetMemoryTree {
            id: None,
            active_session_id: self.active_session_id.clone(),
            node,
            rest: Map::default(),
        };
        tokio::spawn(async move {
            let reply = fetch::<MemoryTreeReply>(&client, request, "get_memory_tree")
                .await
                .map(|reply| reply.tree);
            // The run loop owns the receiver; a closed loop has no tree
            // left to fold the level into.
            let _ = updates.send(MemoryTreeUpdate {
                epoch,
                fetch: MemoryTreeFetch { node, reply },
            });
        });
    }

    /// Fold a landed level into the open tree (a level of a tree since
    /// closed or reopened is dropped). The gauge stays with the open-time
    /// status and the live updates: a level's status is a snapshot from
    /// its request and may trail a newer `memory_update`.
    pub(crate) fn apply_memory_tree_update(
        &mut self,
        update: MemoryTreeUpdate,
        view: &mut AgentView,
    ) {
        if update.epoch != self.memory_tree_epoch {
            return;
        }
        if let Some(tree) = view.memory_tree.as_mut() {
            tree.apply(update.fetch);
            self.dirty = true;
        }
    }

    /// One key press while the tree is open: navigation stays in the
    /// tree, an opened line fetches its level, the close keys dismiss it.
    pub(super) fn handle_memory_tree_key(
        &mut self,
        key: KeyEvent,
        view: &mut AgentView,
    ) -> Result<()> {
        let Some(id) = key_event_to_id(&key) else {
            return Ok(());
        };
        // The tree consumes Ctrl+C (close, not exit): report the handled
        // press so the force-quit guard can disarm.
        if id == "ctrl+c" {
            self.exit_guard.note_ctrl_c_handled();
        }
        let action = view
            .memory_tree
            .as_mut()
            .map(|tree| tree.handle_key(&id, view.editor.keybindings()));
        match action {
            Some(MemoryTreeAction::None) | None => {}
            Some(MemoryTreeAction::Close) => {
                view.memory_tree = None;
                // Levels still in flight belong to the closed tree.
                self.memory_tree_epoch += 1;
            }
            Some(MemoryTreeAction::Fetch(node)) => self.spawn_memory_tree_fetch(Some(node)),
        }
        self.dirty = true;
        Ok(())
    }

    /// One live `memory_update`: never a transcript row, only the gauge's
    /// new view size, with the working marker when a request is open.
    pub(super) fn apply_memory_update(&mut self, update: &MemoryUpdate, view: &mut AgentView) {
        let timing = if self.turn_active {
            UpdateTiming::InRequest
        } else {
            UpdateTiming::Idle
        };
        self.set_memory_gauge(MemoryGauge::after(update, timing), view);
    }

    /// The gauge's reading for this session, mirrored into the chrome.
    pub(super) fn set_memory_gauge(&mut self, gauge: MemoryGauge, view: &mut AgentView) {
        self.memory = Some(gauge);
        view.chrome.memory = Some(gauge);
        self.dirty = true;
    }

    /// A request began or ended: the gauge's working marker clears.
    pub(super) fn settle_memory_gauge(&mut self, view: &mut AgentView) {
        if let Some(mut gauge) = self.memory {
            gauge.settle();
            self.set_memory_gauge(gauge, view);
        }
    }
}
