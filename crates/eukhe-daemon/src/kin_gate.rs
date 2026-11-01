//! The kin check of an agent's message: an agent reaches only its parent
//! and its own children. The supervisor asks it before every agent-origin
//! `send_message` delivery (the woken targets included, before the wake)
//! and before it mints a worker-to-worker peer ticket, so both delivery
//! paths are gated. The decision is the compiled Bend core's
//! (`eukhe_bend::rules::kin`, laws `laws/kin.bend`), over the live
//! spawn-ledger edges.

use std::path::Path;
use std::sync::Arc;

use eukhe_bend::rules::kin::{admit, Admission, Edge, Message};

use crate::registry::ResidentWorker;
use crate::rlm_roster::session_family_key;
use crate::supervisor::Supervisor;

/// What one sending agent's messages are checked against: its key and the
/// live parent edges of the spawn ledger.
pub(crate) struct KinView {
    sender: String,
    /// `(child, parent)` keys of the live spawn-ledger edges.
    edges: Vec<(String, String)>,
}

/// The key of a session in the kin check: the family key of its storage,
/// else (a memory session, which has no ledger edges) its worker id.
fn session_key(session_file: Option<&Path>, worker_id: &str) -> String {
    match session_file {
        Some(file) => session_family_key(file).to_string_lossy().into_owned(),
        None => format!("worker:{worker_id}"),
    }
}

impl KinView {
    /// Admit a message to the session stored at `target_file` (`None`: a
    /// memory session, keyed by `target_worker`); the error is the
    /// refusal the sender sees, naming `target_label`.
    ///
    /// # Errors
    ///
    /// The target is neither the sender's parent nor one of its children.
    pub(crate) fn admit(
        &self,
        target_file: Option<&Path>,
        target_worker: &str,
        target_label: &str,
    ) -> Result<(), String> {
        let target = session_key(target_file, target_worker);
        let edges: Vec<Edge<'_>> = self
            .edges
            .iter()
            .map(|(child, parent)| Edge { child, parent })
            .collect();
        match admit(&Message {
            sender: &self.sender,
            target: &target,
            edges: &edges,
        }) {
            Admission::Admit(_) => Ok(()),
            Admission::Refuse(reason) => Err(format!("Cannot message {target_label}: {reason}")),
        }
    }
}

impl Supervisor {
    /// The kin view of the agent `source` sends as.
    ///
    /// # Errors
    ///
    /// The spawn ledger cannot be read.
    pub(crate) async fn kin_view(
        self: &Arc<Self>,
        source: &ResidentWorker,
    ) -> anyhow::Result<KinView> {
        let session_file = source.descriptor.lock().await.session_file.clone();
        // The spawn admission appends every edge to the daemon-default
        // ledger (`supervisor/adoption.rs`).
        let edges = self
            .rlm_spawn_ledger_for(None)
            .await?
            .live_edges()?
            .into_iter()
            .map(|edge| {
                (
                    session_family_key(Path::new(&edge.child))
                        .to_string_lossy()
                        .into_owned(),
                    session_family_key(Path::new(&edge.parent))
                        .to_string_lossy()
                        .into_owned(),
                )
            })
            .collect();
        Ok(KinView {
            sender: session_key(session_file.as_deref().map(Path::new), &source.worker_id),
            edges,
        })
    }

    /// Admit the agent `source`'s message to the resident `target`.
    ///
    /// # Errors
    ///
    /// The refusal the sender sees, or the ledger read's error.
    pub(crate) async fn admit_kin_resident(
        self: &Arc<Self>,
        source: &ResidentWorker,
        target: &ResidentWorker,
        target_label: &str,
    ) -> Result<(), String> {
        let view = self
            .kin_view(source)
            .await
            .map_err(|error| format!("{error:#}"))?;
        let target_file = target.descriptor.lock().await.session_file.clone();
        view.admit(
            target_file.as_deref().map(Path::new),
            &target.worker_id,
            target_label,
        )
    }
}

#[cfg(test)]
mod tests {
    use std::path::Path;

    use super::KinView;

    /// A view of the agent stored at `sender` over a root with two
    /// children, `a` and `b`, and `a`'s child `c`.
    fn view(sender: &str) -> KinView {
        let edge = |child: &str, parent: &str| (child.to_owned(), parent.to_owned());
        KinView {
            sender: sender.to_owned(),
            edges: vec![
                edge("/s/a", "/s/root"),
                edge("/s/b", "/s/root"),
                edge("/s/c", "/s/a"),
            ],
        }
    }

    /// The regression: a sibling (and a grandparent, and itself) is
    /// refused; the parent and an own child are admitted.
    #[test]
    fn only_the_parent_and_own_children_are_admitted() {
        let refusal = |target: &str| {
            Err(format!(
                "Cannot message {target}: agents message only their parent and their own children"
            ))
        };
        let admit =
            |sender: &str, target: &str| view(sender).admit(Some(Path::new(target)), "w", target);
        assert_eq!(
            [
                admit("/s/a", "/s/root"),
                admit("/s/a", "/s/c"),
                admit("/s/root", "/s/b"),
                admit("/s/a", "/s/b"),
                admit("/s/c", "/s/root"),
            ],
            [Ok(()), Ok(()), Ok(()), refusal("/s/b"), refusal("/s/root")]
        );
        assert_eq!(
            admit("/s/a", "/s/a"),
            Err("Cannot message /s/a: an agent cannot message itself".to_owned())
        );
    }
}
