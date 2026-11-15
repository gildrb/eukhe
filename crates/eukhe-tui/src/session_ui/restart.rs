//! `/restart` and the staged-update notice. The composition root's
//! [`Restarter`](eukhe_client::restart::Restarter) applies a staged update
//! and names the build to start; the plan
//! ([`eukhe_client::restart::plan`]) decides what the daemon does. A plan
//! that starts the build ends this run with the target; the composition
//! root starts it on this session once the terminal is restored. A busy
//! daemon is never stopped.

use eukhe_client::restart::plan;

use super::{AgentView, SessionUi};

impl SessionUi {
    /// `/restart`.
    pub(super) async fn restart(&mut self, view: &mut AgentView) {
        let Some(restarter) = self.restarter.clone() else {
            self.error_row("/restart is not available in this client", view);
            return;
        };
        // `return_to_agents_view` is false only for `--no-session` runs.
        if !self.return_to_agents_view {
            self.error_row(
                "/restart reopens this session from its file, and a --no-session session has none",
                view,
            );
            return;
        }
        // Applying the update and reading the target's identity run
        // processes: off the UI loop.
        let prepared = {
            let restarter = std::sync::Arc::clone(&restarter);
            tokio::task::spawn_blocking(move || restarter.prepare()).await
        };
        let target = match prepared {
            Ok(Ok(target)) => target,
            Ok(Err(why)) => {
                self.error_row(&format!("Cannot restart: {why}"), view);
                return;
            }
            Err(error) => {
                self.error_row(&format!("Cannot restart: {error}"), view);
                return;
            }
        };
        let decided = plan(&self.client, &target, restarter.release_wait()).await;
        match decided.stay_message(&target) {
            None => {
                self.note(&format!("Restarting on eukhe {}", target.version), view);
                self.restart_target = Some(target);
                self.exit_requested = true;
            }
            Some(message) => self.note(&message, view),
        }
    }

    /// The staged-update notice, once per process.
    pub(crate) fn show_update_notice(&mut self, view: &mut AgentView) {
        if let Some(notice) = self
            .restarter
            .as_ref()
            .and_then(|restarter| restarter.take_notice())
        {
            self.note(&notice, view);
        }
    }
}
