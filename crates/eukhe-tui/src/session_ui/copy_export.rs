//! The `/copy` and `/export` runs: the clipboard copy of the last
//! assistant text and the daemon-side session export.
use super::{
    AgentView, DaemonCommand, Duration, Map, Result, SessionUi, Value, UI_REQUEST_TIMEOUT_MS,
};

impl SessionUi {
    // ------------------------------------------------------------------
    // Clipboard (/copy)
    // ------------------------------------------------------------------

    /// `/copy` (TS `handleCopyCommand`): fetch the last assistant text
    /// from the daemon and copy it to the clipboard. No assistant text
    /// yet is the TS error row; a clipboard failure surfaces the copy
    /// chain's own message.
    pub(crate) async fn handle_copy_command(&mut self, view: &mut AgentView) -> Result<()> {
        let data = self
            .bounded_request(
                Duration::from_millis(UI_REQUEST_TIMEOUT_MS),
                DaemonCommand::GetLastAssistantText {
                    id: None,
                    active_session_id: self.active_session_id.clone(),
                    rest: Map::default(),
                },
            )
            .await?;
        let text = data
            .get("text")
            .and_then(Value::as_str)
            .map(str::trim)
            .filter(|text| !text.is_empty())
            .map(str::to_string);
        let Some(text) = text else {
            self.error_row("No agent messages to copy yet.", view);
            return Ok(());
        };
        match crate::clipboard::copy_to_clipboard(&text, &mut self.osc_sink) {
            Ok(crate::clipboard::CopyOutcome::Confirmed) => {
                self.toast("Copied last agent message to clipboard", view);
            }
            Ok(crate::clipboard::CopyOutcome::Requested) => {
                self.toast(crate::clipboard::CLIPBOARD_REQUESTED, view);
            }
            Err(message) => self.error_row(&message, view),
        }
        Ok(())
    }

    // ------------------------------------------------------------------
    // Session export (/export)
    // ------------------------------------------------------------------

    /// `/export [path]` (TS `handleExportCommand`): export the session to
    /// HTML -- or, for an explicit `.jsonl` path, the current branch as a
    /// JSONL file -- and report the written path. The daemon owns the
    /// export; failures surface as the TS error row.
    pub(crate) async fn handle_export_command(
        &mut self,
        resolved: &eukhe_types::slash_commands::ResolvedSlashCommand,
        view: &mut AgentView,
    ) -> Result<()> {
        let command_text = if resolved.args.is_empty() {
            "/export".to_string()
        } else {
            format!("/export {}", resolved.args)
        };
        let output_path = crate::path_argument::path_command_argument(&command_text, "/export");
        let request = if output_path.as_deref().is_some_and(|path| {
            std::path::Path::new(path)
                .extension()
                .is_some_and(|ext| ext.eq_ignore_ascii_case("jsonl"))
        }) {
            DaemonCommand::ExportJsonl {
                id: None,
                active_session_id: self.active_session_id.clone(),
                output_path,
                rest: Map::default(),
            }
        } else {
            DaemonCommand::ExportHtml {
                id: None,
                active_session_id: self.active_session_id.clone(),
                output_path,
                // The files this client's theme resolves against, so the
                // export paints the theme the terminal shows.
                theme_paths: self.client_settings.as_ref().map(|settings| {
                    settings
                        .theme_sources()
                        .registered
                        .iter()
                        .map(|path| path.to_string_lossy().into_owned())
                        .collect()
                }),
                rest: Map::default(),
            }
        };
        match self
            .bounded_request(Duration::from_millis(UI_REQUEST_TIMEOUT_MS), request)
            .await
        {
            Ok(data) => {
                let path = data.get("path").and_then(Value::as_str).unwrap_or_default();
                self.note(&format!("Session exported to: {path}"), view);
            }
            Err(error) => {
                self.error_row(&format!("Failed to export session: {error:#}"), view);
            }
        }
        Ok(())
    }
}
