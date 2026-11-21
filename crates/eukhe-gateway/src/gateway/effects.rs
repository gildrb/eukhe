//! Irreversible effects and per-prompt snapshots from the phone: the
//! end-of-run message (`run_report`, to the peer holding the floor, after
//! the run's answer), `/effects`, `/undo` and `/diff [all]`. The texts are
//! `eukhe_types`' (`run_report_text`, `ledger_text`, `undo_text`,
//! `diff_text`), the ones every surface shows.

use anyhow::Context;
use eukhe_client::saved_sessions::DaemonLauncher;
use eukhe_types::daemon::DaemonCommand;
use eukhe_types::effects::{
    ledger_text, run_report_text, RanEffect, RanEffectsReply, RunReport, UnknownEffect,
    UnknownEffectsReply,
};
use eukhe_types::undo::{diff_text, undo_text, DiffScope, TurnDiffReply, UndoReply};
use serde_json::Map;

use super::{Done, Gateway};
use crate::signal::Peer;
use crate::style;

impl<L: DaemonLauncher> Gateway<L> {
    /// A root run ended: the peer holding the floor hears the end-of-run
    /// message (none when nothing ran and nothing was left unknown).
    pub(super) async fn send_run_report(&self, ran: &[RanEffect], unknown: &[UnknownEffect]) {
        let Some(peer) = self.floor.clone() else {
            return;
        };
        let report = RunReport {
            ran: ran.to_vec(),
            unknown: unknown.to_vec(),
        };
        if let Some(text) = run_report_text(&report) {
            self.reply(&peer, text).await;
        }
    }

    /// `/effects`: the session's ledger of irreversible effects that ran,
    /// then each step a crash left unknown.
    pub(super) async fn effects(&mut self) -> anyhow::Result<String> {
        let binding = self.routed_binding().await?;
        let ran: RanEffectsReply = serde_json::from_value(
            self.link
                .client
                .request_ok(DaemonCommand::GetRanEffects {
                    id: None,
                    active_session_id: binding.active_session_id.clone(),
                    rest: Map::default(),
                })
                .await
                .context("read the effects ledger")?,
        )
        .context("read the get_ran_effects reply")?;
        let unknown: UnknownEffectsReply = serde_json::from_value(
            self.link
                .client
                .request_ok(DaemonCommand::GetUnknownEffects {
                    id: None,
                    active_session_id: binding.active_session_id,
                    rest: Map::default(),
                })
                .await
                .context("read the unknown effects")?,
        )
        .context("read the get_unknown_effects reply")?;
        Ok(std::iter::once(ledger_text(&ran.effects))
            .chain(unknown.effects.iter().map(UnknownEffect::line))
            .collect::<Vec<_>>()
            .join("\n"))
    }

    /// `/undo`: what it restored, and the irreversible effects of the
    /// undone prompt's run it could not take back.
    pub(super) async fn undo(&mut self) -> anyhow::Result<String> {
        let binding = self.routed_binding().await?;
        let reply: UndoReply = serde_json::from_value(
            self.link
                .client
                .request_ok(DaemonCommand::UndoTurn {
                    id: None,
                    active_session_id: binding.active_session_id,
                    rest: Map::default(),
                })
                .await
                .context("undo")?,
        )
        .context("read the undo_turn reply")?;
        Ok(undo_text(&reply).trim_end().to_owned())
    }

    /// `/diff [all]`: the diff as a code block, in as many messages as it
    /// takes (sent here: nothing more to reply).
    pub(super) async fn diff(&mut self, peer: &Peer, scope: DiffScope) -> anyhow::Result<Done> {
        let binding = self.routed_binding().await?;
        let reply: TurnDiffReply = serde_json::from_value(
            self.link
                .client
                .request_ok(DaemonCommand::GetTurnDiff {
                    id: None,
                    active_session_id: binding.active_session_id,
                    scope,
                    rest: Map::default(),
                })
                .await
                .context("read the diff")?,
        )
        .context("read the get_turn_diff reply")?;
        let block = format!("```\n{}\n```", diff_text(&reply).trim_end());
        for chunk in style::render(&block) {
            self.signal.send(peer, &chunk).await?;
        }
        Ok(Done::Quiet)
    }
}
