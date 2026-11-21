//! The exactly-once effects surface of the session view: the session's
//! ledger of steps a restart could not tell the outcome of and treated as
//! not run (seeded from the attach snapshot's `unknownEffects`, then
//! `unknown_effects_update`), and `/effects` (list) with `/effects
//! ran|not-run <id>` (an optional correction after looking at the world).
//! The run's end-of-run report lists the steps; the view asks nothing.
//! A model request's row is the one notice: it says what stays counted.

use eukhe_types::effects::{
    EffectKind, EffectResolution, ResolvedEffectReply, UnknownEffect, UnknownEffectsReply,
};
use eukhe_types::slash_arguments::LiveValues;

use super::{
    AgentView, ChatEntry, DaemonCommand, Duration, Map, SessionUi, StatusKind,
    UI_REQUEST_TIMEOUT_MS,
};
use crate::glyphs::WARN;

/// The warning row of a model request a restart cut and did not send
/// again: what was cut and what stays counted (its `what`, a sentence of
/// its own; its provider's usage report settles it).
fn request_row(effect: &UnknownEffect) -> String {
    format!("{WARN} {}", effect.what)
}

/// The uncorrected model requests of the ledger `next` that were not in
/// the ledger `known`, oldest first.
fn newly_cut_requests<'a>(
    known: &'a [UnknownEffect],
    next: &'a [UnknownEffect],
) -> impl Iterator<Item = &'a UnknownEffect> {
    next.iter().filter(|effect| {
        effect.kind == EffectKind::Request
            && effect.is_open()
            && !known.iter().any(|was| was.id == effect.id)
    })
}

impl SessionUi {
    /// One `unknown_effects_update`: a warning row for each model request
    /// cut since the last ledger, then the ledger replaces it.
    pub(super) fn apply_unknown_effects(
        &mut self,
        effects: Vec<UnknownEffect>,
        view: &mut AgentView,
    ) {
        for effect in newly_cut_requests(&self.unknown_effects, &effects) {
            view.push_entry(ChatEntry::Status {
                text: request_row(effect),
                kind: StatusKind::Warning,
            });
            self.last_status_index = None;
            self.dirty = true;
        }
        self.unknown_effects = effects;
        self.sync_effect_completions(view);
    }

    /// The uncorrected entries' ids become the values `/effects ran` and
    /// `/effects not-run` complete.
    pub(super) fn sync_effect_completions(&self, view: &mut AgentView) {
        let rows = self
            .unknown_effects
            .iter()
            .filter(|effect| effect.is_open())
            .map(|effect| crate::autocomplete::CompletionItem {
                value: effect.id.clone(),
                label: effect.id.clone(),
                description: Some(effect.what.clone()),
                argument_hint: None,
                source_tag: None,
                path_row: None,
            })
            .collect();
        view.editor
            .set_autocomplete_live_values(LiveValues::OpenEffects, rows);
    }

    /// `/effects` lists the ledger; `/effects ran <id>` and `/effects
    /// not-run <id>` correct one entry. `sub` is the subcommand path,
    /// `args` the text after it.
    pub(super) async fn handle_effects_command(
        &mut self,
        sub: &[String],
        args: &str,
        view: &mut AgentView,
    ) {
        let timeout = Duration::from_millis(UI_REQUEST_TIMEOUT_MS);
        let Some(word) = sub.first() else {
            let listed = self
                .bounded_request(
                    timeout,
                    DaemonCommand::GetUnknownEffects {
                        id: None,
                        active_session_id: self.active_session_id.clone(),
                        rest: Map::default(),
                    },
                )
                .await
                .and_then(|data| {
                    serde_json::from_value::<UnknownEffectsReply>(data).map_err(anyhow::Error::from)
                });
            match listed {
                Ok(UnknownEffectsReply { effects }) => {
                    let text = if effects.is_empty() {
                        "No step was treated as not run after a crash.".to_owned()
                    } else {
                        effects
                            .iter()
                            .map(UnknownEffect::line)
                            .collect::<Vec<_>>()
                            .join("\n")
                    };
                    self.unknown_effects = effects;
                    self.sync_effect_completions(view);
                    self.plain_row(&text, view);
                }
                Err(error) => self.error_row(&format!("{error:#}"), view),
            }
            return;
        };
        let Some(resolution) = EffectResolution::from_word(word) else {
            self.note_as(
                "Usage: /effects [ran|not-run <id>]",
                StatusKind::Warning,
                view,
            );
            return;
        };
        let effect_id = args.trim();
        if effect_id.is_empty() {
            self.note_as(
                &format!("Usage: /effects {} <id>", resolution.word()),
                StatusKind::Warning,
                view,
            );
            return;
        }
        let resolved = self
            .bounded_request(
                timeout,
                DaemonCommand::ResolveUnknownEffect {
                    id: None,
                    active_session_id: self.active_session_id.clone(),
                    effect_id: effect_id.to_owned(),
                    resolution,
                    rest: Map::default(),
                },
            )
            .await
            .and_then(|data| {
                serde_json::from_value::<ResolvedEffectReply>(data).map_err(anyhow::Error::from)
            });
        match resolved {
            Ok(ResolvedEffectReply { effect }) => {
                self.note(&format!("Corrected {}", effect.line()), view);
            }
            Err(error) => self.error_row(&format!("{error:#}"), view),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn effect(id: &str, kind: EffectKind, resolution: Option<EffectResolution>) -> UnknownEffect {
        UnknownEffect {
            id: id.to_owned(),
            kind,
            what: format!("bash: {id}"),
            at: 0.0,
            cause: None,
            settled_run: None,
            resolution,
        }
    }

    /// Only a model request cut since the last ledger warns: a step
    /// treated as not run waits for the end-of-run report, and a request
    /// known before or corrected stays silent.
    #[test]
    fn only_newly_cut_requests_warn() {
        let known = [effect("r1", EffectKind::Request, None)];
        let next = [
            effect("r1", EffectKind::Request, None),
            effect("tool:c1", EffectKind::Tool, None),
            effect("r2", EffectKind::Request, None),
            effect("r3", EffectKind::Request, Some(EffectResolution::NotRun)),
        ];
        let cut: Vec<&str> = newly_cut_requests(&known, &next)
            .map(|effect| effect.id.as_str())
            .collect();
        assert_eq!(cut, ["r2"]);
    }

    #[test]
    fn a_request_row_says_what_stays_counted() {
        let request = UnknownEffect {
            what: "Model request to p/m cut by a crash, not resent (no deduplication declared). \
                   Up to $0.42 stays counted until its usage is known."
                .to_owned(),
            ..effect("request:1:1", EffectKind::Request, None)
        };
        assert_eq!(
            request_row(&request),
            "! Model request to p/m cut by a crash, not resent (no deduplication declared). \
             Up to $0.42 stays counted until its usage is known."
        );
    }
}
