//! The exactly-once effects surface of the session view: the session's
//! ledger of effects whose outcome a restart could not tell (seeded from
//! the attach snapshot's `unknownEffects`, then `unknown_effects_update`),
//! a warning row for each effect that opens and one summary row on every
//! rebuilt transcript while some stay open, and `/effects` (list) with
//! `/effects ran|not-run <id>` (settle one after looking at the world).

use eukhe_types::effects::{
    EffectResolution, ResolvedEffectReply, UnknownEffect, UnknownEffectsReply,
};

use super::{
    AgentView, ChatEntry, DaemonCommand, Duration, Map, SessionUi, StatusKind,
    UI_REQUEST_TIMEOUT_MS,
};
use crate::glyphs::WARN;

/// The warning row of one effect that opened: what it is, its id, and how
/// to settle it.
fn opened_row(effect: &UnknownEffect) -> String {
    format!(
        "{WARN} Interrupted, outcome unknown: {} ({}). Check whether it ran, then /effects ran {} or /effects not-run {}",
        effect.what, effect.id, effect.id, effect.id
    )
}

/// The rebuilt transcript's summary row while `open` effects stay open.
fn open_summary_row(open: usize) -> String {
    let effects = if open == 1 {
        "effect has"
    } else {
        "effects have"
    };
    format!("{WARN} {open} interrupted {effects} an unknown outcome: /effects lists them")
}

/// The effects of the ledger `next` that are open and were not open in
/// the ledger `known`, oldest first.
fn newly_open<'a>(
    known: &'a [UnknownEffect],
    next: &'a [UnknownEffect],
) -> impl Iterator<Item = &'a UnknownEffect> {
    next.iter().filter(|effect| {
        effect.is_open() && !known.iter().any(|was| was.id == effect.id && was.is_open())
    })
}

impl SessionUi {
    /// One `unknown_effects_update`: a warning row for each effect that
    /// opened since the last ledger, then the ledger replaces it.
    pub(super) fn apply_unknown_effects(
        &mut self,
        effects: Vec<UnknownEffect>,
        view: &mut AgentView,
    ) {
        for effect in newly_open(&self.unknown_effects, &effects) {
            view.push_entry(ChatEntry::Status {
                text: opened_row(effect),
                kind: StatusKind::Warning,
            });
            self.last_status_index = None;
            self.dirty = true;
        }
        self.unknown_effects = effects;
    }

    /// The rebuilt transcript's notice: one summary row while the ledger
    /// holds open effects, none otherwise.
    pub(super) fn push_open_effects_notice(&mut self, view: &mut AgentView) {
        let open = self
            .unknown_effects
            .iter()
            .filter(|effect| effect.is_open())
            .count();
        if open > 0 {
            view.push_entry(ChatEntry::Status {
                text: open_summary_row(open),
                kind: StatusKind::Warning,
            });
        }
    }

    /// `/effects` lists the ledger; `/effects ran <id>` and `/effects
    /// not-run <id>` settle one open effect. `sub` is the subcommand path,
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
                        "No interrupted effects with an unknown outcome.".to_owned()
                    } else {
                        effects
                            .iter()
                            .map(UnknownEffect::line)
                            .collect::<Vec<_>>()
                            .join("\n")
                    };
                    self.unknown_effects = effects;
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
                self.note(&format!("Resolved {}", effect.line()), view);
            }
            Err(error) => self.error_row(&format!("{error:#}"), view),
        }
    }
}

#[cfg(test)]
mod tests {
    use eukhe_types::effects::EffectKind;

    use super::*;

    fn effect(id: &str, resolution: Option<EffectResolution>) -> UnknownEffect {
        UnknownEffect {
            id: id.to_owned(),
            kind: EffectKind::Tool,
            what: format!("bash: {id}"),
            at: 0.0,
            resolution,
        }
    }

    /// Only an effect that opened since the last ledger warns: one open
    /// before, or settled now, stays silent.
    #[test]
    fn only_newly_open_effects_warn() {
        let known = [effect("a", None), effect("b", Some(EffectResolution::Ran))];
        let next = [
            effect("a", None),
            effect("b", Some(EffectResolution::Ran)),
            effect("c", None),
            effect("d", Some(EffectResolution::NotRun)),
        ];
        let opened: Vec<&str> = newly_open(&known, &next)
            .map(|effect| effect.id.as_str())
            .collect();
        assert_eq!(opened, ["c"]);
        let from_nothing: Vec<&str> = newly_open(&[], &next)
            .map(|effect| effect.id.as_str())
            .collect();
        assert_eq!(from_nothing, ["a", "c"]);
    }

    #[test]
    fn the_rows_name_the_effect_and_the_count() {
        assert_eq!(
            opened_row(&effect("tool:c1", None)),
            "! Interrupted, outcome unknown: bash: tool:c1 (tool:c1). Check whether it ran, then /effects ran tool:c1 or /effects not-run tool:c1"
        );
        assert_eq!(
            open_summary_row(1),
            "! 1 interrupted effect has an unknown outcome: /effects lists them"
        );
        assert_eq!(
            open_summary_row(2),
            "! 2 interrupted effects have an unknown outcome: /effects lists them"
        );
    }
}
