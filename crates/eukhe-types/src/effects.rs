//! Exactly-once effects on the wire: an effect whose outcome a restart
//! could not tell ([`UnknownEffect`]), how a client settles one
//! ([`EffectResolution`]), and the replies of the daemon commands
//! `get_unknown_effects` ([`UnknownEffectsReply`]) and
//! `resolve_unknown_effect` ([`ResolvedEffectReply`]). The session keeps
//! them in its durable `eukhe.effects` ledger
//! (`eukhe_durable::harness::effects`); the `unknown_effects_update`
//! session event carries the whole ledger after each change.

use serde::{Deserialize, Serialize};

/// What kind of effect it is.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub enum EffectKind {
    /// A tool call.
    Tool,
    /// A provider request.
    Request,
    /// A background job.
    Job,
    /// A file write.
    Write,
    /// A subagent spawn.
    Spawn,
    /// A cron fire or a heartbeat.
    Fire,
    /// The delivery of a queued or steering message.
    Message,
}

impl EffectKind {
    /// The wire name.
    #[must_use]
    pub const fn name(self) -> &'static str {
        match self {
            Self::Tool => "tool",
            Self::Request => "request",
            Self::Job => "job",
            Self::Write => "write",
            Self::Spawn => "spawn",
            Self::Fire => "fire",
            Self::Message => "message",
        }
    }
}

/// How a client settled an unknown effect after looking at the world.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub enum EffectResolution {
    /// It ran.
    Ran,
    /// It did not run.
    NotRun,
}

impl EffectResolution {
    /// The word a person types for it (`eukhe effects resolve <id>
    /// ran|not-run`, `/effects ran|not-run <id>`).
    #[must_use]
    pub const fn word(self) -> &'static str {
        match self {
            Self::Ran => "ran",
            Self::NotRun => "not-run",
        }
    }

    /// The resolution `word` names ([`Self::word`]), in any case.
    #[must_use]
    pub fn from_word(word: &str) -> Option<Self> {
        [Self::Ran, Self::NotRun]
            .into_iter()
            .find(|resolution| resolution.word().eq_ignore_ascii_case(word))
    }
}

/// An effect whose outcome a restart could not tell.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct UnknownEffect {
    /// The effect's id in its conversation: a tool call's id, a request's
    /// `request:<task>:<attempt>`, a job's `job:<id>`.
    pub id: String,
    pub kind: EffectKind,
    /// What it is, for people: the tool and its call, the job's label.
    pub what: String,
    /// When the restart settled it, in ms since the epoch.
    pub at: f64,
    /// How a client resolved it; none while nobody knows.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub resolution: Option<EffectResolution>,
}

impl UnknownEffect {
    /// Nobody settled it yet.
    #[must_use]
    pub fn is_open(&self) -> bool {
        self.resolution.is_none()
    }

    /// One line for people: `<id> <kind> <unknown|ran|not-run> <what>`.
    #[must_use]
    pub fn line(&self) -> String {
        let state = self.resolution.map_or("unknown", EffectResolution::word);
        format!("{} {} {state} {}", self.id, self.kind.name(), self.what)
    }
}

/// The `get_unknown_effects` response data: the session's ledger, oldest
/// first, open and resolved.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct UnknownEffectsReply {
    pub effects: Vec<UnknownEffect>,
}

/// The `resolve_unknown_effect` response data: the effect as resolved.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct ResolvedEffectReply {
    pub effect: UnknownEffect,
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The wire form: camelCase fields and kinds, no `resolution` while
    /// open, `notRun` once settled so.
    #[test]
    fn an_unknown_effect_round_trips_its_wire_form() {
        let open = serde_json::json!({
            "id": "tool:call-1",
            "kind": "tool",
            "what": "bash: make deploy",
            "at": 1_700_000_000_000.0,
        });
        let effect: UnknownEffect = serde_json::from_value(open.clone()).expect("open effect");
        assert_eq!(
            effect,
            UnknownEffect {
                id: "tool:call-1".to_owned(),
                kind: EffectKind::Tool,
                what: "bash: make deploy".to_owned(),
                at: 1_700_000_000_000.0,
                resolution: None,
            }
        );
        assert_eq!(serde_json::to_value(&effect).expect("encodes"), open);
        let settled = UnknownEffect {
            resolution: Some(EffectResolution::NotRun),
            ..effect
        };
        assert_eq!(
            serde_json::to_value(&settled).expect("encodes")["resolution"],
            "notRun"
        );
    }

    /// The typed words read back as their resolution in any case; any
    /// other word is none.
    #[test]
    fn resolution_words_read_back() {
        for resolution in [EffectResolution::Ran, EffectResolution::NotRun] {
            assert_eq!(
                EffectResolution::from_word(resolution.word()),
                Some(resolution)
            );
        }
        assert_eq!(
            EffectResolution::from_word("NOT-RUN"),
            Some(EffectResolution::NotRun)
        );
        assert_eq!(EffectResolution::from_word("notRun"), None);
    }

    #[test]
    fn the_line_names_the_effect_and_its_state() {
        let effect = UnknownEffect {
            id: "job:7".to_owned(),
            kind: EffectKind::Job,
            what: "cargo build".to_owned(),
            at: 0.0,
            resolution: None,
        };
        assert_eq!(effect.line(), "job:7 job unknown cargo build");
        let ran = UnknownEffect {
            resolution: Some(EffectResolution::Ran),
            ..effect
        };
        assert_eq!(ran.line(), "job:7 job ran cargo build");
    }
}
