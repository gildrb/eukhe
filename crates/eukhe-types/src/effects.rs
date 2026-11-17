//! Exactly-once effects on the wire: a step whose outcome a restart could
//! not tell and that was not safe to repeat, which Eukhe treats as not run
//! ([`UnknownEffect`], why: [`UnknownCause`]), how a person may correct
//! that afterwards ([`EffectResolution`]), the run's end-of-run lines of
//! such steps ([`UnknownEffect::report_line`], [`treated_not_run`]), and
//! the replies of the daemon commands `get_unknown_effects`
//! ([`UnknownEffectsReply`]) and `resolve_unknown_effect`
//! ([`ResolvedEffectReply`]). The session keeps them in its durable
//! `eukhe.effects` ledger (`eukhe_durable::harness::effects`); the
//! `unknown_effects_update` session event carries the whole ledger after
//! each change.

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

/// A person's optional correction of a step Eukhe treated as not run,
/// after looking at the world. Nothing waits for one.
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

/// Why a restart treated a step of unknown outcome as not run: the world
/// showed nothing of it and running it again was not safe.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub enum UnknownCause {
    /// A repeat may change the world again (a command, a request to a
    /// host, a partial edit).
    NotRepeatSafe,
    /// Its target declares no deduplication of a repeat of its key.
    NoDedup,
    /// It was already sent again as often as its target's declaration
    /// allows.
    ResendsSpent,
    /// Its tool is no longer offered.
    ToolGone,
    /// Its run was stopped: nothing of it starts any more.
    RunStopped,
}

impl UnknownCause {
    /// The reason for people, as the end-of-run report shows it.
    #[must_use]
    pub const fn text(self) -> &'static str {
        match self {
            Self::NotRepeatSafe => "cut by a crash; not safe to repeat",
            Self::NoDedup => "cut by a crash; its target declares no deduplication",
            Self::ResendsSpent => "cut by a crash; already sent again as often as allowed",
            Self::ToolGone => "cut by a crash; its tool is no longer offered",
            Self::RunStopped => "cut by a crash; its run was stopped",
        }
    }
}

/// A step whose outcome a restart could not tell and that was not safe to
/// repeat: Eukhe treated it as not run, never ran it again, and its run
/// went on.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct UnknownEffect {
    /// The effect's id in its conversation: a tool call's id, a request's
    /// `request:<task>:<attempt>`, a job's `job:<id>`.
    pub id: String,
    pub kind: EffectKind,
    /// What it is, for people: the tool and its call (`bash: git push`),
    /// the job's label.
    pub what: String,
    /// When the restart settled it, in ms since the epoch.
    pub at: f64,
    /// Why it was treated as not run; none in a ledger written before the
    /// cause was kept.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub cause: Option<UnknownCause>,
    /// The run of the root session whose end-of-run report lists it.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub settled_run: Option<u64>,
    /// A person's correction; none while it stands as treated not run.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub resolution: Option<EffectResolution>,
}

impl UnknownEffect {
    /// Nobody corrected it: it stands as treated not run.
    #[must_use]
    pub fn is_open(&self) -> bool {
        self.resolution.is_none()
    }

    /// One line for people: `<id> <kind> <treated-not-run|ran|not-run>
    /// <what>`.
    #[must_use]
    pub fn line(&self) -> String {
        let state = self
            .resolution
            .map_or("treated-not-run", EffectResolution::word);
        format!("{} {} {state} {}", self.id, self.kind.name(), self.what)
    }

    /// Its line in the end-of-run report's `Unknown after a crash,
    /// treated as not run:` section: `- <what> (<why>)`, a tool call by
    /// its tool and call, any other step by its kind first.
    #[must_use]
    pub fn report_line(&self) -> String {
        let why = self.cause.map_or("cut by a crash", UnknownCause::text);
        let kind = match self.kind {
            EffectKind::Tool | EffectKind::Write => "",
            EffectKind::Request => "model request: ",
            EffectKind::Job => "background job: ",
            EffectKind::Spawn => "subagent: ",
            EffectKind::Fire => "scheduled fire: ",
            EffectKind::Message => "message: ",
        };
        format!("- {kind}{} ({why})", self.what)
    }
}

/// The steps the run `run` treated as not run, oldest first: the ledger's
/// entries it settled, model requests apart (their usage report settles
/// them, O11).
pub fn treated_not_run(
    effects: &[UnknownEffect],
    run: u64,
) -> impl Iterator<Item = &UnknownEffect> {
    effects
        .iter()
        .filter(move |effect| effect.settled_run == Some(run) && effect.kind != EffectKind::Request)
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
    /// it stands, `notRun` once corrected so; a ledger written before the
    /// cause and the run were kept reads with none.
    #[test]
    fn an_unknown_effect_round_trips_its_wire_form() {
        let open = serde_json::json!({
            "id": "tool:call-1",
            "kind": "tool",
            "what": "bash: make deploy",
            "at": 1_700_000_000_000.0,
            "cause": "notRepeatSafe",
            "settledRun": 3,
        });
        let effect: UnknownEffect = serde_json::from_value(open.clone()).expect("open effect");
        assert_eq!(
            effect,
            UnknownEffect {
                id: "tool:call-1".to_owned(),
                kind: EffectKind::Tool,
                what: "bash: make deploy".to_owned(),
                at: 1_700_000_000_000.0,
                cause: Some(UnknownCause::NotRepeatSafe),
                settled_run: Some(3),
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
        let older = serde_json::json!({
            "id": "job:7",
            "kind": "job",
            "what": "cargo build",
            "at": 0.0,
        });
        assert_eq!(
            serde_json::from_value::<UnknownEffect>(older).expect("older effect"),
            UnknownEffect {
                id: "job:7".to_owned(),
                kind: EffectKind::Job,
                what: "cargo build".to_owned(),
                at: 0.0,
                cause: None,
                settled_run: None,
                resolution: None,
            }
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

    fn job(cause: Option<UnknownCause>, settled_run: Option<u64>) -> UnknownEffect {
        UnknownEffect {
            id: "job:7".to_owned(),
            kind: EffectKind::Job,
            what: "cargo build".to_owned(),
            at: 0.0,
            cause,
            settled_run,
            resolution: None,
        }
    }

    #[test]
    fn the_line_names_the_effect_and_its_state() {
        let effect = job(None, None);
        assert_eq!(effect.line(), "job:7 job treated-not-run cargo build");
        let ran = UnknownEffect {
            resolution: Some(EffectResolution::Ran),
            ..effect
        };
        assert_eq!(ran.line(), "job:7 job ran cargo build");
    }

    /// The report line: a tool call by its call, any other step by its
    /// kind, then why; a ledger entry with no cause says only the crash.
    #[test]
    fn the_report_line_says_what_and_why() {
        let call = UnknownEffect {
            id: "tool:c1".to_owned(),
            kind: EffectKind::Tool,
            what: "bash: git push origin main".to_owned(),
            ..job(Some(UnknownCause::NotRepeatSafe), Some(1))
        };
        assert_eq!(
            [
                call.report_line(),
                job(Some(UnknownCause::RunStopped), Some(1)).report_line(),
                job(None, None).report_line(),
            ],
            [
                "- bash: git push origin main (cut by a crash; not safe to repeat)",
                "- background job: cargo build (cut by a crash; its run was stopped)",
                "- background job: cargo build (cut by a crash)",
            ]
        );
    }

    /// A run's report holds the steps it settled, oldest first, and no
    /// model request.
    #[test]
    fn a_run_reports_only_the_steps_it_settled() {
        let request = UnknownEffect {
            id: "request:4:0".to_owned(),
            kind: EffectKind::Request,
            ..job(Some(UnknownCause::NoDedup), Some(2))
        };
        let earlier = UnknownEffect {
            id: "job:1".to_owned(),
            ..job(Some(UnknownCause::NotRepeatSafe), Some(1))
        };
        let first = UnknownEffect {
            id: "job:2".to_owned(),
            ..job(Some(UnknownCause::NotRepeatSafe), Some(2))
        };
        let second = UnknownEffect {
            id: "tool:c3".to_owned(),
            kind: EffectKind::Write,
            ..job(Some(UnknownCause::NotRepeatSafe), Some(2))
        };
        let ledger = [earlier, first.clone(), request, second.clone()];
        assert_eq!(
            treated_not_run(&ledger, 2).cloned().collect::<Vec<_>>(),
            [first, second]
        );
    }
}
