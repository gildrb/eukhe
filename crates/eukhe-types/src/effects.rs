//! Effects on the wire: a step whose outcome a restart could not tell and
//! that was not safe to repeat, which Eukhe treats as not run
//! ([`UnknownEffect`], why: [`UnknownCause`]), how a person may correct
//! that afterwards ([`EffectResolution`]), the run's end-of-run lines of
//! such steps ([`UnknownEffect::report_line`], [`treated_not_run`]); an
//! irreversible effect that ran ([`RanEffect`], its classes
//! [`EffectClass`]), the end-of-run report ([`RunReport`],
//! [`run_report_text`]), an attached editor's permission question
//! ([`EditorPermissionRequest`], [`EditorVerdict`]); and the replies of
//! the daemon commands `get_unknown_effects` ([`UnknownEffectsReply`]),
//! `resolve_unknown_effect` ([`ResolvedEffectReply`]) and
//! `get_ran_effects` ([`RanEffectsReply`]). The session keeps them in its
//! durable `eukhe.effects` ledger (`eukhe_durable::harness::effects`); the
//! `unknown_effects_update` and `ran_effects_update` session events carry
//! the whole ledger after each change.

use serde::{Deserialize, Serialize};

use crate::shell::{ShellEffect, ShellEffects};

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

/// The class of an effect (spec/README.md I1): read, write and exec inside
/// the workspace are reversible; every other class is irreversible
/// (`eukhe_bend::rules::irreversible::is_irreversible`).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub enum EffectClass {
    /// Reads files or shell state.
    Read,
    /// Changes files inside the workspace.
    Write,
    /// Runs a program.
    Exec,
    /// Talks to the network.
    Net,
    /// Writes or deletes outside the workspace.
    Outside,
    /// Writes a protected place (`.git`, a `.eukhe` dir, a `PATH` dir, an
    /// auto-start dir, eukhe's run dir, work root or executables dir).
    Protected,
    /// Reads or writes a secret.
    Secret,
    /// Past the vocabulary: an MCP tool not declared read-only.
    Unknown,
}

impl EffectClass {
    /// Every class, in code order.
    pub const ALL: [Self; 8] = [
        Self::Read,
        Self::Write,
        Self::Exec,
        Self::Net,
        Self::Outside,
        Self::Protected,
        Self::Secret,
        Self::Unknown,
    ];

    /// The class's code (`bend/irreversible.bend`: 0 to 7).
    #[must_use]
    pub fn code(self) -> u8 {
        match self {
            Self::Read => 0,
            Self::Write => 1,
            Self::Exec => 2,
            Self::Net => 3,
            Self::Outside => 4,
            Self::Protected => 5,
            Self::Secret => 6,
            Self::Unknown => 7,
        }
    }

    /// The class's wire name.
    #[must_use]
    pub fn as_str(self) -> &'static str {
        match self {
            Self::Read => "read",
            Self::Write => "write",
            Self::Exec => "exec",
            Self::Net => "net",
            Self::Outside => "outside",
            Self::Protected => "protected",
            Self::Secret => "secret",
            Self::Unknown => "unknown",
        }
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

impl EffectClass {
    /// The classes of a shell step's effects, in code order (one class per
    /// effect, same code).
    #[must_use]
    pub fn of_shell(effects: ShellEffects) -> Vec<Self> {
        effects.iter().map(Self::of_shell_effect).collect()
    }

    fn of_shell_effect(effect: ShellEffect) -> Self {
        match effect {
            ShellEffect::Read => Self::Read,
            ShellEffect::Write => Self::Write,
            ShellEffect::Exec => Self::Exec,
            ShellEffect::Net => Self::Net,
            ShellEffect::Outside => Self::Outside,
            ShellEffect::Protected => Self::Protected,
            ShellEffect::Secret => Self::Secret,
        }
    }

    /// The classes' names joined by `+` (`exec+net`).
    #[must_use]
    pub fn names(classes: &[Self]) -> String {
        classes
            .iter()
            .map(|class| class.as_str())
            .collect::<Vec<_>>()
            .join("+")
    }
}

/// What ran an irreversible effect.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub enum RanKind {
    /// One step of a `bash` script (or of a cell's `bash()`).
    ShellStep,
    /// A document tool's or kernel `fs.*` access.
    DocumentAccess,
    /// An MCP tool call not declared read-only.
    McpCall,
}

/// An irreversible effect that ran, as its root session's ledger keeps it
/// (spec I4, I5).
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct RanEffect {
    /// `e<N>`: per root session, from 1, never reused.
    pub id: String,
    /// The effect's stable id (`<session>:<tool call>:<step>`): recording
    /// the same key again changes nothing.
    pub key: String,
    /// The root session's run it ran in.
    pub run: u64,
    pub kind: RanKind,
    /// What ran, for people.
    pub command: String,
    /// Every class of it, in code order.
    pub classes: Vec<EffectClass>,
    /// The subagent that ran it; `None` for the root agent.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub agent: Option<String>,
    /// The session that ran it.
    pub session_id: String,
    /// When it was recorded, in ms since the epoch.
    pub at_ms: u64,
}

impl RanEffect {
    /// The effect's line in the end-of-run message: `- e3 git push origin
    /// main (net)`, `- e4 curl -X POST https://x (exec+net; subagent
    /// fix-tests)`.
    #[must_use]
    pub fn report_line(&self) -> String {
        let classes = EffectClass::names(&self.classes);
        match &self.agent {
            Some(agent) => format!(
                "- {} {} ({classes}; subagent {agent})",
                self.id, self.command
            ),
            None => format!("- {} {} ({classes})", self.id, self.command),
        }
    }

    /// What the model reads in the tool result that caused it:
    /// `[irreversible: e3 git push origin main (net)]`.
    #[must_use]
    pub fn tool_note(&self) -> String {
        format!(
            "[irreversible: {} {} ({})]",
            self.id,
            self.command,
            EffectClass::names(&self.classes)
        )
    }
}

/// An irreversible effect that ran, before its root's ledger numbered it
/// (the ledger sets `id` and `run`).
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct RanEffectDraft {
    /// The effect's stable id (`<session>:<tool call>:<step>`).
    pub key: String,
    pub kind: RanKind,
    pub command: String,
    pub classes: Vec<EffectClass>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub agent: Option<String>,
    pub session_id: String,
    pub at_ms: u64,
}

impl RanEffectDraft {
    /// The effect as the ledger records it: `e<number>` in run `run`.
    #[must_use]
    pub fn recorded(self, number: u64, run: u64) -> RanEffect {
        RanEffect {
            id: format!("e{number}"),
            key: self.key,
            run,
            kind: self.kind,
            command: self.command,
            classes: self.classes,
            agent: self.agent,
            session_id: self.session_id,
            at_ms: self.at_ms,
        }
    }
}

/// The end of one root run (spec I6): the irreversible effects that ran in
/// it, in order, and the effects a crash left unknown that it treated as
/// not run.
#[derive(Debug, Clone, Default, PartialEq, Serialize, Deserialize)]
pub struct RunReport {
    pub ran: Vec<RanEffect>,
    pub unknown: Vec<UnknownEffect>,
}

/// The one end-of-run message of `report`; `None` when both of its lists
/// are empty.
#[must_use]
pub fn run_report_text(report: &RunReport) -> Option<String> {
    let ran = (!report.ran.is_empty()).then(|| {
        std::iter::once("Irreversible effects ran this run:".to_owned())
            .chain(report.ran.iter().map(RanEffect::report_line))
    });
    let unknown = (!report.unknown.is_empty()).then(|| {
        std::iter::once("Unknown after a crash, treated as not run:".to_owned())
            .chain(report.unknown.iter().map(UnknownEffect::report_line))
    });
    let lines: Vec<String> = ran
        .into_iter()
        .flatten()
        .chain(unknown.into_iter().flatten())
        .collect();
    (!lines.is_empty()).then(|| lines.join("\n"))
}

/// The whole ledger for people (`/effects`, `eukhe effects`, spec I7): one
/// [`RanEffect::report_line`] per effect, by id.
#[must_use]
pub fn ledger_text(ran: &[RanEffect]) -> String {
    if ran.is_empty() {
        return "No irreversible effect ran in this session.".to_owned();
    }
    std::iter::once("Irreversible effects ran in this session:".to_owned())
        .chain(ran.iter().map(RanEffect::report_line))
        .collect::<Vec<_>>()
        .join("\n")
}

/// The `get_ran_effects` response data: the root session's whole ledger
/// of irreversible effects that ran, by id.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct RanEffectsReply {
    pub effects: Vec<RanEffect>,
}

/// The daemon asks an attached editor whether one irreversible effect may
/// run (the `editor_permission` frame, spec I12).
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct EditorPermissionRequest {
    /// Unique within the session; the answer names it.
    pub request_id: String,
    /// The tool call of the session that runs the effect; none outside a
    /// tool call.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub tool_call_id: Option<String>,
    /// What runs, for people.
    pub command: String,
    /// Every class of it, in code order.
    pub classes: Vec<EffectClass>,
    /// The subagent that runs it; `None` for the root agent.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub agent: Option<String>,
}

/// The editor's answer to one [`EditorPermissionRequest`].
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum EditorVerdict {
    /// It runs.
    Allow,
    /// It does not run (rejected or cancelled in the editor).
    Reject,
    /// The editor has no permission method: it runs.
    Unsupported,
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

    fn ran(id: &str, command: &str, classes: &[EffectClass], agent: Option<&str>) -> RanEffect {
        RanEffect {
            id: id.to_owned(),
            key: format!("s1:{id}:0"),
            run: 2,
            kind: RanKind::ShellStep,
            command: command.to_owned(),
            classes: classes.to_vec(),
            agent: agent.map(str::to_owned),
            session_id: "s1".to_owned(),
            at_ms: 5,
        }
    }

    /// The wire form: camelCase fields and classes, no `agent` for the
    /// root.
    #[test]
    fn a_ran_effect_round_trips_its_wire_form() {
        let wire = serde_json::json!({
            "id": "e1",
            "key": "s1:e1:0",
            "run": 2,
            "kind": "shellStep",
            "command": "git push origin main",
            "classes": ["net"],
            "sessionId": "s1",
            "atMs": 5,
        });
        let effect = ran("e1", "git push origin main", &[EffectClass::Net], None);
        assert_eq!(serde_json::to_value(&effect).expect("encodes"), wire);
        assert_eq!(
            serde_json::from_value::<RanEffect>(wire).expect("decodes"),
            effect
        );
    }

    #[test]
    fn the_report_line_names_the_classes_and_the_subagent() {
        assert_eq!(
            ran("e3", "git push origin main", &[EffectClass::Net], None).report_line(),
            "- e3 git push origin main (net)"
        );
        assert_eq!(
            ran(
                "e4",
                "curl -X POST https://x",
                &[EffectClass::Exec, EffectClass::Net],
                Some("fix-tests")
            )
            .report_line(),
            "- e4 curl -X POST https://x (exec+net; subagent fix-tests)"
        );
    }

    #[test]
    fn the_tool_note_names_the_effect() {
        assert_eq!(
            ran("e3", "git push origin main", &[EffectClass::Net], None).tool_note(),
            "[irreversible: e3 git push origin main (net)]"
        );
    }

    /// One message: the ran section, then the unknown section; a section
    /// without entries is left out; nothing when both are empty.
    #[test]
    fn the_run_report_text_has_a_section_per_list() {
        let push = ran("e1", "git push", &[EffectClass::Net], None);
        let unknown = job(Some(UnknownCause::NotRepeatSafe), Some(2));
        assert_eq!(
            [
                run_report_text(&RunReport::default()),
                run_report_text(&RunReport {
                    ran: vec![push.clone()],
                    unknown: Vec::new(),
                }),
                run_report_text(&RunReport {
                    ran: Vec::new(),
                    unknown: vec![unknown.clone()],
                }),
                run_report_text(&RunReport {
                    ran: vec![push],
                    unknown: vec![unknown],
                }),
            ],
            [
                None,
                Some("Irreversible effects ran this run:\n- e1 git push (net)".to_owned()),
                Some(
                    "Unknown after a crash, treated as not run:\n- background job: cargo build \
                     (cut by a crash; not safe to repeat)"
                        .to_owned()
                ),
                Some(
                    "Irreversible effects ran this run:\n- e1 git push (net)\nUnknown after a \
                     crash, treated as not run:\n- background job: cargo build (cut by a crash; \
                     not safe to repeat)"
                        .to_owned()
                ),
            ]
        );
    }

    #[test]
    fn the_ledger_text_lists_every_effect() {
        let remove = ran(
            "e2",
            "rm -rf /tmp/x",
            &[EffectClass::Write, EffectClass::Outside],
            Some("cleaner"),
        );
        assert_eq!(
            [
                ledger_text(&[]),
                ledger_text(&[ran("e1", "git push", &[EffectClass::Net], None), remove]),
            ],
            [
                "No irreversible effect ran in this session.".to_owned(),
                "Irreversible effects ran in this session:\n- e1 git push (net)\n- e2 rm -rf /tmp/x \
                 (write+outside; subagent cleaner)"
                    .to_owned(),
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

    #[test]
    fn shell_effects_map_to_their_classes() {
        assert_eq!(
            EffectClass::of_shell(ShellEffects::of(&ShellEffect::ALL)),
            EffectClass::ALL[..7].to_vec()
        );
    }
}
