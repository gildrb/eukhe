//! Blind attacks on the checks (layer 2): an attacker, a model request
//! that never sees the worker's transcript, reads the user's messages, the
//! checks and the code the task changed, and answers wrong code for one
//! changed file with a witness (a command and the stdout the task requires
//! of it). The attack runs in a scratch copy of the workspace: the wrong
//! code against every gauged check, then the witness, whose stdout alone is
//! compared; a separate judge decides whether the required output is what
//! the task asks. The compiled
//! core (`eukhe_bend::rules::attack`) decides the outcome; a survivor keeps
//! done from being certified (`spec/README.md` S8).

use std::path::{Path, PathBuf};
use std::sync::Arc;

use eukhe_bend::rules::attack::{self, Run};
use eukhe_bend::rules::verify::{Answer, Verdict};
use eukhe_chord::context::Context;
use eukhe_durable::session::{SessionError, SessionResult};
use eukhe_durable::types::ConversationId;
use eukhe_types::acceptance::{AttackMark, AttackOutcome};
use futures::future::BoxFuture;

use super::scratch::Scratch;
use super::{changes, check_file, copy_of, run_check, verdict, Pass, Probe};
use crate::autonomous::now_millis;
use crate::durable::acceptance::evidence::{read_answer, Ran};
use crate::durable::acceptance::{Judge, JudgeQuestion, JudgeReply, JudgeRequest};
use crate::durable::budget::BudgetGate;

/// The most attacks the verifier makes on one state.
pub(crate) const MAX_ATTACKS: usize = 2;
/// The most characters of the changed code an attacker reads.
const MAX_CODE_CHARS: usize = 40_000;
/// The most characters of a witness's output a mark keeps.
const MAX_GOT_CHARS: usize = 400;
/// The time limit of a witness's run.
const WITNESS_TIMEOUT_MS: u64 = 60_000;

/// One gauged check an attack must pass.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct Gauged {
    pub(crate) command: String,
    pub(crate) pass: Pass,
    pub(crate) timeout_ms: u64,
}

/// One attack's question: the task, the checks, and the workspace whose
/// changed code it attacks.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct AttackProbe {
    pub(crate) conversation_id: ConversationId,
    /// The user's messages, oldest first: the task, in its owner's words.
    pub(crate) messages: Vec<String>,
    /// The checks as the owner set them, one line each.
    pub(crate) checks: Vec<String>,
    /// The gauged checks the wrong code must pass.
    pub(crate) gauged: Vec<Gauged>,
    /// Every check's own files: never replaced.
    pub(crate) protected: Vec<String>,
    pub(crate) workspace: PathBuf,
    pub(crate) baseline: Option<String>,
    /// The state the attack is made on.
    pub(crate) at: u64,
    /// The attack's number on this state, from 1.
    pub(crate) number: usize,
}

/// Attacks the checks of a task with wrong code. The product
/// implementation ([`ModelAttacker`]) asks the session's model and works in
/// scratch copies; tests script one. `attack` resolves with the mark (an
/// attack that could not run says why in its note), and with `Err` only
/// when `cx` was cancelled: nothing is recorded then.
pub(crate) trait Attacker: Send + Sync {
    fn attack<'a>(
        &'a self,
        probe: AttackProbe,
        cx: &'a Context,
    ) -> BoxFuture<'a, SessionResult<AttackMark>>;
}

/// The product [`Attacker`]: the judge's model as the attacker and as the
/// witness's judge, each run behind the session's budget.
pub(crate) struct ModelAttacker {
    pub(crate) budget: Arc<BudgetGate>,
    pub(crate) judge: Arc<dyn Judge>,
}

impl Attacker for ModelAttacker {
    fn attack<'a>(
        &'a self,
        probe: AttackProbe,
        cx: &'a Context,
    ) -> BoxFuture<'a, SessionResult<AttackMark>> {
        Box::pin(attack(&self.budget, self.judge.as_ref(), probe, cx))
    }
}

/// What an attacker answered.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct Attack {
    pub(crate) path: String,
    pub(crate) content: String,
    pub(crate) witness: String,
    pub(crate) required: String,
}

/// The attack in an attacker's reply: its first JSON object with the
/// string fields `path`, `content`, `witness` and `required`.
///
/// # Errors
///
/// The reply holds no such object, in words.
pub(crate) fn read_attack(reply: &str) -> Result<Attack, String> {
    let start = reply.find('{');
    let end = reply.rfind('}');
    let (Some(start), Some(end)) = (start, end) else {
        return Err("the attacker's reply holds no JSON object".to_owned());
    };
    let object: serde_json::Value = serde_json::from_str(reply.get(start..=end).unwrap_or(""))
        .map_err(|error| format!("the attacker's reply does not read as JSON: {error}"))?;
    let field = |name: &str| {
        object
            .get(name)
            .and_then(serde_json::Value::as_str)
            .map(str::to_owned)
            .ok_or_else(|| format!("the attacker's reply has no string `{name}`"))
    };
    Ok(Attack {
        path: field("path")?,
        content: field("content")?,
        witness: field("witness")?,
        required: field("required")?,
    })
}

fn cut(text: &str, max: usize) -> String {
    if text.chars().count() <= max {
        return text.to_owned();
    }
    let prefix: String = text.chars().take(max).collect();
    format!("{prefix}\n... [truncated]")
}

/// The attacker's evidence: the checks, then each changed file of the
/// code under test, whole.
fn attack_evidence(probe: &AttackProbe, files: &[(String, String)]) -> String {
    let mut parts = vec![format!("<checks>\n{}\n</checks>", probe.checks.join("\n"))];
    for (path, text) in files {
        parts.push(format!("<file path=\"{path}\">\n{text}\n</file>"));
    }
    cut(&parts.join("\n\n"), MAX_CODE_CHARS)
}

/// The changed files of the code under test and their text; or why there
/// is none.
fn changed_code(probe: &AttackProbe) -> Result<Vec<(String, String)>, String> {
    let changed = changes::changed_lines(&probe.workspace, probe.baseline.as_deref())
        .map_err(|unknown| unknown.text())?;
    let files: Vec<(String, String)> = changed
        .into_iter()
        .filter(|file| !check_file(&file.path, &probe.protected))
        .filter_map(|file| {
            std::fs::read_to_string(probe.workspace.join(&file.path))
                .ok()
                .map(|text| (file.path, text))
        })
        .collect();
    if files.is_empty() {
        return Err("the task changed no file of code under test to attack".to_owned());
    }
    Ok(files)
}

/// A mark for `probe` that ended as `outcome` for `note`.
fn mark(
    probe: &AttackProbe,
    outcome: AttackOutcome,
    attack: Option<&Attack>,
    got: &str,
    note: String,
) -> AttackMark {
    AttackMark {
        outcome,
        at: probe.at,
        path: attack.map(|attack| attack.path.clone()).unwrap_or_default(),
        witness: attack
            .map(|attack| attack.witness.clone())
            .unwrap_or_default(),
        required: attack
            .map(|attack| attack.required.clone())
            .unwrap_or_default(),
        got: cut(got, MAX_GOT_CHARS),
        note,
        attacked_at: now_millis(),
    }
}

fn outcome_of(outcome: attack::Outcome) -> AttackOutcome {
    match outcome {
        attack::Outcome::Survived => AttackOutcome::Survived,
        attack::Outcome::Clean => AttackOutcome::Clean,
        attack::Outcome::Unrun => AttackOutcome::Unrun,
    }
}

/// The judge's reply text, or why there is none.
///
/// # Errors
///
/// `cx` was cancelled.
async fn ask(
    judge: &dyn Judge,
    request: JudgeRequest,
    cx: &Context,
) -> SessionResult<Result<String, String>> {
    match judge.judge(request, cx).await {
        JudgeReply::Text(text) => Ok(Ok(text)),
        JudgeReply::Unavailable(why) => Ok(Err(why)),
        JudgeReply::Stopped => match cx.abort_signal().and_then(|signal| signal.reason()) {
            Some(reason) => Err(SessionError::Aborted(reason)),
            None => Ok(Err("the request was cancelled".to_owned())),
        },
    }
}

/// Make one attack on `probe`'s checks: ask the attacker, run its wrong
/// code against the gauged checks and its witness in a scratch copy, ask
/// the judge about the required output, and let the compiled core decide.
///
/// # Errors
///
/// `cx` was cancelled.
async fn attack(
    budget: &Arc<BudgetGate>,
    judge: &dyn Judge,
    probe: AttackProbe,
    cx: &Context,
) -> SessionResult<AttackMark> {
    let unrun = |probe: &AttackProbe, attack: Option<&Attack>, note: String| {
        mark(probe, AttackOutcome::Unrun, attack, "", note)
    };
    let scan = probe.clone();
    let files = tokio::task::spawn_blocking(move || changed_code(&scan))
        .await
        .map_err(SessionError::other)?;
    let files = match files {
        Ok(files) => files,
        Err(note) => return Ok(unrun(&probe, None, note)),
    };
    let reply = ask(
        judge,
        JudgeRequest {
            conversation_id: probe.conversation_id,
            question: JudgeQuestion::Attack(probe.messages.clone()),
            evidence: attack_evidence(&probe, &files),
            model: None,
        },
        cx,
    )
    .await?;
    let found = match reply.and_then(|text| read_attack(&text)) {
        Ok(found) => found,
        Err(note) => {
            return Ok(unrun(
                &probe,
                None,
                format!("the attacker gave no attack: {note}"),
            ))
        }
    };
    if !files.iter().any(|(path, _)| *path == found.path) {
        return Ok(unrun(
            &probe,
            Some(&found),
            format!(
                "the attacker replaced {}, which is no changed file of the code under test",
                found.path
            ),
        ));
    }
    let copy = match copy_with(&probe.workspace, Some(&found)).await {
        Ok(copy) => copy,
        Err(note) => return Ok(unrun(&probe, Some(&found), note)),
    };
    // The wrong code against every gauged check: the first that fails
    // catches it.
    for gauged in &probe.gauged {
        let check = Probe {
            command: gauged.command.clone(),
            pass: gauged.pass,
            timeout_ms: gauged.timeout_ms,
            protected: Vec::new(),
            workspace: copy.root().to_path_buf(),
            baseline: None,
            at: probe.at,
        };
        let ran = match run_check(budget, &check, copy.root(), gauged.timeout_ms, cx).await? {
            Ok(ran) => ran,
            Err(note) => return Ok(unrun(&probe, Some(&found), note)),
        };
        if verdict(gauged.pass, ran.evidence)? != Verdict::Confirmed {
            let run = Run {
                ran: true,
                passes: false,
                differs: false,
                agrees: None,
            };
            let outcome = outcome_of(attack::outcome(run).map_err(SessionError::other)?);
            return Ok(mark(
                &probe,
                outcome,
                Some(&found),
                "",
                format!("check `{}` caught it ({})", gauged.command, ran.summary),
            ));
        }
    }
    drop(copy);
    // The witness runs the same way on both versions, each in a fresh
    // copy. What it shows is its stdout, the output the task requires of a
    // command; its stderr (an interpreter's warning, a log line) is not
    // compared: a witness that means stderr says `2>&1`. It shows the wrong
    // code wrong when the code under test prints the required output and
    // the wrong code another; it shows the code under test wrong when that
    // prints another, whatever the wrong code prints (the worker's own
    // lookup table prints what the attacker's does).
    let wrong = match witness_run(budget, &probe, &found.witness, Some(&found), cx).await? {
        Ok(ran) => ran,
        Err(note) => return Ok(unrun(&probe, Some(&found), note)),
    };
    let real = match witness_run(budget, &probe, &found.witness, None, cx).await? {
        Ok(ran) => ran,
        Err(note) => return Ok(unrun(&probe, Some(&found), note)),
    };
    let got = wrong.stdout.trim().to_owned();
    let real_got = real.stdout.trim();
    let required = found.required.trim();
    let real_fails = real_got != required;
    let differs = real_fails || got != required;
    let agrees = if differs {
        let reply = ask(
            judge,
            JudgeRequest {
                conversation_id: probe.conversation_id,
                question: JudgeQuestion::Witness {
                    messages: probe.messages.clone(),
                    witness: found.witness.clone(),
                    required: found.required.clone(),
                },
                evidence: witness_evidence(&found.witness, &wrong, &real),
                model: None,
            },
            cx,
        )
        .await?;
        match reply
            .as_ref()
            .map(|text| read_answer(&JudgeReply::Text(text.clone())))
        {
            Ok(Answer::Yes) => Some(true),
            Ok(Answer::No) => Some(false),
            Ok(Answer::Unreadable | Answer::Unavailable | Answer::Stopped) | Err(_) => None,
        }
    } else {
        None
    };
    let run = Run {
        ran: true,
        passes: true,
        differs,
        agrees,
    };
    // What survives the checks is the code under test itself when the
    // witness shows that wrong.
    let outcome = match outcome_of(attack::outcome(run).map_err(SessionError::other)?) {
        AttackOutcome::Survived if real_fails => AttackOutcome::Fails,
        outcome => outcome,
    };
    let note = match outcome {
        AttackOutcome::Survived => format!(
            "the checks passed wrong code in {}: `{}` gives {}, the task requires {}",
            found.path,
            found.witness,
            one_line(&got),
            one_line(&found.required)
        ),
        AttackOutcome::Fails => format!(
            "`{}` gives {}, the task requires {}",
            found.witness,
            one_line(real_got),
            one_line(&found.required)
        ),
        AttackOutcome::Clean if !differs => {
            "its witness shows no wrong output: the code it wrote does what the task requires there"
                .to_owned()
        }
        AttackOutcome::Clean => {
            "the judge did not agree the required output is what the task asks".to_owned()
        }
        AttackOutcome::Unrun => "the judge gave no verdict on the required output".to_owned(),
    };
    Ok(mark(&probe, outcome, Some(&found), &got, note))
}

/// A scratch copy of `workspace`, with the attack's file written over it
/// when `replacement` is one; or why there is none.
async fn copy_with(workspace: &Path, replacement: Option<&Attack>) -> Result<Scratch, String> {
    let copy = copy_of(workspace).await?;
    if let Some(found) = replacement {
        let path = copy.root().join(&found.path);
        std::fs::write(&path, &found.content).map_err(|error| {
            format!(
                "{} could not be written in the scratch copy: {error}",
                found.path
            )
        })?;
        super::drop_bytecode(&path);
    }
    Ok(copy)
}

/// `witness` run in a fresh copy of the workspace, the attack's file
/// written over it when `replacement` is one: the attacker's code and the
/// code under test are run the same way. What it did, or why it did not
/// run.
///
/// # Errors
///
/// `cx` was cancelled.
async fn witness_run(
    budget: &Arc<BudgetGate>,
    probe: &AttackProbe,
    witness: &str,
    replacement: Option<&Attack>,
    cx: &Context,
) -> SessionResult<Result<Ran, String>> {
    let copy = match copy_with(&probe.workspace, replacement).await {
        Ok(copy) => copy,
        Err(note) => return Ok(Err(note)),
    };
    let check = Probe {
        command: witness.to_owned(),
        pass: Pass::Exit(0),
        timeout_ms: WITNESS_TIMEOUT_MS,
        protected: Vec::new(),
        workspace: copy.root().to_path_buf(),
        baseline: None,
        at: probe.at,
    };
    run_check(budget, &check, copy.root(), WITNESS_TIMEOUT_MS, cx).await
}

/// The witness judge's evidence: what `witness` printed on the attacker's
/// code and on the code under test, each version's stdout (compared) and
/// stderr (not compared) apart.
fn witness_evidence(witness: &str, wrong: &Ran, real: &Ran) -> String {
    format!(
        "`{witness}` printed:\n\n{}\n\n{}",
        printed("on the adversary's code", wrong),
        printed("on the code under test", real)
    )
}

/// What one version printed, for the witness judge: its stdout, then its
/// stderr when there is any.
fn printed(version: &str, ran: &Ran) -> String {
    let stdout = cut(ran.stdout.trim(), MAX_GOT_CHARS);
    let stderr = ran.stderr.trim();
    if stderr.is_empty() {
        format!("{version}, on stdout:\n{stdout}")
    } else {
        format!(
            "{version}, on stdout:\n{stdout}\n{version}, on stderr (not compared):\n{}",
            cut(stderr, MAX_GOT_CHARS)
        )
    }
}

/// `text` on one line, cut short.
fn one_line(text: &str) -> String {
    let joined = text.split_whitespace().collect::<Vec<_>>().join(" ");
    format!("`{}`", cut(&joined, 80))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn an_attack_reads_from_the_first_json_object_of_the_reply() {
        let reply = "Here:\n```json\n{\"path\": \"lib.py\", \"content\": \"def f(n):\\n    return 0\\n\", \"witness\": \"python3 -c 'import lib; print(lib.f(5))'\", \"required\": \"120\"}\n```";
        assert_eq!(
            read_attack(reply),
            Ok(Attack {
                path: "lib.py".to_owned(),
                content: "def f(n):\n    return 0\n".to_owned(),
                witness: "python3 -c 'import lib; print(lib.f(5))'".to_owned(),
                required: "120".to_owned(),
            })
        );
        assert_eq!(
            read_attack("no attack"),
            Err("the attacker's reply holds no JSON object".to_owned())
        );
        assert_eq!(
            read_attack("{\"path\": \"lib.py\"}"),
            Err("the attacker's reply has no string `content`".to_owned())
        );
    }
}
