//! The strength of a check: a check is only as good as what it catches.
//! Before a passed claim counts as done, the verifier breaks the code the
//! task changed on purpose and runs each gauged check (a command, an
//! until-condition) on every broken copy; a check that still passes on a
//! break let it through. The compiled core (`eukhe_bend::rules::strength`)
//! decides from the counts whether the check is strong, whether done is
//! certified, and the label; this module makes and runs the breaks.
//!
//! - Only the lines the task changed are broken ([`changes`]): the
//!   workspace against the commit it held when the checks were set, and
//!   the untracked files. The check's own files (its `--protect` files)
//!   and test files are never broken: they are the check, not the code.
//! - The breaks ([`mutants`]) know Rust, TypeScript and JavaScript, Python
//!   and Bend; any other text file gets the breaks that need no grammar.
//!   At most [`MAX_BREAKS`] are run, spread over the changed lines.
//! - Every run happens in a scratch copy of the workspace ([`scratch`]),
//!   never in the user's workspace: first the check unbroken (it must pass
//!   there, or the breaks show nothing), then the breaks, in parallel over
//!   a few copies.
//! - Each run passes the run's budget like a tool call and counts as one
//!   program run; when the budget refuses one, the measurement is cut
//!   short and shows nothing.

mod changes;
mod mutants;
mod scratch;

use std::path::{Path, PathBuf};
use std::sync::Arc;
use std::time::Instant;

use eukhe_bend::rules::verify::{self, Evidence, Verdict};
use eukhe_budget::PROGRAM_LABEL;
use eukhe_chord::context::{await_with_context, Context};
use eukhe_durable::session::{SessionError, SessionResult};
use eukhe_types::acceptance::Survivor;
use futures::future::BoxFuture;

pub(crate) use changes::baseline;
use mutants::Mutant;
use scratch::Scratch;

use super::evidence::{ran_of, Ran};
use crate::autonomous::run_gate_command;
use crate::durable::budget::{BudgetGate, ToolOutcome};

/// The most breaks one measurement runs.
pub(crate) const MAX_BREAKS: usize = 24;
/// The most surviving breaks a mark keeps.
const MAX_SURVIVORS: usize = 8;
/// The most scratch copies one measurement runs breaks in at once.
const MAX_COPIES: usize = 4;
/// The shortest time limit of one break's run.
const MIN_BREAK_TIMEOUT_MS: u64 = 10_000;

/// What the check must do to pass.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Pass {
    /// A command: exit with this code.
    Exit(u32),
    /// An until-condition: hold (exit 0).
    Holds,
}

/// One measurement's question: the check, and the workspace whose changed
/// lines it breaks.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct Probe {
    pub(crate) command: String,
    pub(crate) pass: Pass,
    pub(crate) timeout_ms: u64,
    /// The check's own files: never broken.
    pub(crate) protected: Vec<String>,
    pub(crate) workspace: PathBuf,
    pub(crate) baseline: Option<String>,
    /// The state the breaks are made from: it also picks the sample.
    pub(crate) at: u64,
}

/// What one measurement found.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct Measurement {
    pub(crate) caught: u64,
    pub(crate) ran: u64,
    pub(crate) planned: u64,
    pub(crate) survivors: Vec<Survivor>,
    /// Why fewer breaks ran than planned, or why none was planned.
    pub(crate) note: Option<String>,
}

impl Measurement {
    /// No break ran out of `planned`, for `note`.
    fn none(planned: usize, note: String) -> Self {
        Self {
            caught: 0,
            ran: 0,
            planned: count(planned),
            survivors: Vec::new(),
            note: Some(note),
        }
    }
}

fn count(n: usize) -> u64 {
    u64::try_from(n).unwrap_or(u64::MAX)
}

/// Breaks the code a task changed and runs a check on each break.
///
/// The product implementation ([`MutantBreaker`]) works in scratch copies
/// of the workspace and never writes the user's files; tests script one.
/// `measure` resolves with what it found (a measurement that could not run
/// says why in its note), and with `Err` only when `cx` was cancelled:
/// nothing is recorded then, and the check is measured again.
pub(crate) trait Breaker: Send + Sync {
    fn measure<'a>(
        &'a self,
        probe: Probe,
        cx: &'a Context,
    ) -> BoxFuture<'a, SessionResult<Measurement>>;
}

/// The product [`Breaker`]: the breaks of [`mutants`] in scratch copies,
/// each run behind the session's budget.
pub(crate) struct MutantBreaker {
    pub(crate) budget: Arc<BudgetGate>,
}

impl Breaker for MutantBreaker {
    fn measure<'a>(
        &'a self,
        probe: Probe,
        cx: &'a Context,
    ) -> BoxFuture<'a, SessionResult<Measurement>> {
        Box::pin(measure(&self.budget, probe, cx))
    }
}

/// A file that belongs to the check, not to the code under test: one of
/// its protected files, or a test file by its path.
fn check_file(path: &str, protected: &[String]) -> bool {
    const TEST_DIRS: &[&str] = &["test", "tests", "__tests__", "spec", "proof", "proofs"];
    let name = path.rsplit('/').next().unwrap_or(path);
    protected.iter().any(|file| file == path)
        || path
            .split('/')
            .rev()
            .skip(1)
            .any(|dir| TEST_DIRS.contains(&dir))
        || name.starts_with("test_")
        || name.contains("_test.")
        || name.contains(".test.")
        || name.contains(".spec.")
        || name == "PROOF.bend"
        || name == "LAWS.bend"
}

/// The breaks of the lines the task changed in the code under test, in
/// file and line order; a Rust file's inline test module (from its
/// `#[cfg(test)]` on) is the check's.
fn plan(
    workspace: &Path,
    baseline: Option<&str>,
    protected: &[String],
) -> Result<Vec<Mutant>, String> {
    let changed = changes::changed_lines(workspace, baseline).map_err(|unknown| unknown.text())?;
    let mut planned = Vec::new();
    for file in changed
        .into_iter()
        .filter(|file| !check_file(&file.path, protected))
    {
        let Ok(text) = std::fs::read_to_string(workspace.join(&file.path)) else {
            continue;
        };
        let lines: Vec<&str> = text.lines().collect();
        let tests_from = (mutants::Lang::of(&file.path) == mutants::Lang::Rust)
            .then(|| lines.iter().position(|line| line.trim() == "#[cfg(test)]"))
            .flatten()
            .unwrap_or(lines.len());
        for number in file.lines {
            let index = usize::try_from(number)
                .unwrap_or(usize::MAX)
                .saturating_sub(1);
            if let Some(line) = lines.get(index).filter(|_| index < tests_from) {
                planned.extend(mutants::of_line(&file.path, number, line));
            }
        }
    }
    Ok(planned)
}

/// How one break's run ended.
enum Outcome {
    Caught,
    Survived,
    /// It did not run (the budget refused it, the check could not start):
    /// the measurement is cut short, for this reason.
    NotRun(String),
}

/// The check run in `dir` behind the budget: what it did, or why it did not
/// run.
///
/// # Errors
///
/// `cx` was cancelled.
async fn run_check(
    budget: &Arc<BudgetGate>,
    probe: &Probe,
    dir: &Path,
    timeout_ms: u64,
    cx: &Context,
) -> SessionResult<Result<Ran, String>> {
    let outcome = budget
        .gated_call(
            format!("{PROGRAM_LABEL}acceptance-break"),
            cx.clone(),
            |cx| async move {
                await_with_context(run_gate_command(&probe.command, dir, timeout_ms), &cx)
                    .await
                    .map(|result| ran_of(result, timeout_ms))
            },
        )
        .await;
    match outcome {
        ToolOutcome::Ran(Ok(ran)) => Ok(Ok(ran)),
        ToolOutcome::Ran(Err(aborted)) => Err(SessionError::Aborted(aborted)),
        ToolOutcome::Refused(_) => Ok(Err(
            "the run's budget left no room for more breaks".to_owned()
        )),
    }
}

/// The check's verdict on what one run showed: the compiled core's.
fn verdict(pass: Pass, evidence: Evidence) -> SessionResult<Verdict> {
    match pass {
        Pass::Exit(code) => verify::grade_command(u64::from(code), true, evidence),
        Pass::Holds => verify::grade_until(evidence),
    }
    .map_err(SessionError::other)
}

/// How a break's run ended: a check that passes let the break through; one
/// that fails, runs past its time or dies caught it; one that could not
/// start or was cancelled showed nothing.
fn outcome(pass: Pass, ran: &Ran) -> SessionResult<Outcome> {
    Ok(match verdict(pass, ran.evidence)? {
        Verdict::Confirmed => Outcome::Survived,
        Verdict::Refuted => Outcome::Caught,
        Verdict::Broken => match ran.evidence {
            Evidence::SpawnFailed => Outcome::NotRun(format!("a break's run {}", ran.summary)),
            Evidence::Exited(_) | Evidence::NoStatus | Evidence::TimedOut | Evidence::Cancelled => {
                Outcome::Caught
            }
        },
        Verdict::Unjudged => Outcome::NotRun("a break's run was cancelled".to_owned()),
    })
}

/// What one scratch copy's share of the breaks showed.
#[derive(Default)]
struct Share {
    caught: u64,
    ran: u64,
    survivors: Vec<Survivor>,
    note: Option<String>,
}

/// Run `breaks` one after another in `copy`, each file put back after its
/// run; stop at the first break that did not run.
///
/// # Errors
///
/// `cx` was cancelled.
async fn run_share(
    budget: &Arc<BudgetGate>,
    probe: &Probe,
    copy: &Scratch,
    breaks: Vec<Mutant>,
    timeout_ms: u64,
    cx: &Context,
) -> SessionResult<Share> {
    let mut share = Share::default();
    for mutant in breaks {
        let path = copy.root().join(&mutant.path);
        let Ok(original) = std::fs::read_to_string(&path) else {
            share.note = Some(format!(
                "{} could not be read in the scratch copy",
                mutant.path
            ));
            break;
        };
        let broken = broken_text(&original, &mutant);
        if let Err(error) = std::fs::write(&path, broken) {
            share.note = Some(format!("{} could not be broken: {error}", mutant.path));
            break;
        }
        drop_bytecode(&path);
        let ran = run_check(budget, probe, copy.root(), timeout_ms, cx).await;
        let restored = std::fs::write(&path, &original);
        drop_bytecode(&path);
        let ran = ran?;
        if let Err(error) = restored {
            share.note = Some(format!("{} could not be put back: {error}", mutant.path));
            break;
        }
        let ended = match ran {
            Ok(ran) => outcome(probe.pass, &ran)?,
            Err(reason) => Outcome::NotRun(reason),
        };
        match ended {
            Outcome::Caught => {
                share.caught += 1;
                share.ran += 1;
            }
            Outcome::Survived => {
                share.ran += 1;
                share.survivors.push(Survivor {
                    path: mutant.path.clone(),
                    line: mutant.line,
                    change: mutant.change.clone(),
                });
            }
            Outcome::NotRun(reason) => {
                share.note = Some(reason);
                break;
            }
        }
    }
    Ok(share)
}

/// Remove the compiled cache beside the file at `path` in a scratch copy
/// (Python's `__pycache__`): a cache keyed by the source's mtime in whole
/// seconds and its size would run the unbroken code for a break of the
/// same length written within the same second (`*` to `+`), and the
/// broken code after the file is put back.
fn drop_bytecode(path: &Path) {
    if let Some(dir) = path.parent() {
        // Absent is the usual case; a cache that cannot be removed only
        // risks the stale run it guards against.
        let _ = std::fs::remove_dir_all(dir.join("__pycache__"));
    }
}

/// `original` with the line of `mutant` replaced by its text (the line
/// endings kept).
fn broken_text(original: &str, mutant: &Mutant) -> String {
    let index = usize::try_from(mutant.line)
        .unwrap_or(usize::MAX)
        .saturating_sub(1);
    original
        .split_inclusive('\n')
        .enumerate()
        .map(|(at, line)| {
            if at == index {
                let ending = &line[line.trim_end_matches(['\n', '\r']).len()..];
                format!("{}{ending}", mutant.text)
            } else {
                line.to_owned()
            }
        })
        .collect()
}

/// The time limit of one break's run: three times the unbroken run plus
/// five seconds (a break that loops is caught by it), at least
/// [`MIN_BREAK_TIMEOUT_MS`], at most the check's own limit.
fn break_timeout(unbroken_ms: u64, limit_ms: u64) -> u64 {
    unbroken_ms
        .saturating_mul(3)
        .saturating_add(5000)
        .max(MIN_BREAK_TIMEOUT_MS)
        .min(limit_ms)
}

/// How many scratch copies run breaks at once.
fn copies(planned: usize) -> usize {
    let cores = std::thread::available_parallelism().map_or(1, std::num::NonZero::get);
    (cores / 2).clamp(1, MAX_COPIES).min(planned)
}

/// A scratch copy of `workspace`, made off the async threads.
async fn copy_of(workspace: &Path) -> Result<Scratch, String> {
    let workspace = workspace.to_path_buf();
    tokio::task::spawn_blocking(move || scratch::copy(&workspace))
        .await
        .map_err(|error| error.to_string())
        .and_then(|copied| copied.map_err(|error| error.to_string()))
        .map_err(|error| format!("a scratch copy of the workspace could not be made: {error}"))
}

/// Measure `probe`'s check: [`plan`], the unbroken run in a first scratch
/// copy, then the sampled breaks over [`copies`] copies.
///
/// # Errors
///
/// `cx` was cancelled.
async fn measure(
    budget: &Arc<BudgetGate>,
    probe: Probe,
    cx: &Context,
) -> SessionResult<Measurement> {
    let (workspace, baseline, protected) = (
        probe.workspace.clone(),
        probe.baseline.clone(),
        probe.protected.clone(),
    );
    let planned =
        tokio::task::spawn_blocking(move || plan(&workspace, baseline.as_deref(), &protected))
            .await
            .map_err(SessionError::other)?;
    let breaks = match planned {
        Err(note) => return Ok(Measurement::none(0, note)),
        Ok(all) => mutants::sample(all, MAX_BREAKS, probe.at),
    };
    let planned = breaks.len();
    if planned == 0 {
        return Ok(Measurement::none(
            0,
            "the task changed no line of code that eukhe can break".to_owned(),
        ));
    }
    let first = match copy_of(&probe.workspace).await {
        Ok(copy) => copy,
        Err(note) => return Ok(Measurement::none(planned, note)),
    };
    let started = Instant::now();
    let unbroken = match run_check(budget, &probe, first.root(), probe.timeout_ms, cx).await? {
        Ok(ran) => ran,
        Err(note) => return Ok(Measurement::none(planned, note)),
    };
    if verdict(probe.pass, unbroken.evidence)? != Verdict::Confirmed {
        return Ok(Measurement::none(
            planned,
            format!(
                "the check does not pass unbroken in a scratch copy of the workspace ({}), so its breaks show nothing",
                unbroken.summary
            ),
        ));
    }
    let unbroken_ms = u64::try_from(started.elapsed().as_millis()).unwrap_or(u64::MAX);
    let timeout_ms = break_timeout(unbroken_ms, probe.timeout_ms);
    let mut copies_made = vec![first];
    for _ in 1..copies(planned) {
        match copy_of(&probe.workspace).await {
            Ok(copy) => copies_made.push(copy),
            // Fewer copies run the same breaks, only slower.
            Err(_) => break,
        }
    }
    let mut shares: Vec<Vec<Mutant>> = vec![Vec::new(); copies_made.len()];
    for (index, mutant) in breaks.into_iter().enumerate() {
        shares[index % copies_made.len()].push(mutant);
    }
    let runs = copies_made
        .iter()
        .zip(shares)
        .map(|(copy, share)| run_share(budget, &probe, copy, share, timeout_ms, cx));
    let mut found = Measurement {
        caught: 0,
        ran: 0,
        planned: count(planned),
        survivors: Vec::new(),
        note: None,
    };
    for share in futures::future::join_all(runs).await {
        let share = share?;
        found.caught += share.caught;
        found.ran += share.ran;
        found.survivors.extend(share.survivors);
        found.note = found.note.or(share.note);
    }
    found
        .survivors
        .sort_by(|a, b| (&a.path, a.line).cmp(&(&b.path, b.line)));
    found.survivors.truncate(MAX_SURVIVORS);
    Ok(found)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn the_check_s_files_are_never_broken() {
        let protected = vec!["checks/run.sh".to_owned()];
        assert_eq!(
            [
                "src/lib.rs",
                "checks/run.sh",
                "tests/api.rs",
                "pkg/test_math.py",
                "web/app.test.ts",
                "web/app.spec.js",
                "go/math_test.go",
                "proof/area/law.bend",
                "LAWS.bend",
                "bend/model.bend",
            ]
            .map(|path| check_file(path, &protected)),
            [false, true, true, true, true, true, true, true, true, false]
        );
    }

    #[test]
    fn a_break_replaces_its_line_and_keeps_the_endings() {
        let mutant = Mutant {
            path: "a.py".to_owned(),
            line: 2,
            text: "    pass".to_owned(),
            change: "line dropped".to_owned(),
        };
        assert_eq!(
            broken_text("def f():\r\n    x = 1\r\n    return x\n", &mutant),
            "def f():\r\n    pass\r\n    return x\n"
        );
    }

    #[test]
    fn a_break_runs_at_most_the_check_s_limit() {
        assert_eq!(
            [
                break_timeout(1000, 600_000),
                break_timeout(100_000, 600_000),
                break_timeout(400_000, 600_000),
                break_timeout(0, 5000),
            ],
            [10_000, 305_000, 600_000, 5000]
        );
    }
}
