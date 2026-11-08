//! The autoresearch operations of the `autoresearch` skill and the
//! `/autoresearch` command. Each locks the store of the current branch,
//! steps the Lab, logs what it accepted, and only then carries out the
//! effect the Lab answered (write-ahead). The replies are JSON for the
//! skill, which formats them for the model; metric values are the Lab's
//! exact decimals, as text.

use std::path::{Path, PathBuf};
use std::time::{Duration, SystemTime};

use anyhow::Context as _;
use eukhe_bend::rules::autoresearch::{
    Config, Direction, Effect, Event, Metric, Mode, RunRow, Snapshot, Status,
};
use serde_json::{json, Value};

use super::git::{self, ensure_branch, Branch, Workspace};
use super::runner::{self, RunEnd, HARNESS, SCRIPT, TIMEOUT_EXIT};
use super::store::Durability;
use super::Autoresearch;

/// The last lines of a run's output its reply shows, and their bytes at
/// most.
const TAIL_LINES: usize = 10;
const TAIL_BYTES: usize = 4096;

/// The runs of the current segment `state` lists (the last ones).
const STATE_RUNS: usize = 20;

/// The heading of the ideas backlog in the notes.
const IDEAS: &str = "## Ideas";

/// The heading of the constraints in the notes.
const CONSTRAINTS: &str = "## Constraints";

/// What an operation answers: the reply to the caller, the Lab's mode
/// after it, and whether it turned the mode on (an accepted init or
/// `SetMode(On)`).
#[derive(Debug, Clone, PartialEq)]
pub(crate) struct Reply {
    pub(crate) value: Value,
    pub(crate) mode: Mode,
    pub(crate) started: bool,
}

/// `autoresearch.init` arguments.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct InitArgs {
    pub(crate) name: String,
    pub(crate) metric: String,
    /// `None`: the goal of the session's config, else the name.
    pub(crate) goal: Option<String>,
    pub(crate) unit: String,
    pub(crate) direction: Direction,
    pub(crate) secondary: Vec<String>,
    pub(crate) scope: Vec<String>,
    pub(crate) off_limits: Vec<String>,
    /// Written to the notes' `## Constraints` section.
    pub(crate) constraints: Vec<String>,
    pub(crate) max_iterations: Option<u32>,
    pub(crate) new_segment: bool,
}

/// `autoresearch.log` arguments: the earlier runs to flag first, then the
/// log of the pending run.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct LogArgs {
    pub(crate) status: Status,
    pub(crate) description: String,
    pub(crate) justification: Option<String>,
    pub(crate) flags: Vec<(u32, String)>,
}

/// What `/autoresearch <goal>` did: the branch, and whether the store had
/// a config already (a resume) or not (the harness comes first).
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct Begun {
    pub(crate) branch: Branch,
    pub(crate) configured: bool,
}

impl Autoresearch {
    /// Open or reconfigure the session (`Event::Init`). Off an
    /// `autoresearch/*` branch, the branch comes first (a clean tree is
    /// needed); on it, an accepted init commits the harness changes as the
    /// baseline.
    ///
    /// # Errors
    ///
    /// [`super::Refused`], a dirty tree off the branch, a store or core
    /// failure.
    pub(crate) async fn init(&self, args: InitArgs) -> anyhow::Result<Reply> {
        let workspace = Workspace::of(&self.cwd).await?;
        let goal_hint = args.goal.clone().unwrap_or_else(|| args.name.clone());
        let branch = ensure_branch(&workspace, Some(&goal_hint), &today()?).await?;
        let mut session = self.session().await?;
        let previous = session.opened()?.lab.snapshot()?.config;
        let goal = args
            .goal
            .or_else(|| previous.map(|config| config.goal))
            .unwrap_or_else(|| args.name.clone());
        let config = Config {
            name: args.name.clone(),
            goal: goal.clone(),
            metric: args.metric,
            unit: args.unit,
            direction: args.direction,
            secondary: args.secondary,
            scope: args.scope,
            off_limits: args.off_limits,
            max_iterations: args.max_iterations,
        };
        let harness = session.workspace.root.join(HARNESS).is_file();
        session.accept(
            &Event::Init {
                config,
                new_segment: args.new_segment,
                harness,
            },
            Durability::Synced,
        )?;
        let git = match (
            &session.workspace.repo,
            session.workspace.on_autoresearch_branch(),
        ) {
            (Some(repo), true) => outcome_of(
                repo.commit_all(&format!(
                    "autoresearch: harness\n\nBenchmark entrypoint: {SCRIPT}\nGoal: {goal}"
                ))
                .await,
            ),
            (Some(_), false) => json!("not on an autoresearch/* branch: nothing committed"),
            (None, _) => Value::Null,
        };
        let notes_path = session.opened()?.store.notes_path();
        if !args.constraints.is_empty() {
            let notes = read_notes(&notes_path)?;
            write_notes(
                &notes_path,
                &set_section(&notes, CONSTRAINTS, &bullets(&args.constraints)),
            )?;
        }
        let snapshot = session.opened()?.lab.snapshot()?;
        Ok(Reply {
            value: json!({
                "branch": branch.line(),
                "git": git,
                "state": snapshot_json(&snapshot),
            }),
            mode: snapshot.mode,
            started: true,
        })
    }

    /// Run the benchmark once (`Start`, a `Line` per output line,
    /// `Finish`). A run the gate refused stays unfinished: the next run
    /// abandons it.
    ///
    /// # Errors
    ///
    /// [`super::Refused`] (no session yet), a store, run or core failure.
    pub(crate) async fn run(&self, timeout: Duration, request: &str) -> anyhow::Result<Reply> {
        let mut session = self.session().await?;
        let started = session.opened()?.lab.snapshot()?.runs.len();
        let run = u32::try_from(started)
            .ok()
            .and_then(|count| count.checked_add(1))
            .context("too many runs")?;
        session.accept(&Event::Start { run }, Durability::Synced)?;
        let log = session.opened()?.store.run_dir(run)?.join("benchmark.log");
        let gate = (self.gate)(request);
        let root = session.workspace.root.clone();
        let end = runner::run(gate, root, &log, timeout, |text| {
            session
                .accept(&Event::Line { text }, Durability::Buffered)
                .map(drop)
        })
        .await?;
        let (exit_code, timed_out, refused) = match end {
            RunEnd::Exited(code) => (Some(code), false, None),
            RunEnd::TimedOut => (Some(TIMEOUT_EXIT), true, None),
            RunEnd::Refused(text) => (None, false, Some(text)),
        };
        if let Some(exit_code) = exit_code {
            session.accept(
                &Event::Finish {
                    exit_code,
                    timed_out,
                },
                Durability::Synced,
            )?;
        }
        let snapshot = session.opened()?.lab.snapshot()?;
        let row = snapshot.runs.iter().find(|row| row.id == run);
        Ok(Reply {
            value: json!({
                "run": row.map(row_json),
                "exit_code": exit_code,
                "timed_out": timed_out,
                "refused": refused,
                "tail": tail(&log)?,
                "log": log.display().to_string(),
                "config": snapshot.config.as_ref().map(config_json),
                "baseline": metric(snapshot.baseline.as_ref()),
                "best": metric(snapshot.best.as_ref()),
            }),
            mode: snapshot.mode,
            started: false,
        })
    }

    /// Flag the runs of `args.flags`, then log the pending run, then carry
    /// out the Lab's effect: commit a kept run, reset the tree for every
    /// other status. The scope deviations are the changed paths outside
    /// the scope or inside the off-limits paths.
    ///
    /// # Errors
    ///
    /// [`super::Refused`], a store or core failure.
    pub(crate) async fn log(&self, args: LogArgs) -> anyhow::Result<Reply> {
        let mut session = self.session().await?;
        let mut flagged = Vec::new();
        for (run, reason) in args.flags {
            session.accept(&Event::Flag { run, reason }, Durability::Synced)?;
            flagged.push(run);
        }
        let before = session.opened()?.lab.snapshot()?;
        let changed = match &session.workspace.repo {
            Some(repo) => repo.dirty_paths().await?,
            None => Vec::new(),
        };
        let deviated = match &before.config {
            Some(config) => git::deviations(&changed, &config.scope, &config.off_limits),
            None => Vec::new(),
        };
        let outcome = session.accept(
            &Event::Log {
                status: args.status,
                description: args.description.clone(),
                justification: args.justification,
                deviations: u32::try_from(deviated.len()).context("too many changed paths")?,
            },
            Durability::Synced,
        )?;
        let snapshot = session.opened()?.lab.snapshot()?;
        let row = before
            .pending
            .and_then(|id| snapshot.runs.iter().find(|row| row.id == id));
        let git = match (outcome.effect, &session.workspace.repo) {
            (Effect::Nothing, _) => Value::Null,
            (Effect::Commit | Effect::Reset, None) => {
                json!("not in a git repository: nothing committed or reset")
            }
            (Effect::Commit, Some(repo)) => {
                let name = snapshot
                    .config
                    .as_ref()
                    .map_or_else(String::new, |config| config.metric.clone());
                let value = row
                    .and_then(|row| row.metric.as_ref())
                    .map_or_else(|| "null".to_owned(), ToString::to_string);
                let message = format!(
                    "{}\n\nResult: {{\"status\":\"keep\",{}:{value}}}",
                    args.description,
                    serde_json::to_string(&name)?
                );
                outcome_of(repo.commit_all(&message).await)
            }
            (Effect::Reset, Some(repo)) if session.workspace.on_autoresearch_branch() => {
                outcome_of(repo.reset().await)
            }
            (Effect::Reset, Some(_)) => json!(
                "not on an autoresearch/* branch: the tree was not reset; revert the run's changes yourself"
            ),
        };
        Ok(Reply {
            value: json!({
                "run": row.map(row_json),
                "flagged": flagged,
                "deviations": deviated,
                "git": git,
                "stopped": outcome.stopped,
                "state": snapshot_json(&snapshot),
            }),
            mode: snapshot.mode,
            started: false,
        })
    }

    /// Flag run `run` as suspect (its result leaves baseline, best and
    /// confidence).
    ///
    /// # Errors
    ///
    /// [`super::Refused`], a store or core failure.
    pub(crate) async fn flag(&self, run: u32, reason: String) -> anyhow::Result<Reply> {
        let mut session = self.session().await?;
        session.accept(&Event::Flag { run, reason }, Durability::Synced)?;
        let snapshot = session.opened()?.lab.snapshot()?;
        Ok(Reply {
            value: json!({ "state": snapshot_json(&snapshot) }),
            mode: snapshot.mode,
            started: false,
        })
    }

    /// Replace the notes with `body`, and/or add `idea` to the ideas
    /// backlog; answer the notes.
    ///
    /// # Errors
    ///
    /// The notes cannot be read or written, a store or core failure.
    pub(crate) async fn notes(
        &self,
        body: Option<String>,
        idea: Option<String>,
    ) -> anyhow::Result<Reply> {
        let mut session = self.session().await?;
        let path = session.opened()?.store.notes_path();
        let mut notes = match body {
            Some(body) => body,
            None => read_notes(&path)?,
        };
        if let Some(idea) = idea {
            notes = add_idea(&notes, &idea);
        }
        write_notes(&path, &notes)?;
        let mode = session.opened()?.lab.snapshot()?.mode;
        Ok(Reply {
            value: json!({ "notes": notes }),
            mode,
            started: false,
        })
    }

    /// The session of the current branch: config, runs, baseline, best,
    /// confidence, pending run, mode, notes.
    ///
    /// # Errors
    ///
    /// A store or core failure.
    pub(crate) async fn state(&self) -> anyhow::Result<Reply> {
        let mut session = self.session().await?;
        let snapshot = session.opened()?.lab.snapshot()?;
        let opened = session.opened()?;
        let notes = read_notes(&opened.store.notes_path())?;
        let store = opened.store.dir().display().to_string();
        Ok(Reply {
            value: json!({
                "root": session.workspace.root.display().to_string(),
                "branch": session.workspace.branch,
                "harness": session.workspace.root.join(HARNESS).is_file(),
                "store": store,
                "notes": notes,
                "state": snapshot_json(&snapshot),
            }),
            mode: snapshot.mode,
            started: false,
        })
    }

    /// The Lab's snapshot of the current branch.
    ///
    /// # Errors
    ///
    /// A store or core failure.
    pub(crate) async fn snapshot(&self) -> anyhow::Result<Snapshot> {
        Ok(self.session().await?.opened()?.lab.snapshot()?)
    }

    /// Turn the mode on or off (`SetMode`).
    ///
    /// # Errors
    ///
    /// [`super::Refused`], a store or core failure.
    pub(crate) async fn set_mode(&self, mode: Mode) -> anyhow::Result<Reply> {
        let mut session = self.session().await?;
        session.accept(&Event::SetMode(mode), Durability::Synced)?;
        let snapshot = session.opened()?.lab.snapshot()?;
        Ok(Reply {
            value: json!({ "state": snapshot_json(&snapshot) }),
            mode: snapshot.mode,
            started: mode == Mode::On,
        })
    }

    /// `/autoresearch <goal>`: put the workspace on an `autoresearch/*`
    /// branch (from a clean tree) and turn the mode of its store on.
    ///
    /// # Errors
    ///
    /// A dirty tree off the branch, a git, store or core failure.
    pub(crate) async fn begin(&self, goal: &str) -> anyhow::Result<Begun> {
        let workspace = Workspace::of(&self.cwd).await?;
        let branch = ensure_branch(&workspace, Some(goal), &today()?).await?;
        let mut session = self.session().await?;
        session.accept(&Event::SetMode(Mode::On), Durability::Synced)?;
        let configured = session.opened()?.lab.snapshot()?.config.is_some();
        Ok(Begun { branch, configured })
    }

    /// `/autoresearch clear`: turn the mode off and close the session of
    /// the current branch. Its store moves aside to
    /// `<store>.cleared-<ms>` (kept, not deleted); the next init starts a
    /// new session. The tree and the branch stay as they are.
    ///
    /// # Errors
    ///
    /// A store, core or rename failure.
    pub(crate) async fn clear(&self) -> anyhow::Result<PathBuf> {
        let mut session = self.session().await?;
        session.accept(&Event::SetMode(Mode::Off), Durability::Synced)?;
        let dir = session.opened()?.store.dir().to_path_buf();
        *session.slot = None;
        let millis = SystemTime::now()
            .duration_since(SystemTime::UNIX_EPOCH)
            .map_or(0, |elapsed| elapsed.as_millis());
        let mut aside = dir.clone().into_os_string();
        aside.push(format!(".cleared-{millis}"));
        let aside = PathBuf::from(aside);
        std::fs::rename(&dir, &aside)
            .with_context(|| format!("could not move {} aside", dir.display()))?;
        Ok(aside)
    }
}

/// Today in the local time zone, `YYYYMMDD`.
fn today() -> anyhow::Result<String> {
    let now = crate::platform::local_time(SystemTime::now())?;
    Ok(format!("{:04}{:02}{:02}", now.year, now.month, now.day))
}

/// A git effect's note, or its failure (the event is logged either way).
fn outcome_of(result: anyhow::Result<String>) -> Value {
    match result {
        Ok(note) => json!(note),
        Err(error) => json!(format!("failed: {error:#}")),
    }
}

fn metric(value: Option<&Metric>) -> Value {
    value.map_or(Value::Null, |value| json!(value.to_string()))
}

fn status_name(status: Status) -> &'static str {
    match status {
        Status::Keep => "keep",
        Status::Discard => "discard",
        Status::Crash => "crash",
        Status::ChecksFailed => "checks_failed",
    }
}

fn direction_name(direction: Direction) -> &'static str {
    match direction {
        Direction::Lower => "lower",
        Direction::Higher => "higher",
    }
}

fn mode_name(mode: Mode) -> &'static str {
    match mode {
        Mode::On => "on",
        Mode::Off => "off",
    }
}

fn row_json(row: &RunRow) -> Value {
    json!({
        "id": row.id,
        "segment": row.segment,
        "status": row.status.map(status_name),
        "abandoned": row.abandoned,
        "finished": row.finished,
        "passed": row.passed,
        "flagged": row.flagged,
        "metric": metric(row.metric.as_ref()),
        "metrics": row
            .metrics
            .iter()
            .map(|(name, value)| json!([name, value.to_string()]))
            .collect::<Vec<_>>(),
        "description": row.description,
    })
}

fn config_json(config: &Config) -> Value {
    json!({
        "name": config.name,
        "goal": config.goal,
        "metric": config.metric,
        "unit": config.unit,
        "direction": direction_name(config.direction),
        "secondary": config.secondary,
        "scope": config.scope,
        "off_limits": config.off_limits,
        "max_iterations": config.max_iterations,
    })
}

fn snapshot_json(snapshot: &Snapshot) -> Value {
    let segment: Vec<&RunRow> = snapshot
        .runs
        .iter()
        .filter(|row| row.segment == snapshot.segment)
        .collect();
    let shown = &segment[segment.len().saturating_sub(STATE_RUNS)..];
    json!({
        "config": snapshot.config.as_ref().map(config_json),
        "segment": snapshot.segment,
        "mode": mode_name(snapshot.mode),
        "pending": snapshot.pending,
        "baseline": metric(snapshot.baseline.as_ref()),
        "best": metric(snapshot.best.as_ref()),
        "logged": snapshot.logged_in_segment,
        "confidence_tenths": snapshot.confidence_tenths,
        "runs": shown.iter().map(|row| row_json(row)).collect::<Vec<_>>(),
        "runs_in_segment": segment.len(),
        "runs_total": snapshot.runs.len(),
    })
}

/// The last [`TAIL_LINES`] lines of `log`, at most [`TAIL_BYTES`].
fn tail(log: &Path) -> anyhow::Result<String> {
    let bytes = std::fs::read(log).with_context(|| format!("could not read {}", log.display()))?;
    let start = bytes.len().saturating_sub(TAIL_BYTES);
    let text = String::from_utf8_lossy(&bytes[start..]);
    let lines: Vec<&str> = text.lines().collect();
    Ok(lines[lines.len().saturating_sub(TAIL_LINES)..].join("\n"))
}

fn read_notes(path: &Path) -> anyhow::Result<String> {
    match std::fs::read_to_string(path) {
        Ok(notes) => Ok(notes),
        Err(error) if error.kind() == std::io::ErrorKind::NotFound => Ok(String::new()),
        Err(error) => Err(error).with_context(|| format!("could not read {}", path.display())),
    }
}

fn write_notes(path: &Path, notes: &str) -> anyhow::Result<()> {
    std::fs::write(path, notes).with_context(|| format!("could not write {}", path.display()))
}

fn bullets(items: &[String]) -> String {
    items.iter().fold(String::new(), |mut out, item| {
        out.push_str("- ");
        out.push_str(item);
        out.push('\n');
        out
    })
}

/// `notes` with `idea` added as the last bullet of the `## Ideas`
/// section (made at the end when missing).
fn add_idea(notes: &str, idea: &str) -> String {
    let current = section(notes, IDEAS).unwrap_or_default();
    set_section(notes, IDEAS, &format!("{current}- {}\n", idea.trim()))
}

/// The body of section `heading` of `notes` (up to the next `## `
/// heading); `None` when it has none.
fn section(notes: &str, heading: &str) -> Option<String> {
    let (start, end) = section_bounds(notes, heading)?;
    let body = &notes[start..end];
    Some(
        body.strip_prefix(heading)?
            .trim_start_matches('\n')
            .to_owned(),
    )
}

/// `notes` with the body of section `heading` replaced by `body` (the
/// section added at the end when missing).
fn set_section(notes: &str, heading: &str, body: &str) -> String {
    let block = format!("{heading}\n\n{body}");
    match section_bounds(notes, heading) {
        Some((start, end)) => {
            let rest = &notes[end..];
            let gap = if rest.is_empty() { "" } else { "\n" };
            format!("{}{block}{gap}{rest}", &notes[..start])
        }
        None if notes.trim().is_empty() => block,
        None => format!("{}\n\n{block}", notes.trim_end()),
    }
}

/// Where section `heading` starts (its heading line) and ends (the next
/// `## ` heading line, or the end).
fn section_bounds(notes: &str, heading: &str) -> Option<(usize, usize)> {
    let mut offset = 0;
    let mut start = None;
    for line in notes.split_inclusive('\n') {
        let title = line.trim_end();
        match start {
            None if title == heading => start = Some(offset),
            Some(begin) if title.starts_with("## ") => return Some((begin, offset)),
            Some(_) | None => {}
        }
        offset += line.len();
    }
    start.map(|begin| (begin, notes.len()))
}

#[cfg(test)]
mod tests {
    use super::{add_idea, set_section, CONSTRAINTS};

    #[test]
    fn ideas_append_under_their_heading() {
        let notes = add_idea("# Plan\n\nmeasure first\n", "unroll the loop");
        assert_eq!(
            notes,
            "# Plan\n\nmeasure first\n\n## Ideas\n\n- unroll the loop\n"
        );
        assert_eq!(
            add_idea(&notes, "cache the table"),
            "# Plan\n\nmeasure first\n\n## Ideas\n\n- unroll the loop\n- cache the table\n"
        );
    }

    #[test]
    fn a_section_is_replaced_in_place() {
        let notes = "## Constraints\n\n- old\n\n## Ideas\n\n- x\n";
        assert_eq!(
            set_section(notes, CONSTRAINTS, "- new\n"),
            "## Constraints\n\n- new\n\n## Ideas\n\n- x\n"
        );
    }
}
