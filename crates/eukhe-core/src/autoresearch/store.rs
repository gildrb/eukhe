//! The durable event log of one autoresearch session (one repository
//! branch): `~/.eukhe/autoresearch/<repo-key>/events.jsonl`, one accepted
//! Lab event per line, written before its effect runs. Opening the store
//! replays the log through a fresh Lab, so the state after a crash, a
//! restart or a context reset is the state the log holds. Run output goes
//! to `runs/NNNN/benchmark.log`, the notes to `notes.md`.

use std::fs::{self, File, OpenOptions};
use std::io::Write as _;
use std::path::{Path, PathBuf};

use anyhow::{bail, Context as _};
use eukhe_bend::rules::autoresearch::{Config, Direction, Event, Lab, Mode, Status};
use serde::{Deserialize, Serialize};

/// The log file in a store directory.
const EVENTS: &str = "events.jsonl";

/// The notes file in a store directory.
const NOTES: &str = "notes.md";

/// Whether an append waits for the disk.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Durability {
    /// fsync before the append returns: the event may have an effect.
    Synced,
    /// Written, synced with the next [`Durability::Synced`] append: a
    /// run's output line, which has no effect.
    Buffered,
}

/// The store of one repository branch.
#[derive(Debug)]
pub(crate) struct Store {
    dir: PathBuf,
    log: Option<File>,
    /// The bytes of the log this store wrote or replayed.
    seen: u64,
}

impl Store {
    /// The store directory of `root` on `branch` under `home`
    /// (`~/.eukhe/autoresearch`): the root path with every `/` replaced
    /// by `-`, then `--<branch>` (`/` in it also `-`; `HEAD` when
    /// detached, `nogit` without git).
    pub(crate) fn dir_of(home: &Path, root: &Path, branch: Option<&str>, git: bool) -> PathBuf {
        let root = root.to_string_lossy().replace('/', "-");
        let branch = match (git, branch) {
            (false, _) => "nogit".to_owned(),
            (true, None) => "HEAD".to_owned(),
            (true, Some(branch)) => branch.replace('/', "-"),
        };
        home.join(format!("{root}--{branch}"))
    }

    /// Open the store in `dir` and replay its log through a fresh Lab. A
    /// last line cut short by a crash (no newline) never reached the disk
    /// whole, so its effect never ran: it is dropped from the file.
    ///
    /// # Errors
    ///
    /// The directory or log cannot be read or created, a line does not
    /// decode, or the Lab refuses a logged event (the log is corrupt).
    pub(crate) fn open(dir: PathBuf) -> anyhow::Result<(Store, Lab)> {
        fs::create_dir_all(&dir).with_context(|| format!("could not create {}", dir.display()))?;
        let path = dir.join(EVENTS);
        let text = match fs::read(&path) {
            Ok(bytes) => bytes,
            Err(error) if error.kind() == std::io::ErrorKind::NotFound => Vec::new(),
            Err(error) => {
                return Err(error).with_context(|| format!("could not read {}", path.display()))
            }
        };
        let whole = text
            .iter()
            .rposition(|byte| *byte == b'\n')
            .map_or(0, |end| end + 1);
        let mut lab = Lab::open()?;
        let body = std::str::from_utf8(&text[..whole])
            .with_context(|| format!("{} is not UTF-8", path.display()))?;
        for (index, line) in body.lines().enumerate() {
            let stored: Stored = serde_json::from_str(line)
                .with_context(|| format!("{} line {}", path.display(), index + 1))?;
            if let Err(refusal) = lab.step(&stored.into_event())? {
                bail!(
                    "{} line {}: the Lab refuses the logged event: {}",
                    path.display(),
                    index + 1,
                    refusal.text
                );
            }
        }
        if whole < text.len() {
            let file = OpenOptions::new()
                .write(true)
                .open(&path)
                .with_context(|| format!("could not open {}", path.display()))?;
            file.set_len(whole as u64)?;
            file.sync_all()?;
        }
        let store = Store {
            dir,
            log: None,
            seen: whole as u64,
        };
        Ok((store, lab))
    }

    /// The store directory.
    pub(crate) fn dir(&self) -> &Path {
        &self.dir
    }

    /// Whether the log on disk is the one this store holds (another
    /// process appended when it is not).
    pub(crate) fn current(&self) -> bool {
        fs::metadata(self.dir.join(EVENTS)).map_or(0, |meta| meta.len()) == self.seen
    }

    /// Append `event` (accepted by the Lab) to the log.
    ///
    /// # Errors
    ///
    /// The write or the sync fails.
    pub(crate) fn append(&mut self, event: &Event, durability: Durability) -> anyhow::Result<()> {
        let mut line = serde_json::to_string(&Stored::of(event))?;
        line.push('\n');
        let path = self.dir.join(EVENTS);
        let log = match &mut self.log {
            Some(log) => log,
            None => self.log.insert(
                OpenOptions::new()
                    .create(true)
                    .append(true)
                    .open(&path)
                    .with_context(|| format!("could not open {}", path.display()))?,
            ),
        };
        log.write_all(line.as_bytes())
            .with_context(|| format!("could not append to {}", path.display()))?;
        if durability == Durability::Synced {
            log.sync_data()
                .with_context(|| format!("could not sync {}", path.display()))?;
        }
        self.seen += line.len() as u64;
        Ok(())
    }

    /// The output directory of run `run` (`runs/NNNN`), created.
    ///
    /// # Errors
    ///
    /// The directory cannot be created.
    pub(crate) fn run_dir(&self, run: u32) -> anyhow::Result<PathBuf> {
        let dir = self.dir.join("runs").join(format!("{run:04}"));
        fs::create_dir_all(&dir).with_context(|| format!("could not create {}", dir.display()))?;
        Ok(dir)
    }

    /// The notes file.
    pub(crate) fn notes_path(&self) -> PathBuf {
        self.dir.join(NOTES)
    }
}

/// One logged event: the JSON form of a Lab [`Event`].
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "event", rename_all = "snake_case")]
enum Stored {
    Init {
        config: StoredConfig,
        new_segment: bool,
        harness: bool,
    },
    Start {
        run: u32,
    },
    Line {
        text: String,
    },
    Finish {
        exit_code: i32,
        timed_out: bool,
    },
    Log {
        status: StoredStatus,
        description: String,
        justification: Option<String>,
        deviations: u32,
    },
    Flag {
        run: u32,
        reason: String,
    },
    Mode {
        on: bool,
    },
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
struct StoredConfig {
    name: String,
    goal: String,
    metric: String,
    unit: String,
    higher_is_better: bool,
    secondary: Vec<String>,
    scope: Vec<String>,
    off_limits: Vec<String>,
    max_iterations: Option<u32>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
enum StoredStatus {
    Keep,
    Discard,
    Crash,
    ChecksFailed,
}

impl Stored {
    fn of(event: &Event) -> Self {
        match event {
            Event::Init {
                config,
                new_segment,
                harness,
            } => Self::Init {
                config: StoredConfig {
                    name: config.name.clone(),
                    goal: config.goal.clone(),
                    metric: config.metric.clone(),
                    unit: config.unit.clone(),
                    higher_is_better: match config.direction {
                        Direction::Lower => false,
                        Direction::Higher => true,
                    },
                    secondary: config.secondary.clone(),
                    scope: config.scope.clone(),
                    off_limits: config.off_limits.clone(),
                    max_iterations: config.max_iterations,
                },
                new_segment: *new_segment,
                harness: *harness,
            },
            Event::Start { run } => Self::Start { run: *run },
            Event::Line { text } => Self::Line { text: text.clone() },
            Event::Finish {
                exit_code,
                timed_out,
            } => Self::Finish {
                exit_code: *exit_code,
                timed_out: *timed_out,
            },
            Event::Log {
                status,
                description,
                justification,
                deviations,
            } => Self::Log {
                status: match status {
                    Status::Keep => StoredStatus::Keep,
                    Status::Discard => StoredStatus::Discard,
                    Status::Crash => StoredStatus::Crash,
                    Status::ChecksFailed => StoredStatus::ChecksFailed,
                },
                description: description.clone(),
                justification: justification.clone(),
                deviations: *deviations,
            },
            Event::Flag { run, reason } => Self::Flag {
                run: *run,
                reason: reason.clone(),
            },
            Event::SetMode(mode) => Self::Mode {
                on: match mode {
                    Mode::On => true,
                    Mode::Off => false,
                },
            },
        }
    }

    fn into_event(self) -> Event {
        match self {
            Self::Init {
                config,
                new_segment,
                harness,
            } => Event::Init {
                config: Config {
                    name: config.name,
                    goal: config.goal,
                    metric: config.metric,
                    unit: config.unit,
                    direction: if config.higher_is_better {
                        Direction::Higher
                    } else {
                        Direction::Lower
                    },
                    secondary: config.secondary,
                    scope: config.scope,
                    off_limits: config.off_limits,
                    max_iterations: config.max_iterations,
                },
                new_segment,
                harness,
            },
            Self::Start { run } => Event::Start { run },
            Self::Line { text } => Event::Line { text },
            Self::Finish {
                exit_code,
                timed_out,
            } => Event::Finish {
                exit_code,
                timed_out,
            },
            Self::Log {
                status,
                description,
                justification,
                deviations,
            } => Event::Log {
                status: match status {
                    StoredStatus::Keep => Status::Keep,
                    StoredStatus::Discard => Status::Discard,
                    StoredStatus::Crash => Status::Crash,
                    StoredStatus::ChecksFailed => Status::ChecksFailed,
                },
                description,
                justification,
                deviations,
            },
            Self::Flag { run, reason } => Event::Flag { run, reason },
            Self::Mode { on } => Event::SetMode(if on { Mode::On } else { Mode::Off }),
        }
    }
}
