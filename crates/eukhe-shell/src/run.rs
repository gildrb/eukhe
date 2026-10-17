//! The interpreter: runs a script step by step through the approval gate
//! (the model's `exec`, bend/tools.bend part 4).
//!
//! A pipeline's commands run together, joined by OS pipes (bounded by the
//! kernel's pipe buffer): an external command is a child process in its
//! own process group, an own coreutil runs on a blocking thread. A command
//! that ends closes its input, so the command that writes to it ends too
//! (SIGPIPE for a program, status 141 for an own coreutil): `yes | head`
//! ends. What reaches the script's stdout and stderr streams to the
//! [`Sink`] as it is written; the shell keeps none of it.

use std::collections::{BTreeMap, BTreeSet};
use std::fs::File;
use std::future::Future;
use std::io::{Read, Write as _};
use std::os::fd::OwnedFd;
use std::path::{Path, PathBuf};
use std::process::Stdio;

use eukhe_types::shell::ShellEffect;
use tokio::io::AsyncReadExt as _;
use tokio::sync::mpsc;
use tokio::task::JoinSet;

use crate::coreutils::{self, Io};
use crate::effect::classify;
use crate::expand::Scope;
use crate::parse::{self, Link, Pipeline, RedirectOp};

/// The effects whose steps run without asking.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct AutoSet(BTreeSet<ShellEffect>);

impl AutoSet {
    pub fn new(effects: impl IntoIterator<Item = ShellEffect>) -> Self {
        Self(effects.into_iter().collect())
    }

    #[must_use]
    pub fn contains(&self, effect: ShellEffect) -> bool {
        self.0.contains(&effect)
    }
}

/// The question about one gated step.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Ask {
    /// The step's place in the script, from 0, in the order steps run.
    pub step: u64,
    /// The step as it will run, after expansion.
    pub command: String,
    pub effect: ShellEffect,
}

/// The user's answer to one [`Ask`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Answer {
    Approve,
    Deny,
    /// No one answered: a denial.
    Unanswered,
}

/// Asks the user whether a gated step may run.
///
/// Implementations ask whoever can answer (the attached client) and
/// resolve when the answer arrives; with no one to ask they resolve
/// [`Answer::Unanswered`] at once. The shell asks once per gated step, in
/// step order, and waits for each answer before it runs anything else.
pub trait Approver: Sync {
    fn approve(&self, ask: Ask) -> impl Future<Output = Answer> + Send;
}

/// Which of the script's streams a chunk of output went to.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Stream {
    Stdout,
    Stderr,
}

/// Where a script's output goes while it runs. Each step that passed the
/// gate begins; then the bytes it writes to the script's stdout and
/// stderr arrive as it writes them (the steps of a pipeline run together,
/// so their chunks interleave; output piped or redirected elsewhere does
/// not arrive); then it ends with its status.
pub trait Sink: Sync {
    fn begin(&self, step: u64, command: &str);
    fn output(&self, step: u64, stream: Stream, bytes: &[u8]);
    fn end(&self, step: u64, status: i32);
}

/// Why a step ran.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Approval {
    /// Its effect is in the auto set.
    Auto,
    /// The user approved it.
    Approved,
}

/// One step that ran and its exit status (its output went to the
/// [`Sink`]).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct StepRun {
    pub step: u64,
    pub command: String,
    pub effect: ShellEffect,
    pub approval: Approval,
    pub status: i32,
}

/// Why a gated step did not run.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Refusal {
    Denied,
    Unanswered,
}

/// How a script ended.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum End {
    /// No step was refused; `status` is the last step's.
    Finished { status: i32 },
    /// A step ran `exit`.
    Exited { status: i32 },
    /// The user did not approve this step: it, every later step, and the
    /// other steps of its pipeline did not run.
    Refused {
        step: u64,
        command: String,
        effect: ShellEffect,
        refusal: Refusal,
    },
}

/// How a script ran: the steps that ran, in order, and how it ended.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Ran {
    pub steps: Vec<StepRun>,
    pub end: End,
}

/// Whether a command is a pipeline by itself: only then do its shell
/// state changes (`cd`, `export`, assignments, `exit`) apply, as in bash.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Place {
    Alone,
    Piped,
}

/// One command of a pipeline, expanded and classified.
struct Planned {
    step: u64,
    argv: Vec<String>,
    assigns: Vec<(String, String)>,
    redirects: Vec<(u32, RedirectOp, String)>,
    /// The step as it will run, for people.
    command: String,
    effect: ShellEffect,
}

/// Where a command's fd 1 or fd 2 goes.
enum Target {
    /// The script's stdout or stderr: to the [`Sink`].
    Capture(Stream),
    /// A file or the next command's input pipe.
    Open(File),
}

impl Target {
    fn try_clone(&self) -> std::io::Result<Self> {
        match self {
            Target::Capture(stream) => Ok(Target::Capture(*stream)),
            Target::Open(file) => file.try_clone().map(Target::Open),
        }
    }
}

/// The streams of one command.
struct Wired {
    /// `None` reads as empty input.
    stdin: Option<File>,
    stdout: File,
    stderr: File,
}

/// A chunk a command wrote to the script's stdout or stderr.
struct Chunk {
    step: u64,
    stream: Stream,
    bytes: Vec<u8>,
}

/// An own coreutil's answer: its status, or its streams back for the
/// external program.
enum Builtin {
    Ran(i32),
    External(Wired),
}

/// Kills an external command's process group when the command is
/// dropped before it ended (a killed script), so every process it
/// started stops and the script's pipes close.
struct GroupKill(Option<i32>);

impl Drop for GroupKill {
    fn drop(&mut self) {
        if let Some(group) = self.0 {
            // A group already gone has nothing left to kill.
            let _ = nix::sys::signal::killpg(
                nix::unistd::Pid::from_raw(group),
                nix::sys::signal::Signal::SIGKILL,
            );
        }
    }
}

/// The state a script runs in: the working directory, the variables (the
/// exported ones are the environment of external programs), the last
/// exit status, and the external shell that runs scripts outside the
/// grammar.
#[derive(Debug, Clone)]
pub struct Shell {
    cwd: PathBuf,
    vars: BTreeMap<String, String>,
    exported: BTreeSet<String>,
    status: i32,
    external: PathBuf,
}

/// `text` quoted for a shell when it needs quotes.
fn quote(text: &str) -> String {
    let plain = !text.is_empty()
        && text
            .chars()
            .all(|c| c.is_ascii_alphanumeric() || "_./=:,+@%^-".contains(c));
    if plain {
        text.to_string()
    } else {
        format!("'{}'", text.replace('\'', "'\\''"))
    }
}

/// A pipe whose read end streams to the sink as `stream` of `step`; the
/// write end.
fn capture(
    step: u64,
    stream: Stream,
    chunks: &mpsc::Sender<Chunk>,
    readers: &mut JoinSet<()>,
) -> std::io::Result<File> {
    let (reader, writer) = std::io::pipe()?;
    let mut reader = tokio::net::unix::pipe::Receiver::from_owned_fd(OwnedFd::from(reader))?;
    let chunks = chunks.clone();
    readers.spawn(async move {
        let mut buffer = vec![0u8; 16 * 1024];
        loop {
            match reader.read(&mut buffer).await {
                Ok(0) => return,
                Ok(read) => {
                    let chunk = Chunk {
                        step,
                        stream,
                        bytes: buffer[..read].to_vec(),
                    };
                    if chunks.send(chunk).await.is_err() {
                        return;
                    }
                }
                Err(error) => {
                    tracing::debug!(%error, step, "reading a step's output failed");
                    return;
                }
            }
        }
    });
    Ok(File::from(OwnedFd::from(writer)))
}

impl Shell {
    /// A shell in `cwd` whose environment is `env` (every variable
    /// exported); `external` runs the scripts outside the grammar
    /// (`bash`).
    pub fn new(
        cwd: impl Into<PathBuf>,
        env: impl IntoIterator<Item = (String, String)>,
        external: impl Into<PathBuf>,
    ) -> Self {
        let vars: BTreeMap<String, String> = env.into_iter().collect();
        Self {
            cwd: cwd.into(),
            exported: vars.keys().cloned().collect(),
            vars,
            status: 0,
            external: external.into(),
        }
    }

    /// The working directory (`cd` changes it).
    #[must_use]
    pub fn cwd(&self) -> &Path {
        &self.cwd
    }

    /// Run `script`: each step whose effect is in `auto` runs, every
    /// other step runs only when `approver` approves it; the first step
    /// it does not approve ends the script. The output streams to `sink`.
    #[tracing::instrument(level = "debug", skip_all, fields(cwd = %self.cwd.display()))]
    pub async fn run(
        &mut self,
        script: &str,
        auto: &AutoSet,
        approver: &impl Approver,
        sink: &impl Sink,
    ) -> Ran {
        let mut steps = Vec::new();
        let list = match parse::parse(script) {
            Ok(list) => list,
            Err(unsupported) => {
                tracing::debug!(why = unsupported.0, "the script runs in the external shell");
                let argv = vec![
                    self.external.display().to_string(),
                    "-c".to_string(),
                    script.to_string(),
                ];
                let command = argv
                    .iter()
                    .map(|word| quote(word))
                    .collect::<Vec<_>>()
                    .join(" ");
                let whole = Planned {
                    step: 0,
                    argv,
                    assigns: Vec::new(),
                    redirects: Vec::new(),
                    command,
                    effect: ShellEffect::Exec,
                };
                let end = self
                    .pipeline(vec![whole], auto, approver, sink, &mut steps)
                    .await;
                return Ran {
                    steps,
                    end: end.unwrap_or(End::Finished {
                        status: self.status,
                    }),
                };
            }
        };
        for chain in &list {
            let planned = self.plan(&chain.first, steps.len() as u64);
            if let Some(end) = self
                .pipeline(planned, auto, approver, sink, &mut steps)
                .await
            {
                return Ran { steps, end };
            }
            for (link, pipeline) in &chain.rest {
                let runs = match link {
                    Link::And => self.status == 0,
                    Link::Or => self.status != 0,
                };
                if runs {
                    let planned = self.plan(pipeline, steps.len() as u64);
                    if let Some(end) = self
                        .pipeline(planned, auto, approver, sink, &mut steps)
                        .await
                    {
                        return Ran { steps, end };
                    }
                }
            }
        }
        Ran {
            steps,
            end: End::Finished {
                status: self.status,
            },
        }
    }

    /// Expand and classify a pipeline's commands, numbered from `first`.
    fn plan(&self, pipeline: &Pipeline, first: u64) -> Vec<Planned> {
        let scope = Scope {
            vars: &self.vars,
            status: self.status,
            cwd: &self.cwd,
        };
        let mut planned = Vec::with_capacity(pipeline.commands.len());
        for (step, command) in (first..).zip(&pipeline.commands) {
            let argv: Vec<String> = command.words.iter().flat_map(|w| scope.fields(w)).collect();
            let assigns: Vec<(String, String)> = command
                .assigns
                .iter()
                .map(|assign| (assign.name.clone(), scope.text(&assign.value)))
                .collect();
            let redirects: Vec<(u32, RedirectOp, String)> = command
                .redirects
                .iter()
                .map(|redirect| {
                    let target = match &redirect.op {
                        RedirectOp::Read(word)
                        | RedirectOp::Write(word)
                        | RedirectOp::Append(word) => scope.text(word),
                        RedirectOp::Dup(to) => to.to_string(),
                    };
                    (redirect.fd, redirect.op.clone(), target)
                })
                .collect();
            let mut effect = classify(&assigns, &argv);
            let writes_file = redirects.iter().any(|(_, op, target)| {
                matches!(op, RedirectOp::Write(_) | RedirectOp::Append(_)) && target != "/dev/null"
            });
            if effect == ShellEffect::Read && writes_file {
                effect = ShellEffect::Write;
            }
            let mut words: Vec<String> = assigns
                .iter()
                .map(|(name, value)| format!("{name}={}", quote(value)))
                .chain(argv.iter().map(|word| quote(word)))
                .collect();
            for (fd, op, target) in &redirects {
                let (default, sign) = match op {
                    RedirectOp::Read(_) => (0, "<"),
                    RedirectOp::Write(_) => (1, ">"),
                    RedirectOp::Append(_) => (1, ">>"),
                    RedirectOp::Dup(_) => (1, ">&"),
                };
                let prefix = if *fd == default {
                    String::new()
                } else {
                    fd.to_string()
                };
                let target = match op {
                    RedirectOp::Dup(_) => target.clone(),
                    RedirectOp::Read(_) | RedirectOp::Write(_) | RedirectOp::Append(_) => {
                        quote(target)
                    }
                };
                words.push(format!("{prefix}{sign}{target}"));
            }
            planned.push(Planned {
                step,
                argv,
                assigns,
                redirects,
                command: words.join(" "),
                effect,
            });
        }
        planned
    }

    /// Gate a pipeline's commands in order, then run them together; `Some`
    /// when the script ends here. A refused command runs no command of
    /// its pipeline.
    async fn pipeline(
        &mut self,
        planned: Vec<Planned>,
        auto: &AutoSet,
        approver: &impl Approver,
        sink: &impl Sink,
        steps: &mut Vec<StepRun>,
    ) -> Option<End> {
        let mut approvals = Vec::with_capacity(planned.len());
        for stage in &planned {
            let approval = if auto.contains(stage.effect) {
                Approval::Auto
            } else {
                let ask = Ask {
                    step: stage.step,
                    command: stage.command.clone(),
                    effect: stage.effect,
                };
                match approver.approve(ask).await {
                    Answer::Approve => Approval::Approved,
                    refused @ (Answer::Deny | Answer::Unanswered) => {
                        return Some(End::Refused {
                            step: stage.step,
                            command: stage.command.clone(),
                            effect: stage.effect,
                            refusal: match refused {
                                Answer::Unanswered => Refusal::Unanswered,
                                Answer::Approve | Answer::Deny => Refusal::Denied,
                            },
                        });
                    }
                }
            };
            approvals.push(approval);
        }
        let place = if planned.len() == 1 {
            Place::Alone
        } else {
            Place::Piped
        };
        for stage in &planned {
            sink.begin(stage.step, &stage.command);
        }
        let statuses = self.launch(&planned, place, sink).await;
        for ((stage, approval), status) in planned.into_iter().zip(approvals).zip(statuses) {
            sink.end(stage.step, status);
            self.status = status;
            let exits = place == Place::Alone && stage.argv.first().is_some_and(|n| n == "exit");
            steps.push(StepRun {
                step: stage.step,
                command: stage.command,
                effect: stage.effect,
                approval,
                status,
            });
            if exits {
                return Some(End::Exited { status });
            }
        }
        None
    }

    /// Run a pipeline's commands together, each one's stdout the next
    /// one's stdin, and stream what reaches the script's stdout and stderr
    /// to `sink`; each command's status, once every command ended and its
    /// output arrived.
    async fn launch(&mut self, planned: &[Planned], place: Place, sink: &impl Sink) -> Vec<i32> {
        let (chunks, mut arrived) = mpsc::channel::<Chunk>(16);
        let mut readers = JoinSet::new();
        let mut running = JoinSet::new();
        // A command whose task fails without a status failed.
        let mut statuses = vec![1; planned.len()];
        let env: Vec<(String, String)> = self
            .exported
            .iter()
            .filter_map(|key| self.vars.get(key).map(|value| (key.clone(), value.clone())))
            .collect();
        let mut next_stdin: Option<File> = None;
        for (at, stage) in planned.iter().enumerate() {
            let stdin = next_stdin.take();
            let wired = if at + 1 == planned.len() {
                Ok(Target::Capture(Stream::Stdout))
            } else {
                std::io::pipe().map(|(reader, writer)| {
                    next_stdin = Some(File::from(OwnedFd::from(reader)));
                    Target::Open(File::from(OwnedFd::from(writer)))
                })
            }
            .map_err(|error| format!("eukhe-shell: pipe: {error}\n"))
            .and_then(|stdout| self.wire(stage, stdin, stdout, &chunks, &mut readers));
            let mut wired = match wired {
                Ok(wired) => wired,
                Err(message) => {
                    sink.output(stage.step, Stream::Stderr, message.as_bytes());
                    continue;
                }
            };
            if let Some((status, message)) = self.state(&stage.argv, &stage.assigns, place) {
                // A closed stderr loses only the message.
                let _ = wired.stderr.write_all(message.as_bytes());
                statuses[at] = status;
                continue;
            }
            let argv = stage.argv.clone();
            let env: Vec<(String, String)> = env
                .iter()
                .cloned()
                .chain(stage.assigns.iter().cloned())
                .collect();
            let cwd = self.cwd.clone();
            running.spawn(async move { (at, command(argv, env, cwd, wired).await) });
        }
        drop(chunks);
        while let Some(chunk) = arrived.recv().await {
            sink.output(chunk.step, chunk.stream, &chunk.bytes);
        }
        while let Some(joined) = running.join_next().await {
            match joined {
                Ok((at, status)) => statuses[at] = status,
                Err(error) => tracing::warn!(%error, "a step's task failed"),
            }
        }
        statuses
    }

    /// The streams of `stage`: `stdin` (the pipe from the command before
    /// it), `stdout` (the pipe to the command after it, or the script's
    /// stdout), and the script's stderr, then its redirections in order.
    /// The error is the message of a redirection that could not open.
    fn wire(
        &self,
        stage: &Planned,
        stdin: Option<File>,
        stdout: Target,
        chunks: &mpsc::Sender<Chunk>,
        readers: &mut JoinSet<()>,
    ) -> Result<Wired, String> {
        let mut stdin = stdin;
        let mut fds = [stdout, Target::Capture(Stream::Stderr)];
        for (fd, op, target) in &stage.redirects {
            let path = self.cwd.join(target);
            let failed = |error: std::io::Error| format!("eukhe-shell: {target}: {error}\n");
            let slot = (*fd as usize).clamp(1, 2) - 1;
            match op {
                RedirectOp::Read(_) => stdin = Some(File::open(&path).map_err(failed)?),
                RedirectOp::Write(_) => {
                    fds[slot] = Target::Open(File::create(&path).map_err(failed)?);
                }
                RedirectOp::Append(_) => {
                    let file = std::fs::OpenOptions::new()
                        .create(true)
                        .append(true)
                        .open(&path)
                        .map_err(failed)?;
                    fds[slot] = Target::Open(file);
                }
                RedirectOp::Dup(to) => {
                    fds[slot] = match to {
                        0 => Target::Capture(Stream::Stdout),
                        to => fds[(*to as usize).min(2) - 1].try_clone().map_err(failed)?,
                    };
                }
            }
        }
        // One pipe per captured stream, shared by `2>&1`.
        let mut captured: [Option<File>; 2] = [None, None];
        let mut open = |target: Target| -> std::io::Result<File> {
            match target {
                Target::Open(file) => Ok(file),
                Target::Capture(stream) => {
                    let slot = match stream {
                        Stream::Stdout => 0,
                        Stream::Stderr => 1,
                    };
                    if let Some(file) = &captured[slot] {
                        return file.try_clone();
                    }
                    let file = capture(stage.step, stream, chunks, readers)?;
                    let opened = file.try_clone()?;
                    captured[slot] = Some(file);
                    Ok(opened)
                }
            }
        };
        let [fd1, fd2] = fds;
        let failed = |error: std::io::Error| format!("eukhe-shell: pipe: {error}\n");
        Ok(Wired {
            stdin,
            stdout: open(fd1).map_err(failed)?,
            stderr: open(fd2).map_err(failed)?,
        })
    }

    /// A shell state command (`cd`, `export`, `unset`, `exit`, or
    /// assignments alone): its status and error message. Its changes
    /// apply only to a command that is a pipeline by itself, as in bash.
    /// `None` for any other command.
    fn state(
        &mut self,
        argv: &[String],
        assigns: &[(String, String)],
        place: Place,
    ) -> Option<(i32, String)> {
        let Some((name, operands)) = argv.split_first() else {
            if place == Place::Alone {
                self.vars.extend(assigns.iter().cloned());
            }
            return Some((0, String::new()));
        };
        match name.as_str() {
            "cd" => {
                let target = match operands.first() {
                    Some(dir) => self.cwd.join(dir),
                    None => PathBuf::from(self.vars.get("HOME").cloned().unwrap_or_default()),
                };
                match std::fs::canonicalize(&target) {
                    Ok(dir) if dir.is_dir() => {
                        if place == Place::Alone {
                            self.cwd = dir;
                        }
                        Some((0, String::new()))
                    }
                    Ok(_) | Err(_) => {
                        let shown = operands.first().map_or("~", String::as_str);
                        Some((1, format!("cd: {shown}: No such directory\n")))
                    }
                }
            }
            "export" | "unset" => {
                if place == Place::Alone {
                    for arg in operands {
                        let (key, value) = match arg.split_once('=') {
                            Some((key, value)) => (key, Some(value)),
                            None => (arg.as_str(), None),
                        };
                        match (name.as_str(), value) {
                            ("export", Some(value)) => {
                                self.vars.insert(key.to_string(), value.to_string());
                                self.exported.insert(key.to_string());
                            }
                            ("export", None) => {
                                self.exported.insert(key.to_string());
                            }
                            (_, _) => {
                                self.vars.remove(key);
                                self.exported.remove(key);
                            }
                        }
                    }
                }
                Some((0, String::new()))
            }
            "exit" => {
                let status = match operands.first() {
                    Some(code) => code.parse().unwrap_or(2),
                    None => self.status,
                };
                Some((status, String::new()))
            }
            _ => None,
        }
    }
}

/// Run one command on its streams: the own coreutil, else the external
/// program in `cwd` with `env`. Its exit status.
#[tracing::instrument(level = "debug", skip_all, fields(program = %argv[0]))]
async fn command(argv: Vec<String>, env: Vec<(String, String)>, cwd: PathBuf, wired: Wired) -> i32 {
    let builtin = {
        let (argv, cwd) = (argv.clone(), cwd.clone());
        tokio::task::spawn_blocking(move || {
            let Wired {
                mut stdin,
                mut stdout,
                mut stderr,
            } = wired;
            let mut empty = std::io::empty();
            let input: &mut dyn Read = match &mut stdin {
                Some(file) => file,
                None => &mut empty,
            };
            let status = coreutils::run(
                &argv,
                &cwd,
                &mut Io {
                    stdin: input,
                    stdout: &mut stdout,
                    stderr: &mut stderr,
                },
            );
            // The streams close here when the coreutil ran: a reader
            // before it sees the closed pipe and ends.
            match status {
                Some(status) => Builtin::Ran(status),
                None => Builtin::External(Wired {
                    stdin,
                    stdout,
                    stderr,
                }),
            }
        })
        .await
    };
    let wired = match builtin {
        Ok(Builtin::Ran(status)) => return status,
        Ok(Builtin::External(wired)) => wired,
        Err(error) => {
            tracing::warn!(%error, "an own coreutil's thread failed");
            return 1;
        }
    };
    let program = &argv[0];
    // A relative path names a file under the shell's directory, not
    // under this process's.
    let path = if program.contains('/') {
        cwd.join(program)
    } else {
        PathBuf::from(program)
    };
    let Wired {
        stdin,
        stdout,
        stderr,
    } = wired;
    let mut report = stderr.try_clone();
    let spawned = {
        let mut command = tokio::process::Command::new(path);
        command
            .args(&argv[1..])
            .current_dir(&cwd)
            .env_clear()
            .envs(env)
            .stdin(stdin.map_or_else(Stdio::null, Stdio::from))
            .stdout(Stdio::from(stdout))
            .stderr(Stdio::from(stderr))
            .process_group(0)
            .kill_on_drop(true);
        // The command keeps the streams' descriptors until it drops.
        command.spawn()
    };
    let mut child = match spawned {
        Ok(child) => child,
        Err(error) => {
            let (message, status) = match error.kind() {
                std::io::ErrorKind::NotFound => ("command not found".to_string(), 127),
                std::io::ErrorKind::PermissionDenied => ("Permission denied".to_string(), 126),
                _ => (error.to_string(), 126),
            };
            if let Ok(report) = &mut report {
                // A closed stderr loses only the message.
                let _ = writeln!(report, "eukhe-shell: {program}: {message}");
            }
            return status;
        }
    };
    drop(report);
    let mut group = GroupKill(child.id().and_then(|pid| i32::try_from(pid).ok()));
    let waited = child.wait().await;
    // It ended: what it left running is no longer this step's.
    group.0 = None;
    match waited {
        Ok(status) => exit_status(status),
        Err(error) => {
            tracing::warn!(%error, %program, "waiting for a step failed");
            1
        }
    }
}

/// A child's exit status as a shell reports it: 128 + the signal that
/// killed it.
fn exit_status(status: std::process::ExitStatus) -> i32 {
    #[cfg(unix)]
    {
        use std::os::unix::process::ExitStatusExt as _;
        status
            .code()
            .or_else(|| status.signal().map(|signal| 128 + signal))
            .unwrap_or(1)
    }
    #[cfg(not(unix))]
    {
        status.code().unwrap_or(1)
    }
}

#[cfg(test)]
mod tests;
