use std::collections::VecDeque;
use std::os::unix::fs::PermissionsExt as _;
use std::time::Duration;

use eukhe_types::path_policy::PathRule;
use parking_lot::Mutex;
use ShellEffect::{Exec, Net, Outside, Protected, Read, Secret, Write};

use super::*;

/// Answers the gated steps in order from a list (none left: no answer)
/// and keeps every question.
struct Scripted {
    answers: Mutex<VecDeque<Answer>>,
    asked: Mutex<Vec<Ask>>,
}

impl Scripted {
    fn new(answers: impl IntoIterator<Item = Answer>) -> Self {
        Self {
            answers: Mutex::new(answers.into_iter().collect()),
            asked: Mutex::new(Vec::new()),
        }
    }
}

impl Approver for Scripted {
    fn approve(&self, ask: Ask) -> impl Future<Output = Answer> + Send {
        self.asked.lock().push(ask);
        let answer = self.answers.lock().pop_front();
        std::future::ready(answer.unwrap_or(Answer::Unanswered))
    }
}

/// What the sink saw of one step.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
struct Streamed {
    command: String,
    stdout: String,
    stderr: String,
    status: Option<i32>,
}

/// Keeps every step's output, by step.
#[derive(Default)]
struct Record(Mutex<BTreeMap<u64, Streamed>>);

impl Sink for Record {
    fn begin(&self, step: u64, command: &str) {
        self.0.lock().entry(step).or_default().command = command.to_string();
    }

    fn output(&self, step: u64, stream: Stream, bytes: &[u8]) {
        let mut seen = self.0.lock();
        let streamed = seen.entry(step).or_default();
        let text = String::from_utf8_lossy(bytes);
        match stream {
            Stream::Stdout => streamed.stdout.push_str(&text),
            Stream::Stderr => streamed.stderr.push_str(&text),
        }
    }

    fn end(&self, step: u64, status: i32) {
        self.0.lock().entry(step).or_default().status = Some(status);
    }
}

/// One step that ran, with the output the sink saw of it.
#[derive(Debug, Clone, PartialEq, Eq)]
struct Seen {
    run: StepRun,
    stdout: String,
    stderr: String,
}

/// The steps that ran with their output; every step began and ended in
/// the sink with its command and status.
fn seen(ran: &Ran, record: &Record) -> Vec<Seen> {
    let streamed = record.0.lock();
    ran.steps
        .iter()
        .map(|run| {
            let got = streamed.get(&run.step).cloned().unwrap_or_default();
            assert_eq!(
                (got.command.as_str(), got.status),
                (run.command.as_str(), Some(run.status)),
                "the sink's begin and end of step {}",
                run.step
            );
            Seen {
                run: run.clone(),
                stdout: got.stdout,
                stderr: got.stderr,
            }
        })
        .collect()
}

/// A work dir with a `bin` of stand-in programs (`curl`, `tool`) that
/// print their arguments; the shell's `PATH` is that `bin`, then the
/// system's. The workspace is `work`; `guard` is protected, `keys` a
/// secret (both outside `work`).
struct Bench {
    dir: tempfile::TempDir,
}

impl Bench {
    fn new() -> Self {
        let dir = tempfile::tempdir().unwrap();
        let bin = dir.path().join("bin");
        std::fs::create_dir(&bin).unwrap();
        for name in ["curl", "tool"] {
            let path = bin.join(name);
            std::fs::write(&path, format!("#!/bin/sh\necho {name} \"$@\"\n")).unwrap();
            std::fs::set_permissions(&path, std::fs::Permissions::from_mode(0o755)).unwrap();
        }
        for sub in ["work", "guard", "keys"] {
            std::fs::create_dir(dir.path().join(sub)).unwrap();
        }
        std::fs::write(dir.path().join("keys/id"), "secret\n").unwrap();
        Self { dir }
    }

    fn work(&self) -> PathBuf {
        self.dir.path().join("work")
    }

    fn paths(&self) -> PathPolicy {
        PathPolicy::new(
            vec![self.work()],
            vec![PathRule::Tree(self.dir.path().join("guard"))],
            vec![self.dir.path().join("keys")],
        )
    }

    fn shell(&self) -> Shell {
        self.shell_at(self.work())
    }

    /// A shell whose working directory is `cwd`.
    fn shell_at(&self, cwd: PathBuf) -> Shell {
        let path = format!("{}:/usr/bin:/bin", self.dir.path().join("bin").display());
        Shell::new(
            cwd,
            [
                ("PATH".to_string(), path),
                ("HOME".to_string(), self.dir.path().display().to_string()),
            ],
            "bash",
        )
    }
}

fn ran(
    step: u64,
    command: &str,
    effects: &[ShellEffect],
    approval: Approval,
    stdout: &str,
    status: i32,
) -> Seen {
    Seen {
        run: StepRun {
            step,
            command: command.to_string(),
            effects: ShellEffects::of(effects),
            approval,
            status,
        },
        stdout: stdout.to_string(),
        stderr: String::new(),
    }
}

#[tokio::test]
async fn approved_steps_run_and_a_denial_stops_the_script() {
    let bench = Bench::new();
    std::fs::write(bench.work().join("notes"), "one\ntwo\n").unwrap();
    let approver = Scripted::new([Answer::Approve, Answer::Deny]);
    let record = Record::default();
    let mut shell = bench.shell();
    let got = shell
        .run(
            "cat notes | grep -c o\necho made > out.txt && cat out.txt\ncurl https://example.com\ntouch never",
            AutoSet::new([Read]),
            &bench.paths(),
            &approver,
            &record,
        )
        .await;
    assert_eq!(
        (seen(&got, &record), got.end),
        (
            vec![
                ran(0, "cat notes", &[Read], Approval::Auto, "", 0),
                ran(1, "grep -c o", &[Read], Approval::Auto, "2\n", 0),
                ran(
                    2,
                    "echo made >out.txt",
                    &[Read, Write],
                    Approval::Approved,
                    "",
                    0
                ),
                ran(3, "cat out.txt", &[Read], Approval::Auto, "made\n", 0),
            ],
            End::Refused {
                step: 4,
                command: "curl https://example.com".to_string(),
                effects: ShellEffects::of(&[Net]),
                refusal: Refusal::Denied,
            },
        )
    );
    assert_eq!(
        *approver.asked.lock(),
        vec![
            Ask {
                step: 2,
                command: "echo made >out.txt".to_string(),
                effects: ShellEffects::of(&[Read, Write]),
            },
            Ask {
                step: 4,
                command: "curl https://example.com".to_string(),
                effects: ShellEffects::of(&[Net]),
            },
        ]
    );
    assert!(!bench.work().join("never").exists());
}

#[tokio::test]
async fn shell_state_chains_and_external_programs() {
    let bench = Bench::new();
    std::fs::create_dir(bench.work().join("sub")).unwrap();
    let approver = Scripted::new([]);
    let record = Record::default();
    let mut shell = bench.shell();
    let got = shell
        .run(
            "cd sub; export WHO=me; X=1; false || echo \"$WHO $X $?\"; tool a 'b c' 2>&1; missing-program; exit 3; echo after",
            AutoSet::new([Read, Exec]),
            &bench.paths(),
            &approver,
            &record,
        )
        .await;
    assert_eq!(
        (seen(&got, &record), got.end),
        (
            vec![
                ran(0, "cd sub", &[Read], Approval::Auto, "", 0),
                ran(1, "export WHO=me", &[Exec], Approval::Auto, "", 0),
                ran(2, "X=1", &[Exec], Approval::Auto, "", 0),
                ran(3, "false", &[Read], Approval::Auto, "", 1),
                ran(4, "echo 'me 1 1'", &[Read], Approval::Auto, "me 1 1\n", 0),
                ran(
                    5,
                    "tool a 'b c' 2>&1",
                    &[Exec],
                    Approval::Auto,
                    "tool a b c\n",
                    0
                ),
                Seen {
                    stderr: "eukhe-shell: missing-program: command not found\n".to_string(),
                    ..ran(6, "missing-program", &[Exec], Approval::Auto, "", 127)
                },
                ran(7, "exit 3", &[Read], Approval::Auto, "", 3),
            ],
            End::Exited { status: 3 },
        )
    );
    assert_eq!(
        shell.cwd(),
        std::fs::canonicalize(bench.work().join("sub")).unwrap()
    );
}

#[tokio::test]
async fn a_script_outside_the_grammar_is_one_step_with_every_effect_it_holds() {
    let bench = Bench::new();
    let script = "for f in a b; do echo $f; done";
    let unanswered = bench
        .shell()
        .run(
            script,
            AutoSet::new([Read]),
            &bench.paths(),
            &Scripted::new([]),
            &Record::default(),
        )
        .await;
    let command = format!("bash -c '{script}'");
    assert_eq!(
        unanswered,
        Ran {
            steps: Vec::new(),
            end: End::Refused {
                step: 0,
                command: command.clone(),
                effects: ShellEffects::of(&[Read, Exec]),
                refusal: Refusal::Unanswered,
            },
        }
    );
    let record = Record::default();
    let approved = bench
        .shell()
        .run(
            script,
            AutoSet::new([Read]),
            &bench.paths(),
            &Scripted::new([Answer::Approve]),
            &record,
        )
        .await;
    assert_eq!(
        (seen(&approved, &record), approved.end),
        (
            vec![ran(
                0,
                &command,
                &[Read, Exec],
                Approval::Approved,
                "a\nb\n",
                0
            )],
            End::Finished { status: 0 },
        )
    );
}

/// Regression: the commands of a pipeline run together, so a command
/// that stops reading ends the endless one before it. `yes` dies of
/// SIGPIPE (141); the own `cat` between them ends with the same status
/// when its output pipe closes.
#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn a_pipeline_ends_when_its_last_command_stops_reading() {
    let bench = Bench::new();
    let auto = AutoSet::new([Read]);
    let paths = bench.paths();
    let record = Record::default();
    let got = tokio::time::timeout(
        Duration::from_secs(10),
        bench
            .shell()
            .run("yes | head -n 3", auto, &paths, &Scripted::new([]), &record),
    )
    .await
    .expect("`yes | head -n 3` ends");
    assert_eq!(
        (seen(&got, &record), got.end),
        (
            vec![
                ran(0, "yes", &[Read], Approval::Auto, "", 141),
                ran(1, "head -n 3", &[Read], Approval::Auto, "y\ny\ny\n", 0),
            ],
            End::Finished { status: 0 },
        )
    );
    let record = Record::default();
    let got = tokio::time::timeout(
        Duration::from_secs(10),
        bench.shell().run(
            "yes | cat | head -n 2",
            auto,
            &paths,
            &Scripted::new([]),
            &record,
        ),
    )
    .await
    .expect("`yes | cat | head -n 2` ends");
    assert_eq!(
        (seen(&got, &record), got.end),
        (
            vec![
                ran(0, "yes", &[Read], Approval::Auto, "", 141),
                ran(1, "cat", &[Read], Approval::Auto, "", 141),
                ran(2, "head -n 2", &[Read], Approval::Auto, "y\ny\n", 0),
            ],
            End::Finished { status: 0 },
        )
    );
}

/// A refused command of a pipeline runs none of it: the commands are
/// gated in order before any runs, so the endless `yes` before the
/// refused `tool` never starts.
#[tokio::test]
async fn a_refused_command_runs_none_of_its_pipeline() {
    let bench = Bench::new();
    let approver = Scripted::new([Answer::Deny]);
    let got = bench
        .shell()
        .run(
            "echo first; yes | tool x",
            AutoSet::new([Read]),
            &bench.paths(),
            &approver,
            &Record::default(),
        )
        .await;
    assert_eq!(
        (got.steps.len(), got.end),
        (
            1,
            End::Refused {
                step: 2,
                command: "tool x".to_string(),
                effects: ShellEffects::of(&[Exec]),
                refusal: Refusal::Denied,
            }
        )
    );
}

/// Regression (audit H4, H2, M4): a step had one effect, so a write
/// redirection of a `Net` or `Exec` step, a write outside the workspace
/// or to a protected place, and a read of a secret ran with the auto set
/// of its main effect. The widest auto set still stops at the secret.
#[tokio::test]
async fn every_effect_of_a_step_must_be_allowed() {
    let bench = Bench::new();
    let approver = Scripted::new([]);
    let got = bench
        .shell()
        .run(
            "curl x > got; touch ../out; touch ../guard/g; cat ../keys/id; cp ../keys/id copy",
            AutoSet::new(ShellEffect::ALL),
            &bench.paths(),
            &approver,
            &Record::default(),
        )
        .await;
    assert_eq!(
        (got.steps.len(), got.end),
        (
            3,
            End::Refused {
                step: 3,
                command: "cat ../keys/id".to_string(),
                effects: ShellEffects::of(&[Read, Secret]),
                refusal: Refusal::Unanswered,
            }
        )
    );
    let asked = Scripted::new([Answer::Approve; 4]);
    let got = bench
        .shell()
        .run(
            "curl x > got; touch ../out; touch ../guard/g; cat ../keys/id; cp ../keys/id copy",
            AutoSet::new([Read, Net]),
            &bench.paths(),
            &asked,
            &Record::default(),
        )
        .await;
    let effects: Vec<ShellEffects> = asked.asked.lock().iter().map(|ask| ask.effects).collect();
    assert_eq!(
        (effects, got.end),
        (
            vec![
                ShellEffects::of(&[Write, Net]),
                ShellEffects::of(&[Write, Outside]),
                ShellEffects::of(&[Write, Protected]),
                ShellEffects::of(&[Read, Secret]),
                ShellEffects::of(&[Write, Secret]),
            ],
            End::Refused {
                step: 4,
                command: "cp ../keys/id copy".to_string(),
                effects: ShellEffects::of(&[Write, Secret]),
                refusal: Refusal::Unanswered,
            }
        )
    );
}

/// Regression: every step run in a working directory that held a secret
/// (the home dir) had `Secret`, so `echo hi`, `date` and `git -C repo
/// log` there always asked. Only a step that reads the directory because
/// it names no path of its own (`ls`, `rg x`, `grep -r x`, `find -name
/// x`, `du`) reads the secret in it.
#[tokio::test]
async fn only_a_step_that_reads_its_working_directory_reads_a_secret_in_it() {
    let bench = Bench::new();
    let asked = Scripted::new([Answer::Approve; 5]);
    let got = bench
        .shell_at(bench.dir.path().to_path_buf())
        .run(
            "echo hi; date; git -C work log; ls work; rg x work; ls; rg x; grep -r x; find -name x; du",
            AutoSet::new([Read]),
            &bench.paths(),
            &asked,
            &Record::default(),
        )
        .await;
    let asked: Vec<(u64, ShellEffects)> = asked
        .asked
        .lock()
        .iter()
        .map(|ask| (ask.step, ask.effects))
        .collect();
    assert_eq!(
        (asked, got.steps.len()),
        (
            (5..10)
                .map(|step| (step, ShellEffects::of(&[Read, Secret])))
                .collect(),
            10
        )
    );
}
