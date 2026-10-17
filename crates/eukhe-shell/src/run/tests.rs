use std::collections::VecDeque;
use std::fmt::Write as _;
use std::os::unix::fs::PermissionsExt as _;
use std::time::Duration;

use parking_lot::Mutex;

use super::*;
use crate::testing::{compare, Rng, Scenario};

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
/// system's.
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
        std::fs::create_dir(dir.path().join("work")).unwrap();
        Self { dir }
    }

    fn work(&self) -> PathBuf {
        self.dir.path().join("work")
    }

    fn shell(&self) -> Shell {
        let path = format!("{}:/usr/bin:/bin", self.dir.path().join("bin").display());
        Shell::new(
            self.work(),
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
    effect: ShellEffect,
    approval: Approval,
    stdout: &str,
    status: i32,
) -> Seen {
    Seen {
        run: StepRun {
            step,
            command: command.to_string(),
            effect,
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
            &AutoSet::new([ShellEffect::Read]),
            &approver,
            &record,
        )
        .await;
    assert_eq!(
        (seen(&got, &record), got.end),
        (
            vec![
                ran(0, "cat notes", ShellEffect::Read, Approval::Auto, "", 0),
                ran(1, "grep -c o", ShellEffect::Read, Approval::Auto, "2\n", 0),
                ran(
                    2,
                    "echo made >out.txt",
                    ShellEffect::Write,
                    Approval::Approved,
                    "",
                    0
                ),
                ran(
                    3,
                    "cat out.txt",
                    ShellEffect::Read,
                    Approval::Auto,
                    "made\n",
                    0
                ),
            ],
            End::Refused {
                step: 4,
                command: "curl https://example.com".to_string(),
                effect: ShellEffect::Net,
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
                effect: ShellEffect::Write,
            },
            Ask {
                step: 4,
                command: "curl https://example.com".to_string(),
                effect: ShellEffect::Net,
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
            &AutoSet::new([ShellEffect::Read, ShellEffect::Exec]),
            &approver,
            &record,
        )
        .await;
    assert_eq!(
        (seen(&got, &record), got.end),
        (
            vec![
                ran(0, "cd sub", ShellEffect::Read, Approval::Auto, "", 0),
                ran(1, "export WHO=me", ShellEffect::Exec, Approval::Auto, "", 0),
                ran(2, "X=1", ShellEffect::Exec, Approval::Auto, "", 0),
                ran(3, "false", ShellEffect::Read, Approval::Auto, "", 1),
                ran(
                    4,
                    "echo 'me 1 1'",
                    ShellEffect::Read,
                    Approval::Auto,
                    "me 1 1\n",
                    0
                ),
                ran(
                    5,
                    "tool a 'b c' 2>&1",
                    ShellEffect::Exec,
                    Approval::Auto,
                    "tool a b c\n",
                    0
                ),
                Seen {
                    stderr: "eukhe-shell: missing-program: command not found\n".to_string(),
                    ..ran(
                        6,
                        "missing-program",
                        ShellEffect::Exec,
                        Approval::Auto,
                        "",
                        127
                    )
                },
                ran(7, "exit 3", ShellEffect::Read, Approval::Auto, "", 3),
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
async fn a_script_outside_the_grammar_is_one_exec_step_and_no_answer_refuses_it() {
    let bench = Bench::new();
    let script = "for f in a b; do echo $f; done";
    let unanswered = bench
        .shell()
        .run(
            script,
            &AutoSet::new([ShellEffect::Read]),
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
                effect: ShellEffect::Exec,
                refusal: Refusal::Unanswered,
            },
        }
    );
    let record = Record::default();
    let approved = bench
        .shell()
        .run(
            script,
            &AutoSet::new([ShellEffect::Read]),
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
                ShellEffect::Exec,
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
    let auto = AutoSet::new([ShellEffect::Read]);
    let record = Record::default();
    let got = tokio::time::timeout(
        Duration::from_secs(10),
        bench
            .shell()
            .run("yes | head -n 3", &auto, &Scripted::new([]), &record),
    )
    .await
    .expect("`yes | head -n 3` ends");
    assert_eq!(
        (seen(&got, &record), got.end),
        (
            vec![
                ran(0, "yes", ShellEffect::Read, Approval::Auto, "", 141),
                ran(
                    1,
                    "head -n 3",
                    ShellEffect::Read,
                    Approval::Auto,
                    "y\ny\ny\n",
                    0
                ),
            ],
            End::Finished { status: 0 },
        )
    );
    let record = Record::default();
    let got = tokio::time::timeout(
        Duration::from_secs(10),
        bench
            .shell()
            .run("yes | cat | head -n 2", &auto, &Scripted::new([]), &record),
    )
    .await
    .expect("`yes | cat | head -n 2` ends");
    assert_eq!(
        (seen(&got, &record), got.end),
        (
            vec![
                ran(0, "yes", ShellEffect::Read, Approval::Auto, "", 141),
                ran(1, "cat", ShellEffect::Read, Approval::Auto, "", 141),
                ran(
                    2,
                    "head -n 2",
                    ShellEffect::Read,
                    Approval::Auto,
                    "y\ny\n",
                    0
                ),
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
            &AutoSet::new([ShellEffect::Read]),
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
                effect: ShellEffect::Exec,
                refusal: Refusal::Denied,
            }
        )
    );
}

/// The command of a step with effect `code` (bend/tools.bend `Eff.code`).
fn step_command(id: u64, code: u64) -> String {
    match code {
        0 => "cat r".to_string(),
        1 => format!("touch w{id}"),
        2 => format!("tool {id}"),
        _ => format!("curl {id}"),
    }
}

const EFFECTS: [ShellEffect; 4] = [
    ShellEffect::Read,
    ShellEffect::Write,
    ShellEffect::Exec,
    ShellEffect::Net,
];

/// The bridge to bend/tools.bend `exec`: scripts of steps with effects,
/// auto sets and the user's answers; the steps that ran and how the
/// script ended.
#[tokio::test]
async fn the_gate_runs_as_its_model() {
    let mut rng = Rng(0x5e11_c0de);
    let mut scenarios = Vec::new();
    for at in 0..60 {
        let bench = Bench::new();
        std::fs::write(bench.work().join("r"), "r\n").unwrap();
        let codes: Vec<u64> = (0..rng.range(0, 6)).map(|_| rng.below(4)).collect();
        let auto: Vec<u64> = (0..4).filter(|_| rng.below(2) == 0).collect();
        let answers: Vec<bool> = (0..rng.range(0, 4)).map(|_| rng.below(3) != 0).collect();
        let script: Vec<String> = codes
            .iter()
            .enumerate()
            .map(|(id, &code)| step_command(id as u64, code))
            .collect();
        let approver =
            Scripted::new(answers.iter().map(
                |&yes| {
                    if yes {
                        Answer::Approve
                    } else {
                        Answer::Deny
                    }
                },
            ));
        let got = bench
            .shell()
            .run(
                &script.join("\n"),
                &AutoSet::new(
                    auto.iter()
                        .map(|&code| EFFECTS[usize::try_from(code).unwrap()]),
                ),
                &approver,
                &Record::default(),
            )
            .await;
        let mut transcript = String::from("x");
        for step in &got.steps {
            let code = EFFECTS.iter().position(|&e| e == step.effect).unwrap();
            write!(transcript, " {}:{code}", step.step).unwrap();
        }
        transcript.push('\n');
        match got.end {
            End::Finished { .. } | End::Exited { .. } => transcript.push_str("e fin\n"),
            End::Refused { step, .. } => writeln!(transcript, "e deny {step}").unwrap(),
        }
        let mut events = String::new();
        for (id, code) in codes.iter().enumerate() {
            writeln!(events, "s {id} {code}").unwrap();
        }
        let yeses: Vec<u64> = answers.iter().map(|&yes| u64::from(yes)).collect();
        for (head, items) in [("a", &auto), ("y", &yeses)] {
            events.push_str(head);
            for item in items {
                write!(events, " {item}").unwrap();
            }
            events.push('\n');
        }
        scenarios.push(Scenario {
            name: format!("{at}"),
            events,
            transcript,
        });
    }
    compare("bend/bridge_shell.bend", scenarios);
}
