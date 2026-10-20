use std::collections::{BTreeSet, VecDeque};
use std::fmt::Write as _;
use std::os::unix::fs::PermissionsExt as _;
use std::time::Duration;

use eukhe_types::path_policy::PathRule;
use parking_lot::Mutex;
use ShellEffect::{Exec, Net, Outside, Protected, Read, Secret, Write};

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

/// Where a bridge scenario runs: the workspace, or the bench dir above
/// it, which holds the secret `keys`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
enum At {
    Work,
    Bench,
}

/// One part of a step as the bridge reads it: 1 when it names a path
/// that is or holds a secret (else 0), and its own effect codes.
type Part = (u8, Vec<u8>);

/// A step's command (`base` of [`BASES`]) with a redirection (`redirect`
/// of [`REDIRECTS`]), run in `at`, and its parts as the bridge expects
/// them, from the path classes of [`Bench`] (bend/tools.bend effect
/// codes). Every word that names no secret, outside or protected path
/// is inside the workspace from both directories. `ls` and `grep -r`
/// read the working directory (a secret part in the bench dir); `echo`
/// and `date` do not.
fn step_parts(id: u64, base: u64, redirect: u64, at: At) -> (String, Vec<Part>) {
    let (up, work) = match at {
        At::Work => ("../", ""),
        At::Bench => ("", "work/"),
    };
    let cwd = u8::from(at == At::Bench);
    let (command, mut parts): (String, Vec<Part>) = match base {
        0 => (format!("cat {work}r"), vec![(0, vec![0])]),
        1 => (format!("touch {work}w{id}"), vec![(0, vec![1])]),
        2 => (format!("tool {work}{id}"), vec![(0, vec![2])]),
        3 => (format!("curl {work}{id}"), vec![(0, vec![3])]),
        4 => (format!("cat {up}keys/id"), vec![(0, vec![0]), (1, vec![])]),
        5 => (
            format!("touch {up}out{id}"),
            vec![(0, vec![1]), (0, vec![4])],
        ),
        6 => (
            format!("touch {up}guard/g{id}"),
            vec![(0, vec![1]), (0, vec![5])],
        ),
        7 => (format!("echo {work}hi"), vec![(0, vec![0])]),
        8 => ("date".to_string(), vec![(0, vec![0])]),
        9 => ("ls".to_string(), vec![(0, vec![0]), (cwd, vec![])]),
        _ => (
            format!("grep -r {work}x"),
            vec![(0, vec![0]), (cwd, vec![])],
        ),
    };
    let (suffix, part): (String, Option<Part>) = match redirect {
        0 => (String::new(), None),
        1 => (format!(" > {work}o{id}"), Some((0, vec![1]))),
        2 => (format!(" > {up}out{id}r"), Some((0, vec![1, 4]))),
        3 => (format!(" > {up}guard/r{id}"), Some((0, vec![1, 5]))),
        _ => (format!(" < {up}keys/id"), Some((1, vec![0]))),
    };
    parts.extend(part);
    (format!("{command}{suffix}"), parts)
}

/// The command kinds of [`step_parts`].
const BASES: u64 = 11;
/// The redirection kinds of [`step_parts`].
const REDIRECTS: u64 = 5;

/// The bridge to bend/tools.bend `part.effs`, `join` and `exec`: scripts
/// of steps built from parts whose effects and secret paths the path
/// classes fix, run in the workspace or in the bench dir (which holds a
/// secret: only a command that reads it has a secret part for it), (a
/// script outside the grammar is one step: exec and every part of every
/// command), auto sets (with the codes that never take effect too) and
/// the user's answers (one per step, mostly yes, so that later steps are
/// reached; some scenarios end their answers early); the steps that ran
/// with their effects, and how the script ended. Every command kind and
/// every redirection kind runs in some scenario in each directory, so a
/// wrong effect of any part shows in a transcript.
#[tokio::test]
#[allow(clippy::too_many_lines)] // One scenario loop: build the script, run it, write its transcript and its model events.
async fn the_gate_runs_as_its_model() {
    let mut rng = Rng(0x5e11_c0de);
    let mut scenarios = Vec::new();
    let mut ran_bases = BTreeSet::new();
    let mut ran_redirects = BTreeSet::new();
    for at in 0..240 {
        let bench = Bench::new();
        std::fs::write(bench.work().join("r"), "r\n").unwrap();
        let place = if rng.below(2) == 0 {
            At::Work
        } else {
            At::Bench
        };
        let kinds: Vec<(u64, u64)> = (0..rng.range(0, 5))
            .map(|_| (rng.below(BASES), rng.below(REDIRECTS)))
            .collect();
        let built: Vec<(String, Vec<Part>)> = (0_u64..)
            .zip(&kinds)
            .map(|(id, &(base, redirect))| step_parts(id, base, redirect, place))
            .collect();
        let external = !built.is_empty() && rng.below(4) == 0;
        let auto: Vec<u8> = (0..7).filter(|_| rng.below(2) == 0).collect();
        let short = usize::from(rng.below(6) == 0);
        let answers: Vec<bool> = (0..built.len().saturating_sub(short))
            .map(|_| rng.below(8) != 0)
            .collect();
        let mut lines: Vec<String> = built.iter().map(|(line, _)| line.clone()).collect();
        if external {
            lines[0] = format!("( {} )", lines[0]);
        }
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
        let cwd = match place {
            At::Work => bench.work(),
            At::Bench => bench.dir.path().to_path_buf(),
        };
        let got = bench
            .shell_at(cwd)
            .run(
                &lines.join("\n"),
                AutoSet::new(auto.iter().map(|&code| ShellEffect::ALL[usize::from(code)])),
                &bench.paths(),
                &approver,
                &Record::default(),
            )
            .await;
        if !external {
            for step in &got.steps {
                let (base, redirect) = kinds[usize::try_from(step.step).unwrap()];
                ran_bases.insert((place, base));
                ran_redirects.insert((place, redirect));
            }
        }
        let mut transcript = String::from("x");
        for step in &got.steps {
            let codes: Vec<String> = step.effects.iter().map(|e| e.code().to_string()).collect();
            write!(transcript, " {}:{}", step.step, codes.join(",")).unwrap();
        }
        transcript.push('\n');
        match got.end {
            End::Finished { .. } | End::Exited { .. } => transcript.push_str("e fin\n"),
            End::Refused { step, .. } => writeln!(transcript, "e deny {step}").unwrap(),
        }
        let mut events = String::new();
        let part = |events: &mut String, (secret, codes): &Part| {
            write!(events, "p {secret}").unwrap();
            for code in codes {
                write!(events, " {code}").unwrap();
            }
            events.push('\n');
        };
        if external {
            events.push_str("s 0\n");
            part(&mut events, &(0, vec![2]));
        }
        for (id, (_, parts)) in built.iter().enumerate() {
            if !external {
                writeln!(events, "s {id}").unwrap();
            }
            for each in parts {
                part(&mut events, each);
            }
        }
        let yeses: Vec<u8> = answers.iter().map(|&yes| u8::from(yes)).collect();
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
    let every = |kinds: u64| -> BTreeSet<(At, u64)> {
        [At::Work, At::Bench]
            .into_iter()
            .flat_map(|place| (0..kinds).map(move |kind| (place, kind)))
            .collect()
    };
    assert_eq!(
        (ran_bases, ran_redirects),
        (every(BASES), every(REDIRECTS)),
        "every command and redirection kind runs in some scenario in each directory"
    );
    compare("bend/bridge_shell.bend", scenarios);
}

/// Regression (audit H4, H2, M4): a step had one effect, so a write
/// redirection of a `Net` or `Exec` step, a write outside the workspace
/// or to a protected place, and a read of a secret ran with the auto set
/// of its main effect.
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
            1,
            End::Refused {
                step: 1,
                command: "touch ../out".to_string(),
                effects: ShellEffects::of(&[Write, Outside]),
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
