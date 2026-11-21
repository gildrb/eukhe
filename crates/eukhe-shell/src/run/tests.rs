use std::os::unix::fs::PermissionsExt as _;
use std::time::Duration;

use eukhe_types::path_policy::{OwnKind, OwnPath, OwnRule, PathRule};
use parking_lot::Mutex;
use ShellEffect::{Exec, Net, Outside, Protected, Read, Secret, Write};

use super::*;

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
/// secret, `agent` eukhe's own config (all outside `work`).
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
        for sub in ["work", "guard", "keys", "agent"] {
            std::fs::create_dir(dir.path().join(sub)).unwrap();
        }
        std::fs::write(dir.path().join("keys/id"), "secret\n").unwrap();
        Self { dir }
    }

    fn work(&self) -> PathBuf {
        self.dir.path().join("work")
    }

    /// `name` in the own `agent` dir, as the refusal names it (real).
    fn agent(&self, name: &str) -> PathBuf {
        std::fs::canonicalize(self.dir.path().join("agent"))
            .unwrap()
            .join(name)
    }

    fn paths(&self) -> PathPolicy {
        PathPolicy::new(
            vec![self.work()],
            vec![PathRule::Tree(self.dir.path().join("guard"))],
            vec![self.dir.path().join("keys")],
        )
        .with_own(vec![OwnRule {
            path: OwnPath::Tree(self.dir.path().join("agent")),
            kind: OwnKind::Config,
        }])
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

fn ran(step: u64, command: &str, effects: &[ShellEffect], stdout: &str, status: i32) -> Seen {
    Seen {
        run: StepRun {
            step,
            command: command.to_string(),
            effects: ShellEffects::of(effects),
            status,
        },
        stdout: stdout.to_string(),
        stderr: String::new(),
    }
}

/// Every step runs unasked, an irreversible one too; a step that writes
/// an own path is refused, and it and every later step do not run.
#[tokio::test]
async fn every_step_runs_unasked_and_an_own_write_stops_the_script() {
    let bench = Bench::new();
    std::fs::write(bench.work().join("notes"), "one\ntwo\n").unwrap();
    let record = Record::default();
    let mut shell = bench.shell();
    let got = shell
        .run(
            "cat notes | grep -c o\necho made > out.txt && cat out.txt\ncurl https://example.com\necho x > ../agent/settings.json\ntouch never",
            &bench.paths(),
            &Unasked,
            &record,
        )
        .await;
    assert_eq!(
        (seen(&got, &record), got.end),
        (
            vec![
                ran(0, "cat notes", &[Read], "", 0),
                ran(1, "grep -c o", &[Read], "2\n", 0),
                ran(2, "echo made >out.txt", &[Read, Write], "", 0),
                ran(3, "cat out.txt", &[Read], "made\n", 0),
                ran(
                    4,
                    "curl https://example.com",
                    &[Net],
                    "curl https://example.com\n",
                    0
                ),
            ],
            End::Refused {
                step: 5,
                command: "echo x >../agent/settings.json".to_string(),
                effects: ShellEffects::of(&[Read, Write, Outside]),
                own: OwnWrite {
                    path: bench.agent("settings.json"),
                    kind: OwnKind::Config,
                },
            },
        )
    );
    assert_eq!(
        (
            bench.agent("settings.json").exists(),
            bench.work().join("never").exists()
        ),
        (false, false)
    );
}

#[tokio::test]
async fn shell_state_chains_and_external_programs() {
    let bench = Bench::new();
    std::fs::create_dir(bench.work().join("sub")).unwrap();
    let record = Record::default();
    let mut shell = bench.shell();
    let got = shell
        .run(
            "cd sub; export WHO=me; X=1; false || echo \"$WHO $X $?\"; tool a 'b c' 2>&1; missing-program; exit 3; echo after",
            &bench.paths(),
            &Unasked,
            &record,
        )
        .await;
    assert_eq!(
        (seen(&got, &record), got.end),
        (
            vec![
                ran(0, "cd sub", &[Read], "", 0),
                ran(1, "export WHO=me", &[Exec], "", 0),
                ran(2, "X=1", &[Exec], "", 0),
                ran(3, "false", &[Read], "", 1),
                ran(4, "echo 'me 1 1'", &[Read], "me 1 1\n", 0),
                ran(5, "tool a 'b c' 2>&1", &[Exec], "tool a b c\n", 0),
                Seen {
                    stderr: "eukhe-shell: missing-program: command not found\n".to_string(),
                    ..ran(6, "missing-program", &[Exec], "", 127)
                },
                ran(7, "exit 3", &[Read], "", 3),
            ],
            End::Exited { status: 3 },
        )
    );
    assert_eq!(
        shell.cwd(),
        std::fs::canonicalize(bench.work().join("sub")).unwrap()
    );
}

/// A script outside the grammar is one step of the external shell with
/// every effect its commands hold: it runs unasked, and is refused whole
/// when one of its commands writes an own path.
#[tokio::test]
async fn a_script_outside_the_grammar_is_one_step_with_every_effect_it_holds() {
    let bench = Bench::new();
    let script = "for f in a b; do echo $f; done";
    let record = Record::default();
    let got = bench
        .shell()
        .run(script, &bench.paths(), &Unasked, &record)
        .await;
    let command = format!("bash -c '{script}'");
    assert_eq!(
        (seen(&got, &record), got.end),
        (
            vec![ran(0, &command, &[Read, Exec], "a\nb\n", 0)],
            End::Finished { status: 0 },
        )
    );
    let script = "for f in a; do echo $f > ../agent/f; done";
    let got = bench
        .shell()
        .run(script, &bench.paths(), &Unasked, &Record::default())
        .await;
    assert_eq!(
        got,
        Ran {
            steps: Vec::new(),
            end: End::Refused {
                step: 0,
                command: format!("bash -c '{script}'"),
                effects: ShellEffects::of(&[Read, Write, Exec, Outside]),
                own: OwnWrite {
                    path: bench.agent("f"),
                    kind: OwnKind::Config,
                },
            },
        }
    );
    assert!(!bench.agent("f").exists());
}

/// Regression: the commands of a pipeline run together, so a command
/// that stops reading ends the endless one before it. `yes` dies of
/// SIGPIPE (141); the own `cat` between them ends with the same status
/// when its output pipe closes.
#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn a_pipeline_ends_when_its_last_command_stops_reading() {
    let bench = Bench::new();
    let paths = bench.paths();
    let record = Record::default();
    let got = tokio::time::timeout(
        Duration::from_secs(10),
        bench
            .shell()
            .run("yes | head -n 3", &paths, &Unasked, &record),
    )
    .await
    .expect("`yes | head -n 3` ends");
    assert_eq!(
        (seen(&got, &record), got.end),
        (
            vec![
                ran(0, "yes", &[Read], "", 141),
                ran(1, "head -n 3", &[Read], "y\ny\ny\n", 0),
            ],
            End::Finished { status: 0 },
        )
    );
    let record = Record::default();
    let got = tokio::time::timeout(
        Duration::from_secs(10),
        bench
            .shell()
            .run("yes | cat | head -n 2", &paths, &Unasked, &record),
    )
    .await
    .expect("`yes | cat | head -n 2` ends");
    assert_eq!(
        (seen(&got, &record), got.end),
        (
            vec![
                ran(0, "yes", &[Read], "", 141),
                ran(1, "cat", &[Read], "", 141),
                ran(2, "head -n 2", &[Read], "y\ny\n", 0),
            ],
            End::Finished { status: 0 },
        )
    );
}

/// A refused command of a pipeline runs none of it: every command is
/// judged before any runs, so the endless `yes` before the refused `cat`
/// never starts.
#[tokio::test]
async fn a_refused_command_runs_none_of_its_pipeline() {
    let bench = Bench::new();
    let got = bench
        .shell()
        .run(
            "echo first; yes | cat > ../agent/x",
            &bench.paths(),
            &Unasked,
            &Record::default(),
        )
        .await;
    assert_eq!(
        (got.steps.len(), got.end),
        (
            1,
            End::Refused {
                step: 2,
                command: "cat >../agent/x".to_string(),
                effects: ShellEffects::of(&[Read, Write, Outside]),
                own: OwnWrite {
                    path: bench.agent("x"),
                    kind: OwnKind::Config,
                },
            }
        )
    );
}

/// Regression (audit H4, H2, M4): a step had one effect, so a write
/// redirection of a `Net` or `Exec` step, a write outside the workspace
/// or to a protected place, and a read of a secret counted only its main
/// effect. Every effect of a step is its own, so each irreversible one
/// is recorded.
#[tokio::test]
async fn every_effect_of_a_step_counts() {
    let bench = Bench::new();
    let got = bench
        .shell()
        .run(
            "curl x > got; touch ../out; touch ../guard/g; cat ../keys/id; cp ../keys/id copy",
            &bench.paths(),
            &Unasked,
            &Record::default(),
        )
        .await;
    let effects: Vec<ShellEffects> = got.steps.iter().map(|step| step.effects).collect();
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
            End::Finished { status: 0 },
        )
    );
}

/// The steps of `ran` that access a secret.
fn secret_steps(ran: &Ran) -> Vec<u64> {
    ran.steps
        .iter()
        .filter(|step| step.effects.contains(Secret))
        .map(|step| step.step)
        .collect()
}

/// Regression: every step run in a working directory that held a secret
/// (the home dir) had `Secret`, so `echo hi`, `date` and `git -C repo
/// log` there counted as irreversible. Only a step that reads the
/// directory because it names no path of its own and descends into it
/// (`rg x`, `grep -r x`, `find -name x`, `du`) reads the secret in it; a
/// shallow `ls` names the entries and reads nothing below them.
#[tokio::test]
async fn only_a_step_that_reads_its_working_directory_reads_a_secret_in_it() {
    let bench = Bench::new();
    let got = bench
        .shell_at(bench.dir.path().to_path_buf())
        .run(
            "echo hi; date; git -C work log; ls work; rg x work; ls; rg x; grep -r x; find -name x; du",
            &bench.paths(),
            &Unasked,
            &Record::default(),
        )
        .await;
    assert_eq!(
        (secret_steps(&got), got.steps.len()),
        ((6..10).collect(), 10)
    );
}

/// A shallow `ls` of a directory that only holds a secret below it (the
/// bench dir over `keys`) names the entries and reads no secret. A
/// recursive `ls -R` of it, `find` and `rg` over it, a listing of the
/// secret itself and a read inside it read the secret.
#[tokio::test]
async fn a_shallow_ls_of_a_secret_holding_directory_reads_no_secret() {
    let bench = Bench::new();
    let got = bench
        .shell_at(bench.dir.path().to_path_buf())
        .run(
            "ls .; ls keys; ls -R .; find .; rg x .; cat keys/id",
            &bench.paths(),
            &Unasked,
            &Record::default(),
        )
        .await;
    assert_eq!((secret_steps(&got), got.steps.len()), ((1..6).collect(), 6));
}

/// Asks about each step in order and refuses one (`refused`), keeping
/// every question.
struct Editor {
    refused: u64,
    asked: Mutex<Vec<(u64, String, ShellEffects)>>,
}

impl Before for Editor {
    fn allows(
        &self,
        step: u64,
        command: &str,
        effects: ShellEffects,
    ) -> impl Future<Output = bool> + Send {
        self.asked.lock().push((step, command.to_owned(), effects));
        std::future::ready(step != self.refused)
    }
}

/// A step `before` refuses does not run, and neither does any later
/// step: the script ends `Rejected` there. An own write is refused before
/// `before` is asked about it.
#[tokio::test]
async fn a_step_before_refuses_stops_the_script() {
    let bench = Bench::new();
    let editor = Editor {
        refused: 1,
        asked: Mutex::new(Vec::new()),
    };
    let record = Record::default();
    let got = bench
        .shell()
        .run(
            "echo one > one.txt; curl https://example.com; echo two > two.txt",
            &bench.paths(),
            &editor,
            &record,
        )
        .await;
    assert_eq!(
        (
            seen(&got, &record),
            got.end,
            editor.asked.lock().clone(),
            bench.work().join("two.txt").exists()
        ),
        (
            vec![ran(0, "echo one >one.txt", &[Read, Write], "", 0)],
            End::Rejected {
                step: 1,
                command: "curl https://example.com".to_string(),
                effects: ShellEffects::of(&[Net]),
            },
            vec![
                (
                    0,
                    "echo one >one.txt".to_owned(),
                    ShellEffects::of(&[Read, Write])
                ),
                (
                    1,
                    "curl https://example.com".to_owned(),
                    ShellEffects::of(&[Net])
                ),
            ],
            false
        )
    );
    let editor = Editor {
        refused: u64::MAX,
        asked: Mutex::new(Vec::new()),
    };
    let got = bench
        .shell()
        .run(
            "echo x > ../agent/f",
            &bench.paths(),
            &editor,
            &Record::default(),
        )
        .await;
    assert_eq!(
        (
            matches!(got.end, End::Refused { .. }),
            editor.asked.lock().len()
        ),
        (true, 0)
    );
}
