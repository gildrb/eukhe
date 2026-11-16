//! The budget ledger's appends under a crash (spec/README.md B5 and D1, law
//! `ledger_ack_durable` of laws/log.bend), at every append point.
//!
//! A child process (this test binary again, in [`child_appends_records`])
//! appends records to one account, an operation each time the test says
//! `go`, and says how many records the account holds once each operation
//! is acknowledged. The test kills it with SIGKILL before an operation,
//! right after an acknowledged one, and while one runs, round after round
//! on the same account, each child recovering what the one before left in
//! flight. After every kill the account holds every record acknowledged
//! before it, unchanged and in order, each once, and replays exactly.
//!
//! A kill inside a record's write leaves its first bytes: the account is
//! then cut at every byte of each append in turn. An open reads exactly
//! the complete records, and the next operation appends its record right
//! after them, byte for byte what it appends to the uncut account.

use std::io::{BufRead, BufReader, Write};
use std::path::Path;
use std::process::{Child, ChildStdin, ChildStdout, Command, Stdio};
use std::time::Duration;

use eukhe_budget::{Ledger, Record, Reserved, Use};
use eukhe_types::budget::{BudgetAmounts, BudgetLimits};

/// The account directory of a child process; unset in the test run.
const CHILD: &str = "EUKHE_LEDGER_CRASH_CHILD";

/// The session whose account the records go to.
const ROOT: &str = "root";

/// The time every ledger of these tests reads.
const T0: u64 = 1_800_000_000_000;

fn fixed() -> u64 {
    T0
}

fn at(dir: &Path) -> Ledger {
    Ledger::of(dir, ROOT).with_clock(fixed)
}

fn request(cost_micros: u64) -> BudgetAmounts {
    BudgetAmounts {
        cost_micros,
        requests: 1,
        ..BudgetAmounts::default()
    }
}

/// A budget no run of these tests spends.
fn limits() -> BudgetLimits {
    BudgetLimits {
        cost_micros: Some(1_000_000_000),
        requests: Some(1_000_000),
        ..BudgetLimits::default()
    }
}

/// The operation after `held` (the reservation this process holds): the
/// account's open, or a restart's recovery, first; then a reservation and
/// its settlement in turn. Answers the reservation held after it.
fn operate(ledger: &Ledger, first: bool, held: Option<u64>) -> Option<u64> {
    if first {
        if ledger.exists() {
            ledger.recover(ROOT).expect("recover");
        } else {
            ledger.open_root(limits()).expect("open");
        }
        return None;
    }
    match held {
        Some(id) => {
            ledger.settle(id, request(7)).expect("settle");
            None
        }
        None => match ledger
            .reserve(
                ROOT,
                Use::Work,
                "model:test/m",
                BudgetAmounts::default(),
                BudgetAmounts::default(),
                &[request(10)],
                0,
            )
            .expect("reserve")
        {
            Reserved::Granted { reservation, .. } => Some(reservation.id),
            Reserved::Refused { refusal, .. } => panic!("refused: {refusal:?}"),
        },
    }
}

/// The child: one operation per `go` line, then `acked <records>`.
#[test]
fn child_appends_records() {
    let Some(dir) = std::env::var_os(CHILD) else {
        return;
    };
    let ledger = at(Path::new(&dir));
    let mut held = None;
    for (index, line) in std::io::stdin().lock().lines().enumerate() {
        assert_eq!(line.expect("stdin"), "go");
        held = operate(&ledger, index == 0, held);
        let records = ledger.audit().expect("audit").records;
        println!("acked {records}");
        std::io::stdout().flush().expect("stdout");
    }
}

/// A child process appending to the account under `dir`.
struct Appender {
    process: Child,
    stdin: ChildStdin,
    stdout: BufReader<ChildStdout>,
}

impl Appender {
    fn spawn(dir: &Path) -> Appender {
        let mut process = Command::new(std::env::current_exe().expect("test binary"))
            .args(["--exact", "child_appends_records", "--nocapture"])
            .env(CHILD, dir)
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .spawn()
            .expect("spawn child");
        let stdin = process.stdin.take().expect("child stdin");
        let stdout = BufReader::new(process.stdout.take().expect("child stdout"));
        Appender {
            process,
            stdin,
            stdout,
        }
    }

    fn go(&mut self) {
        writeln!(self.stdin, "go").expect("send go");
        self.stdin.flush().expect("flush go");
    }

    /// The records the account holds once the operation is acknowledged.
    fn acked(&mut self) -> usize {
        loop {
            let mut line = String::new();
            assert_ne!(
                self.stdout.read_line(&mut line).expect("read"),
                0,
                "the child died"
            );
            if let Some(records) = line.trim_end().strip_prefix("acked ") {
                return records.parse().expect("a count");
            }
        }
    }

    fn kill(mut self) {
        self.process.kill().expect("SIGKILL");
        self.process.wait().expect("reap");
    }
}

/// The complete lines of the account file (a torn tail is no record).
fn complete_lines(dir: &Path) -> Vec<String> {
    let text = std::fs::read_to_string(at(dir).path()).unwrap_or_default();
    let end = text.rfind('\n').map_or(0, |at| at + 1);
    text[..end].lines().map(str::to_owned).collect()
}

/// The account holds the lines `kept` first, then only records, each
/// numbered by its place, and replays exactly.
fn assert_holds(dir: &Path, kept: &[String]) -> Vec<String> {
    let lines = complete_lines(dir);
    assert!(
        lines.starts_with(kept),
        "an acknowledged record changed or was lost:\n{kept:#?}\n{lines:#?}"
    );
    for (index, line) in lines.iter().enumerate() {
        let record: Record = serde_json::from_str(line).expect("a whole record");
        assert_eq!(record.seq, index as u64, "{line}");
    }
    if !lines.is_empty() {
        let audit = at(dir).audit().expect("audit");
        assert_eq!(audit.first_mismatch, None);
        assert_eq!(audit.records, lines.len() as u64);
    }
    lines
}

#[test]
fn a_ledger_killed_at_every_append_point_keeps_every_acknowledged_record() {
    let dir = tempfile::tempdir().unwrap();
    let mut kept = Vec::new();
    for round in 0..24_u64 {
        let mut child = Appender::spawn(dir.path());
        for _ in 0..round % 4 {
            child.go();
            let records = child.acked();
            kept = complete_lines(dir.path());
            assert!(
                kept.len() >= records,
                "an acknowledged record is not on disk"
            );
        }
        match round % 3 {
            // Right after the last acknowledged record (before any, in a
            // round that acknowledged none).
            0 => {}
            // While the next operation starts.
            1 => child.go(),
            // While it runs.
            _ => {
                child.go();
                std::thread::sleep(Duration::from_micros(round * 150));
            }
        }
        child.kill();
        kept = assert_holds(dir.path(), &kept);
    }
    assert!(kept.len() > 10, "{} records", kept.len());
    let mut last = Appender::spawn(dir.path());
    last.go();
    last.acked();
    last.kill();
    assert_holds(dir.path(), &kept);
    assert_eq!(at(dir.path()).holds(ROOT).unwrap(), Vec::new());
}

/// The account's bytes after each of the first `count` operations of one
/// process, from none, each with the reservation held before it.
fn appended(count: usize) -> Vec<(Vec<u8>, Option<u64>)> {
    let dir = tempfile::tempdir().unwrap();
    let ledger = at(dir.path());
    let mut files = vec![(Vec::new(), None)];
    let mut held = None;
    for index in 0..count {
        held = operate(&ledger, index == 0, held);
        files.push((std::fs::read(ledger.path()).unwrap(), held));
    }
    files
}

/// The account after its record `index`, cut at byte `cut` (`files`: the
/// account after each record): no read counts the torn record, and the
/// next operation appends exactly what it appends to the uncut account.
fn cut_then_append(files: &[(Vec<u8>, Option<u64>)], index: usize, cut: usize) {
    let ((_, held), (after, _)) = (&files[index], &files[index + 1]);
    let dir = tempfile::tempdir().unwrap();
    let ledger = at(dir.path());
    std::fs::write(ledger.path(), &after[..cut]).unwrap();
    if index == 0 {
        assert_eq!(ledger.report(ROOT).unwrap(), None, "cut at byte {cut}");
        ledger.open_root(limits()).expect("open");
    } else {
        let records = ledger.audit().unwrap().records;
        assert_eq!(records, index as u64, "cut at byte {cut}");
        operate(&ledger, false, *held);
    }
    assert_eq!(
        std::fs::read(ledger.path()).unwrap(),
        *after,
        "the append after a cut at byte {cut} of record {index}"
    );
}

#[test]
fn a_record_cut_at_any_byte_is_never_read_and_the_next_append_follows_the_complete_ones() {
    // An open, a reservation and its settlement: each kind of record.
    let files = appended(3);
    let mut cuts = Vec::new();
    for (index, pair) in files.windows(2).enumerate() {
        let (before, after) = (&pair[0].0, &pair[1].0);
        assert!(after.starts_with(before));
        cuts.extend((before.len()..after.len()).map(|cut| (index, cut)));
    }
    // Each cut has an account of its own: they run on every core.
    let workers = std::thread::available_parallelism().map_or(1, usize::from);
    std::thread::scope(|scope| {
        for worker in 0..workers {
            let (files, cuts) = (&files, &cuts);
            scope.spawn(move || {
                for &(index, cut) in cuts.iter().skip(worker).step_by(workers) {
                    cut_then_append(files, index, cut);
                }
            });
        }
    });
}
