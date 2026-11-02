//! Every entry of the compiled core on the largest inputs Rust may write.
//!
//! The laws treat a Bend `Nat` as unbounded; the compiled runtime keeps it
//! as an immediate and stops the whole process past 2^48-1. Rust writes no
//! Nat above `wire::NAT_MAX` (14 digits, below 2^48-1) and the Bend Nat
//! reader refuses a 15th digit, so an entry stays inside the bound only if
//! it computes nothing past its inputs' magnitude. That is the trusted
//! boundary this test checks: each file `tests/max_magnitude/<area>.txt`
//! holds valid requests of `bend/ffi_<area>.bend` with every number at its
//! largest, and the entry must answer each of them.
//!
//! A run-time stop ends the process, so each area runs in a child process
//! (this binary again, test `one_area`, the file named by
//! `EUKHE_MAX_MAGNITUDE_FILE`); the parent names the area whose child died.
//!
//! A file holds one step per line (`#` starts a comment line):
//!
//! - `call <input>`: the entry's call answers a value (not the error form);
//! - `open <input>`: opens a stepper, which answers a value;
//! - `step <input>`: feeds the last opened stepper, which answers a value;
//! - `refuse <input>`, `refuse-open <input>`, `refuse-step <input>`: the
//!   same, answered with the error form (an input the wire refuses, such as
//!   a 15-digit number: refused, never a stop).
//!
//! In an input, `{MAX}` is `wire::NAT_MAX`, `{U32MAX}` is `u32::MAX`, `{LONG}`
//! is 15 nines (one digit past the wire), `\n` a newline and `\\` a
//! backslash.

use std::collections::BTreeMap;
use std::path::{Path, PathBuf};
use std::process::Command;

use eukhe_bend::wire::NAT_MAX;
use eukhe_bend::{call, Entry, Stepper};

const FILE_VAR: &str = "EUKHE_MAX_MAGNITUDE_FILE";

fn data_dir() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/max_magnitude")
}

/// The entries of `bend/core_entries.txt`: area name to id.
fn entry_ids() -> BTreeMap<String, u32> {
    let path = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../bend/core_entries.txt");
    let text = std::fs::read_to_string(&path).unwrap_or_else(|e| panic!("{}: {e}", path.display()));
    text.lines()
        .filter(|l| !l.starts_with('#') && !l.trim().is_empty())
        .map(|l| {
            let (id, area) = l
                .split_once(' ')
                .unwrap_or_else(|| panic!("core_entries.txt: {l:?}"));
            let id = id
                .parse()
                .unwrap_or_else(|e| panic!("core_entries.txt: {l:?}: {e}"));
            (area.to_owned(), id)
        })
        .collect()
}

fn expand(raw: &str) -> String {
    let text = raw
        .replace("{MAX}", &NAT_MAX.to_string())
        .replace("{U32MAX}", &u32::MAX.to_string())
        .replace("{LONG}", "999999999999999");
    let mut out = String::with_capacity(text.len());
    let mut chars = text.chars();
    while let Some(c) = chars.next() {
        if c == '\\' {
            match chars.next() {
                Some('n') => out.push('\n'),
                Some('\\') => out.push('\\'),
                other => panic!("max_magnitude: unknown escape \\{other:?} in {raw:?}"),
            }
        } else {
            out.push(c);
        }
    }
    out
}

/// Runs the steps of one area file in this process.
fn run_area(path: &Path) {
    let area = path
        .file_stem()
        .and_then(|s| s.to_str())
        .unwrap_or_else(|| panic!("{}: no area name", path.display()));
    let id = *entry_ids()
        .get(area)
        .unwrap_or_else(|| panic!("{area}: not in bend/core_entries.txt"));
    let entry = *Entry::ALL
        .iter()
        .find(|e| e.id() == id)
        .unwrap_or_else(|| panic!("{area}: id {id} is no Entry"));
    let text = std::fs::read_to_string(path).unwrap_or_else(|e| panic!("{}: {e}", path.display()));
    let mut stepper: Option<Stepper> = None;
    let mut steps = 0;
    for (n, line) in text.lines().enumerate() {
        if line.starts_with('#') || line.trim().is_empty() {
            continue;
        }
        let (kind, raw) = line
            .split_once(' ')
            .unwrap_or_else(|| panic!("{area}:{}: no input", n + 1));
        let input = expand(raw);
        let (action, refused) = match kind.strip_prefix("refuse") {
            Some("") => ("call", true),
            Some(rest) => (rest.strip_prefix('-').unwrap_or(rest), true),
            None => (kind, false),
        };
        let reply = match action {
            "call" => call(entry, &input).unwrap(),
            "open" => {
                let (st, reply) = Stepper::open(entry, &input).unwrap();
                stepper = Some(st);
                reply
            }
            "step" => {
                let st = stepper
                    .as_mut()
                    .unwrap_or_else(|| panic!("{area}:{}: step before open", n + 1));
                st.step(&input).unwrap()
            }
            _ => panic!("{area}:{}: unknown step {kind:?}", n + 1),
        };
        assert_eq!(
            reply.starts_with("E "),
            refused,
            "{area}:{}: {kind} {raw:?} answered {reply:?}",
            n + 1
        );
        steps += 1;
    }
    assert!(steps > 0, "{area}: no step");
}

/// The child: runs the area file the parent names (and nothing when run
/// on its own).
#[test]
fn one_area() {
    if let Ok(path) = std::env::var(FILE_VAR) {
        run_area(Path::new(&path));
    }
}

#[test]
fn every_entry_answers_its_largest_inputs() {
    let ids = entry_ids();
    let dir = data_dir();
    let mut files: Vec<PathBuf> = std::fs::read_dir(&dir)
        .unwrap_or_else(|e| panic!("{}: {e}", dir.display()))
        .map(|e| e.unwrap().path())
        .filter(|p| p.extension().is_some_and(|x| x == "txt"))
        .collect();
    files.sort();
    let covered: Vec<String> = files
        .iter()
        .filter_map(|p| p.file_stem().and_then(|s| s.to_str()).map(str::to_owned))
        .collect();
    // `echo` is the boundary's own self-test: its input is no request.
    let missing: Vec<&String> = ids
        .keys()
        .filter(|a| a.as_str() != "echo" && !covered.contains(a))
        .collect();
    assert!(
        missing.is_empty(),
        "entries with no max_magnitude file: {missing:?}"
    );
    let exe = std::env::current_exe().unwrap();
    let mut failed = Vec::new();
    for file in &files {
        let out = Command::new(&exe)
            .args(["--exact", "one_area", "--nocapture", "--test-threads=1"])
            .env(FILE_VAR, file)
            .output()
            .unwrap();
        if !out.status.success() {
            failed.push(format!(
                "{}: {}\n{}{}",
                file.display(),
                out.status,
                String::from_utf8_lossy(&out.stdout),
                String::from_utf8_lossy(&out.stderr)
            ));
        }
    }
    assert!(failed.is_empty(), "{}", failed.join("\n"));
}
