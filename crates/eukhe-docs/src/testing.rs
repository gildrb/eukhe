//! The bridge tests' harness (a copy of `eukhe-durable`'s
//! `testing::bridge`: eukhe-docs may not depend on eukhe-durable, see the
//! crate table in AGENTS.md). A Rust component and its Bend model (a
//! `bend/` file, whose laws `PROOF.bend` proves) run the same scenarios
//! and must print the same transcript, byte for byte.
//!
//! [`Rng`] generates the scenarios, the same on every run; [`compare`]
//! builds the model's bridge file into a native binary, runs it on each
//! scenario's events and diffs its output with the Rust transcript. It
//! needs `bend` (2.0.39; `$BEND` or on `PATH`) and clang. Without `bend` a
//! bridge is skipped with a message, unless `EUKHE_REQUIRE_BEND` is set, as
//! CI sets it: then a missing `bend` fails it.

use std::path::{Path, PathBuf};
use std::process::Command;

/// A small xorshift generator: the scenarios are the same on every run.
pub struct Rng(pub u64);

impl Rng {
    /// The next number of the sequence.
    fn next(&mut self) -> u64 {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        self.0
    }

    /// A number in `0..n` (`n > 0`).
    pub fn below(&mut self, n: u64) -> u64 {
        self.next() % n
    }

    /// A number in `low..=high`.
    pub fn range(&mut self, low: u64, high: u64) -> u64 {
        low + self.next() % (high - low + 1)
    }
}

/// One scenario of a bridge: its name, the events the model reads, and the
/// transcript the Rust code printed.
pub struct Scenario {
    pub name: String,
    pub events: String,
    pub transcript: String,
}

/// `bend`: `$BEND`, else the first `bend` on `PATH`.
fn bend() -> Option<PathBuf> {
    if let Some(path) = std::env::var_os("BEND") {
        return Some(PathBuf::from(path));
    }
    std::env::split_paths(&std::env::var_os("PATH")?)
        .map(|dir| dir.join("bend"))
        .find(|path| path.is_file())
}

/// The first line where the two transcripts differ, with its number.
fn first_difference(rust: &str, bend: &str) -> String {
    let (mut rust_lines, mut bend_lines) = (rust.lines(), bend.lines());
    let mut at = 1;
    loop {
        match (rust_lines.next(), bend_lines.next()) {
            (Some(left), Some(right)) if left == right => at += 1,
            (None, None) => return "none".to_string(),
            (left, right) => {
                return format!("line {at}:\n  rust: {left:?}\n  bend: {right:?}");
            }
        }
    }
}

/// Build `model` (a `bend/` file, from the repository root) into a native
/// binary, run it on each scenario's events, and require its output to be
/// the Rust transcript, byte for byte. A mismatch keeps the scenario's
/// events and both transcripts in the temp dir. Skips (with a message)
/// when `bend` is not installed, unless `EUKHE_REQUIRE_BEND` is set.
///
/// # Panics
///
/// When `bend` is missing and `EUKHE_REQUIRE_BEND` is set, when the model
/// does not build or fails on a scenario, and when its output differs from
/// the Rust transcript.
pub fn compare(model: &str, scenarios: impl IntoIterator<Item = Scenario>) {
    let Some(bend) = bend() else {
        assert!(
            std::env::var_os("EUKHE_REQUIRE_BEND").is_none(),
            "EUKHE_REQUIRE_BEND is set but no `bend` is on PATH (or in $BEND)"
        );
        eprintln!(
            "SKIPPED the bridge to {model}: `bend` is not installed \
             (https://bend-lang.com/install.sh, version 2.0.39), so the Rust code was \
             not compared with its Bend model"
        );
        return;
    };
    let dir = tempfile::tempdir().unwrap();
    let binary = dir.path().join("bridge");
    let source = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../..")
        .join(model);
    let built = Command::new(&bend)
        .arg(&source)
        .arg("-o")
        .arg(&binary)
        .output()
        .unwrap();
    assert!(
        built.status.success(),
        "bend could not build {model}:\n{}{}",
        String::from_utf8_lossy(&built.stdout),
        String::from_utf8_lossy(&built.stderr)
    );
    let stem = Path::new(model).file_stem().map_or_else(
        || "bridge".to_string(),
        |stem| stem.to_string_lossy().into_owned(),
    );
    for (at, scenario) in scenarios.into_iter().enumerate() {
        let Scenario {
            name,
            events,
            transcript,
        } = scenario;
        let path = dir.path().join(format!("scenario-{at}"));
        std::fs::write(&path, &events).unwrap();
        let ran = Command::new(&binary).arg(&path).output().unwrap();
        assert!(
            ran.status.success(),
            "{model} failed on scenario {name}:\n{}",
            String::from_utf8_lossy(&ran.stderr)
        );
        let output = String::from_utf8(ran.stdout).unwrap();
        if output != transcript {
            let kept = std::env::temp_dir().join(format!("eukhe-{stem}-{at}"));
            std::fs::create_dir_all(&kept).unwrap();
            std::fs::write(kept.join("events"), &events).unwrap();
            std::fs::write(kept.join("rust"), &transcript).unwrap();
            std::fs::write(kept.join("bend"), &output).unwrap();
            panic!(
                "the Rust code and {model} differ on scenario {name} (kept in {}): {}",
                kept.display(),
                first_difference(&transcript, &output)
            );
        }
    }
}
