//! Shared harness for hashline integration tests.
//!
//! [`Workspace`] is a temp directory plus an [`EditStore`]; [`DiskWriter`]
//! persists writes to disk and records every request. [`run_fixture`] runs
//! the session-level JSON fixtures (`tests/fixtures/hashline/patcher.json`):
//!
//! ```json
//! { "cases": [ {
//!   "name": "…",
//!   "files": { "a.txt": "…" },
//!   "args": { "input": "[a.txt#{{tag:a.txt}}]\nPUT 1.=1:\n+x" },
//!   "policy": { "enforceSeenLines": true },
//!   "snapshots": [ { "path": "a.txt", "text": "…", "seenLines": [1] } ],
//!   "expect": { "files": {}, "deleted": [], "error": "substring or ^regex",
//!               "text": "exact", "textContains": [], "writes": 0 }
//! } ] }
//! ```
#![allow(dead_code, reason = "each test binary uses a subset of the harness")]

use std::{
    path::{Path, PathBuf},
    sync::Mutex,
};

use eukhe_docs::{
    apply_hashline, text::lf_text, EditError, EditStore, EditWriter, HashlineOptions,
    HashlineOutcome, Published, WriteOp, WriteRequest,
};
use serde_json::Value;

/// One recorded write: source path and the operation kind.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RecordedWrite {
    pub absolute: PathBuf,
    pub op: &'static str,
    pub before_raw: Option<String>,
}

/// Writes to disk and records every request.
#[derive(Default)]
pub struct DiskWriter {
    pub requests: Mutex<Vec<RecordedWrite>>,
    /// Text the writer reports (and persists) instead of the sent content,
    /// like an editor that formats on save.
    pub rewrite: Option<String>,
}

impl DiskWriter {
    pub fn writes(&self) -> usize {
        self.requests.lock().expect("writer lock").len()
    }
}

fn io_error(path: &Path, source: std::io::Error) -> EditError {
    EditError::Io {
        display: path.display().to_string(),
        path: path.to_path_buf(),
        source,
    }
}

impl DiskWriter {
    /// Record and perform one request; the text that landed.
    fn write(&self, request: &WriteRequest<'_>) -> Result<String, EditError> {
        let (op, before_raw, target, content) = match request.op {
            WriteOp::Update {
                before_raw,
                content,
            } => ("update", Some(before_raw), request.absolute, Some(content)),
            WriteOp::Delete { before_raw } => ("delete", Some(before_raw), request.absolute, None),
            WriteOp::Move {
                before_raw,
                destination,
                content,
                ..
            } => ("move", Some(before_raw), destination, Some(content)),
        };
        self.requests
            .lock()
            .expect("writer lock")
            .push(RecordedWrite {
                absolute: request.absolute.to_path_buf(),
                op,
                before_raw: before_raw.map(str::to_owned),
            });
        let Some(content) = content else {
            std::fs::remove_file(request.absolute).map_err(|e| io_error(request.absolute, e))?;
            return Ok(String::new());
        };
        let written = self.rewrite.clone().unwrap_or_else(|| content.to_owned());
        if let Some(parent) = target.parent() {
            std::fs::create_dir_all(parent).map_err(|e| io_error(parent, e))?;
        }
        std::fs::write(target, &written).map_err(|e| io_error(target, e))?;
        if target != request.absolute {
            std::fs::remove_file(request.absolute).map_err(|e| io_error(request.absolute, e))?;
        }
        Ok(written)
    }
}

impl EditWriter for DiskWriter {
    fn write_all(&self, requests: &[WriteRequest<'_>]) -> Result<Vec<Published>, EditError> {
        let mut published = Vec::with_capacity(requests.len());
        for request in requests {
            match self.write(request) {
                Ok(written) => published.push(Published::Landed {
                    written,
                    warning: None,
                }),
                Err(error) => {
                    published.push(Published::Failed(error));
                    break;
                }
            }
        }
        Ok(published)
    }
}

/// Temp workspace + store for one case.
pub struct Workspace {
    _dir: tempfile::TempDir,
    pub cwd: PathBuf,
    pub store: EditStore,
    pub enforce_seen_lines: bool,
}

impl Workspace {
    pub fn new() -> Self {
        let dir = tempfile::tempdir().expect("tempdir");
        let cwd = dir.path().canonicalize().expect("canonical tempdir");
        Self {
            _dir: dir,
            cwd,
            store: EditStore::new(),
            enforce_seen_lines: false,
        }
    }

    pub fn write(&self, rel: &str, text: &str) -> PathBuf {
        let path = self.cwd.join(rel);
        if let Some(parent) = path.parent() {
            std::fs::create_dir_all(parent).expect("mkdir");
        }
        std::fs::write(&path, text).expect("write fixture file");
        path
    }

    pub fn read(&self, rel: &str) -> Option<String> {
        std::fs::read_to_string(self.cwd.join(rel)).ok()
    }

    /// Record a snapshot (LF-normalized) as a read would, and return its tag.
    pub fn snapshot(&self, rel: &str, text: &str, seen: Option<&[u32]>) -> String {
        let key = eukhe_types::path_policy::real_path(&self.cwd.join(rel));
        self.store.record(&key, &lf_text(text), seen)
    }

    pub fn apply(&self, input: &str, writer: &DiskWriter) -> Result<HashlineOutcome, EditError> {
        let options = HashlineOptions {
            cwd: &self.cwd,
            home: None,
            enforce_seen_lines: self.enforce_seen_lines,
        };
        apply_hashline(input, &options, &self.store, writer)
    }
}

fn expect_matches(actual: &str, pattern: &str) -> bool {
    if let Some(rest) = pattern.strip_prefix('^') {
        regex::Regex::new(&format!("^{rest}"))
            .expect("valid expect regex")
            .is_match(actual)
    } else {
        actual.contains(pattern)
    }
}

fn substitute_tags(input: &str, tags: &[(String, String)]) -> String {
    let mut input = input.to_owned();
    for (path, tag) in tags {
        input = input.replace(&format!("{{{{tag:{path}}}}}"), tag);
    }
    input
}

/// Run every case of a session-level fixture file.
pub fn run_fixture(name: &str) {
    let path = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("tests/fixtures/hashline")
        .join(name);
    let text = std::fs::read_to_string(&path)
        .unwrap_or_else(|e| panic!("read fixture {}: {e}", path.display()));
    let root: Value = serde_json::from_str(&text)
        .unwrap_or_else(|e| panic!("parse fixture {}: {e}", path.display()));
    let cases = root["cases"].as_array().expect("fixture has cases");
    let failures: Vec<String> = cases
        .iter()
        .filter_map(|case| {
            let name = case["name"].as_str().expect("case name");
            run_case(case)
                .err()
                .map(|message| format!("[{name}] {message}"))
        })
        .collect();
    assert!(
        failures.is_empty(),
        "{} case(s) failed in {}:\n{}",
        failures.len(),
        path.display(),
        failures.join("\n\n")
    );
}

fn run_case(case: &Value) -> Result<(), String> {
    let mut ws = Workspace::new();
    if let Some(enforce) = case["policy"]["enforceSeenLines"].as_bool() {
        ws.enforce_seen_lines = enforce;
    }
    for (rel, content) in case["files"].as_object().into_iter().flatten() {
        ws.write(rel, content.as_str().expect("file content string"));
    }
    let mut tags = Vec::new();
    for snap in case["snapshots"].as_array().into_iter().flatten() {
        let rel = snap["path"].as_str().expect("snapshot path");
        let text = snap["text"]
            .as_str()
            .map(str::to_owned)
            .or_else(|| ws.read(rel))
            .expect("snapshot text or existing file");
        let seen: Option<Vec<u32>> = snap["seenLines"].as_array().map(|lines| {
            lines
                .iter()
                .map(|line| u32::try_from(line.as_u64().expect("line")).expect("u32 line"))
                .collect()
        });
        let tag = ws.snapshot(rel, &text, seen.as_deref());
        tags.push((rel.to_owned(), tag));
    }
    let input = case["args"]["input"].as_str().expect("args.input");
    let writer = DiskWriter::default();
    let outcome = ws.apply(&substitute_tags(input, &tags), &writer);

    let expect = &case["expect"];
    let mut problems = Vec::new();
    match (&outcome, expect["error"].as_str()) {
        (Err(err), Some(pattern)) => {
            let actual = err.to_string();
            if !expect_matches(&actual, pattern) {
                problems.push(format!(
                    "error mismatch\n  expected: {pattern}\n  actual:   {actual}"
                ));
            }
        }
        (Err(err), None) => problems.push(format!("unexpected error: {err}")),
        (Ok(_), Some(pattern)) => {
            problems.push(format!("expected error {pattern:?} but apply succeeded"));
        }
        (Ok(_), None) => {}
    }
    if let Ok(outcome) = &outcome {
        if let Some(text) = expect["text"].as_str() {
            if outcome.text != text {
                problems.push(format!(
                    "text mismatch\n  expected: {text:?}\n  actual:   {:?}",
                    outcome.text
                ));
            }
        }
        for part in expect["textContains"].as_array().into_iter().flatten() {
            let part = part.as_str().expect("textContains string");
            if !expect_matches(&outcome.text, part) {
                problems.push(format!(
                    "text missing {part:?}\n  actual: {:?}",
                    outcome.text
                ));
            }
        }
    }
    for (rel, content) in expect["files"].as_object().into_iter().flatten() {
        let expected = content.as_str().expect("expected file string");
        match ws.read(rel) {
            Some(actual) if actual == expected => {}
            Some(actual) => problems.push(format!(
                "file {rel} mismatch\n  expected: {expected:?}\n  actual:   {actual:?}"
            )),
            None => problems.push(format!("file {rel} missing after apply")),
        }
    }
    for rel in expect["deleted"].as_array().into_iter().flatten() {
        let rel = rel.as_str().expect("deleted path");
        if ws.cwd.join(rel).exists() {
            problems.push(format!("file {rel} should have been deleted"));
        }
    }
    if let Some(writes) = expect["writes"].as_u64() {
        let actual = writer.writes() as u64;
        if actual != writes {
            problems.push(format!("expected {writes} writes, got {actual}"));
        }
    }
    if problems.is_empty() {
        Ok(())
    } else {
        Err(problems.join("\n"))
    }
}
