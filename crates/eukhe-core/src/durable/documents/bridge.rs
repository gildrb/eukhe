//! The bridge between the seen-line guard of the documents tools (the
//! wire `read`: [`perform`], then [`bounded`], which marks seen only the
//! rows that are outside the cut; then `edit`) and its Bend model
//! (`bend/doc_seen.bend`, whose laws `PROOF.bend` proves): both run the
//! same scenarios and must print the same transcript, byte for byte
//! (`bend/bridge_doc_seen.bend` documents the events).
//!
//! A scenario reads a long file through small output limits, so the
//! output keeps a head and a tail and cuts the middle. Then it edits with
//! the tag of the read (after an applied edit the test puts the file
//! back, so that tag stays live): at random anchors, or, in one scenario,
//! after the store dropped the read's snapshot. For each anchor the events
//! say whether its row `N:TEXT` is in the text the read returned; the test
//! finds this in the text, not from the implementation.
//!
//! [`compare`] runs it (and skips without `bend`, unless
//! `EUKHE_REQUIRE_BEND` is set).

use std::collections::HashSet;
use std::fmt::Write as _;
use std::path::Path;
use std::sync::Arc;

use eukhe_chord::context::BACKGROUND_CONTEXT;
use eukhe_durable::harness::types::OutputRetain;
use eukhe_durable::harness::{OutputLimits, Truncation};
use eukhe_durable::testing::bridge::{compare, Rng, Scenario};
use serde_json::json;

use super::contract::Function;
use super::requests::{perform, Performed};
use super::tool::bounded;
use super::DocumentsHost;
use crate::durable::bounded_output::BoundedOutput;
use crate::resources::LoadedResources;

const FILE: &str = "long.txt";

fn host(dir: &Path) -> Arc<DocumentsHost> {
    Arc::new(DocumentsHost {
        documents: eukhe_docs::Documents::new(dir.join("locks"), None),
        workspace: dir.to_path_buf(),
        resources: Arc::new(LoadedResources::default()),
        memory: None,
        deps: std::sync::Weak::new(),
        // The gate is not this bridge's subject: the user approves every
        // access that asks.
        gate: super::GateInputs {
            agent_dir: dir.join("agent"),
            settings: Arc::new(crate::durable::EukheSettings::new(
                dir.to_path_buf(),
                dir.join("agent"),
            )),
            sink: Some(Arc::new(|_| {
                Box::pin(async { eukhe_types::shell::ShellAnswer::Approve })
                    as futures::future::BoxFuture<'static, _>
            })),
        },
    })
}

/// `function` with `args` in `dir`: the performed call, or the rejection
/// message.
async fn call(
    host: &Arc<DocumentsHost>,
    dir: &Path,
    function: Function,
    args: serde_json::Value,
) -> Result<Performed, String> {
    let serde_json::Value::Object(args) = args else {
        panic!("arguments are an object");
    };
    perform(
        host,
        function,
        dir.to_path_buf(),
        dir,
        args,
        None,
        &BACKGROUND_CONTEXT,
    )
    .await
    .expect("worker")
    .map_err(|rejection| rejection.message)
}

/// A long file after one bounded read, and the events and transcript of
/// the edits on it so far.
struct Session {
    dir: tempfile::TempDir,
    host: Arc<DocumentsHost>,
    content: String,
    rows: Vec<String>,
    tag: String,
    /// The lines of the text the read returned.
    shown: HashSet<String>,
    /// The last row shown before the cut and the first row after it.
    edges: [u64; 2],
    events: String,
    transcript: String,
    /// The edits that applied.
    landed: usize,
}

impl Session {
    /// Read a file of `count` lines through `limits`, which cut it.
    async fn read(count: u64, limits: OutputLimits, rng: &mut Rng) -> Self {
        let dir = tempfile::tempdir().expect("temp dir");
        let host = host(dir.path());
        let rows: Vec<String> = (1..=count)
            .map(|n| format!("value {n} {}", rng.below(1000)))
            .collect();
        let mut content = rows.join("\n");
        content.push('\n');
        std::fs::write(dir.path().join(FILE), &content).expect("file");
        let read = call(&host, dir.path(), Function::Read, json!({ "path": FILE }))
            .await
            .expect("read");
        let output = BoundedOutput::in_session(None, "t", Truncation::On(limits));
        let (text, diagnostic) = bounded(&host.documents, &read.done, output);
        assert!(diagnostic.is_some(), "the read is cut");
        let numbers: Vec<u64> = text
            .lines()
            .filter_map(|line| line.split_once(':')?.0.parse().ok())
            .collect();
        let edges = numbers
            .windows(2)
            .find(|pair| pair[1] > pair[0] + 1)
            .map(|pair| [pair[0], pair[1]])
            .expect("a gap in the shown rows");
        Self {
            tag: eukhe_docs::file_hash(&content),
            shown: text.lines().map(str::to_owned).collect(),
            edges,
            dir,
            host,
            content,
            rows,
            events: String::new(),
            transcript: String::new(),
            landed: 0,
        }
    }

    /// Whether the row of each line `first..=last` is in the text the read
    /// returned.
    fn show(&mut self, first: u64, last: u64) {
        for line in first..=last {
            let row = &self.rows[usize::try_from(line - 1).expect("line")];
            let shown = self.shown.contains(&format!("{line}:{row}"));
            let _ = writeln!(self.events, "v {line} {}", u8::from(shown));
        }
    }

    /// Replace the lines `first..=last` with one line, with the tag of the
    /// read; an edit that applies is undone on disk, so the tag stays live.
    async fn edit(&mut self, first: u64, last: u64) {
        let _ = writeln!(self.events, "e {first} {last}");
        let input = format!(
            "[{FILE}#{}]\nPUT {first}.={last}:\n+changed {first}",
            self.tag
        );
        let dir = self.dir.path();
        match call(&self.host, dir, Function::Edit, json!({ "input": input })).await {
            Ok(_) => {
                self.transcript.push_str("ok\n");
                self.landed += 1;
                std::fs::write(dir.join(FILE), &self.content).expect("restore");
            }
            Err(message) if message.contains("never displayed") => {
                self.transcript.push_str("unseen\n");
            }
            Err(message) => panic!("edit {first}-{last} failed: {message}"),
        }
    }

    fn scenario(self, name: String) -> Scenario {
        Scenario {
            name,
            events: self.events,
            transcript: self.transcript,
        }
    }
}

/// Edits at random anchors: mostly in the cut middle, some in the head or
/// the tail, some ranges, some longer than one rejection shows whole, some
/// retried as they are. It stops after three applied edits: the store
/// keeps four versions of a file, so the read's snapshot stays.
async fn random_scenario(at: usize, rng: &mut Rng) -> Scenario {
    let count = rng.range(1000, 4000);
    let limits = OutputLimits {
        max_bytes: usize::try_from(rng.range(2_000, 40_000)).expect("bytes"),
        max_lines: usize::try_from(rng.range(20, 600)).expect("lines"),
        retain: OutputRetain::Tail,
    };
    let mut session = Session::read(count, limits, rng).await;
    for _ in 0..rng.range(5, 25) {
        let first = match rng.below(10) {
            // The head or the tail, which the read most likely showed.
            0 => rng.range(1, 10),
            1 => count - rng.below(10),
            // A row at an edge of the cut, or next to it.
            2 | 3 => {
                let edge = session.edges[usize::from(rng.chance(50))];
                (edge + rng.below(3)).saturating_sub(1).clamp(1, count)
            }
            _ => rng.range(1, count),
        };
        let length = match rng.below(10) {
            0 => rng.range(41, 60),
            1 | 2 => rng.range(2, 4),
            _ => 1,
        };
        let last = (first + length - 1).min(count);
        session.show(first, last);
        for _ in 0..rng.range(1, 2) {
            session.edit(first, last).await;
        }
        if session.landed >= 3 {
            break;
        }
    }
    session.scenario(format!("seen {at}"))
}

/// Four edits of head lines apply, so the store drops the read's
/// snapshot; then an edit of a line in the cut middle is still rejected
/// (with no snapshot, no line is seen), and its retry applies.
async fn evicted_scenario(rng: &mut Rng) -> Scenario {
    let limits = OutputLimits {
        max_bytes: 40_000,
        max_lines: 100,
        retain: OutputRetain::Tail,
    };
    let mut session = Session::read(2000, limits, rng).await;
    for line in 1..=4 {
        session.show(line, line);
        session.edit(line, line).await;
    }
    session.show(1000, 1000);
    session.edit(1000, 1000).await;
    session.edit(1000, 1000).await;
    session.scenario("evicted".to_owned())
}

#[tokio::test(flavor = "multi_thread")]
async fn edits_apply_only_on_seen_lines_as_their_model() {
    let mut rng = Rng(0x9e37_79b9_7f4a_7c15);
    let mut scenarios = vec![evicted_scenario(&mut rng).await];
    for at in 0..30 {
        scenarios.push(random_scenario(at, &mut rng).await);
    }
    compare("bend/bridge_doc_seen.bend", scenarios);
}
