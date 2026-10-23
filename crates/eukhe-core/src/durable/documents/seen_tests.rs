//! The seen lines of a bounded read, end to end: the wire `read`
//! ([`perform`], then [`bounded`], which marks seen only the rows outside
//! the cut) and then `edit`. The guard's decision is the compiled model of
//! `bend/doc_seen.bend` (its laws are in `laws/doc_seen.bend`);
//! these tests pin the glue around it: which rows a cut read marks, and that
//! the store keeps a reveal for the retry.

use std::path::Path;
use std::sync::Arc;

use eukhe_chord::context::BACKGROUND_CONTEXT;
use eukhe_durable::harness::types::OutputRetain;
use eukhe_durable::harness::{OutputLimits, Truncation};
use serde_json::json;

use super::contract::Function;
use super::requests::{perform, Performed};
use super::tool::bounded;
use super::DocumentsHost;
use crate::durable::bounded_output::BoundedOutput;
use crate::resources::LoadedResources;

const FILE: &str = "long.txt";
const LINES: u64 = 2000;

fn host(dir: &Path) -> Arc<DocumentsHost> {
    Arc::new(DocumentsHost {
        documents: eukhe_docs::Documents::new(dir.join("locks"), None),
        workspace: dir.to_path_buf(),
        resources: Arc::new(LoadedResources::default()),
        memory: None,
        deps: std::sync::Weak::new(),
        // The gate is not these tests' subject: the user approves every
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

/// What an edit did.
#[derive(Debug, PartialEq, Eq)]
enum Outcome {
    Applied,
    Unseen,
}

/// A long file after one bounded read that cut its middle.
struct Session {
    dir: tempfile::TempDir,
    host: Arc<DocumentsHost>,
    content: String,
    tag: String,
    /// The last row shown before the cut and the first row after it.
    edges: [u64; 2],
}

impl Session {
    async fn read() -> Self {
        let dir = tempfile::tempdir().expect("temp dir");
        let host = host(dir.path());
        let mut content = (1..=LINES)
            .map(|n| format!("value {n}"))
            .collect::<Vec<_>>()
            .join("\n");
        content.push('\n');
        std::fs::write(dir.path().join(FILE), &content).expect("file");
        let read = call(&host, dir.path(), Function::Read, json!({ "path": FILE }))
            .await
            .expect("read");
        let limits = OutputLimits {
            max_bytes: 40_000,
            max_lines: 100,
            retain: OutputRetain::Tail,
        };
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
            dir,
            host,
            content,
            edges,
        }
    }

    /// Replace the lines `first..=last` with one line, with the tag of the
    /// read; an edit that applies is undone on disk, so the tag stays live.
    async fn edit(&self, first: u64, last: u64) -> Outcome {
        let input = format!(
            "[{FILE}#{}]\nPUT {first}.={last}:\n+changed {first}",
            self.tag
        );
        let dir = self.dir.path();
        match call(&self.host, dir, Function::Edit, json!({ "input": input })).await {
            Ok(_) => {
                std::fs::write(dir.join(FILE), &self.content).expect("restore");
                Outcome::Applied
            }
            Err(message) if message.contains("never displayed") => Outcome::Unseen,
            Err(message) => panic!("edit {first}-{last} failed: {message}"),
        }
    }
}

#[tokio::test(flavor = "multi_thread")]
async fn a_cut_read_marks_seen_only_the_rows_it_shows_and_a_reveal_lets_the_retry_apply() {
    let session = Session::read().await;
    let [shown, after] = session.edges;
    assert_eq!(session.edit(shown, shown).await, Outcome::Applied);
    assert_eq!(session.edit(shown + 1, shown + 1).await, Outcome::Unseen);
    assert_eq!(session.edit(shown + 1, shown + 1).await, Outcome::Applied);
    assert_eq!(session.edit(after - 1, after).await, Outcome::Unseen);
    assert_eq!(session.edit(after - 1, after).await, Outcome::Applied);
}

/// Four edits of shown lines apply, so the store drops the read's snapshot;
/// then an edit of a line in the cut middle is still rejected (with no
/// snapshot no line is seen) and its retry applies.
#[tokio::test(flavor = "multi_thread")]
async fn an_evicted_snapshot_sees_no_line_and_a_reveal_still_lets_the_retry_apply() {
    let session = Session::read().await;
    for line in 1..=4 {
        assert_eq!(session.edit(line, line).await, Outcome::Applied);
    }
    let middle = session.edges[0].midpoint(session.edges[1]);
    assert_eq!(session.edit(middle, middle).await, Outcome::Unseen);
    assert_eq!(session.edit(middle, middle).await, Outcome::Applied);
}
