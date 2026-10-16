//! Cross-implementation check against the TS package (no TS test file).
//!
//! `fixtures/storage_cross` was written by `@earendil-works/pi-durable` 1.1
//! (`main` at `42a3497d0`):
//! `trace.json` records a representative commit history (mints, commit
//! batches, sequences) and a read plan with each result as TS `JSON.stringify`
//! text; `jsonl/` holds that history as written by the TS `JsonlStorage`
//! after a close and a reopen. Rust must read the TS files identically and
//! write byte-identical JSONL files.

use std::path::{Path, PathBuf};
use std::sync::Arc;

use eukhe_chord::context::{Context, BACKGROUND_CONTEXT};
use eukhe_chord::json::{from_json, to_json, JsonValue};
use eukhe_durable::errors::StorageError;
use eukhe_durable::storage::jsonl::{open_native_jsonl_storage, JsonlStorageOptions};
use eukhe_durable::storage::MemoryStorage;
use eukhe_durable::types::{Cursor, Storage, StorageWrite};
use serde::de::DeserializeOwned;
use serde::Serialize;

fn cx() -> &'static Context {
    &BACKGROUND_CONTEXT
}

fn fixtures() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/storage_cross")
}

fn trace() -> JsonValue {
    JsonValue::parse(&std::fs::read_to_string(fixtures().join("trace.json")).unwrap()).unwrap()
}

#[track_caller]
fn arg<T: DeserializeOwned>(args: &JsonValue, index: usize) -> T {
    from_json(&args[index]).unwrap_or_else(|error| panic!("argument {index} of {args}: {error}"))
}

fn cursor(args: &JsonValue, index: usize) -> Option<Cursor> {
    arg(args, index)
}

fn text<T: Serialize>(result: Result<T, StorageError>) -> Result<String, String> {
    result
        .map(|value| to_json(&value).unwrap().to_string())
        .map_err(|error| error.to_string())
}

async fn call(storage: &dyn Storage, method: &str, args: &JsonValue) -> Result<String, String> {
    let cx = cx();
    match method {
        "conversation" => text(storage.conversation(arg(args, 0), cx).await),
        "scanConversations" => text(
            storage
                .scan_conversations(&arg(args, 0), arg(args, 1), cursor(args, 2).as_ref(), cx)
                .await,
        ),
        "entry" if args.as_array().unwrap().len() == 1 => {
            text(storage.entry(arg(args, 0), cx).await)
        }
        "entry" => text(storage.entry_in(arg(args, 0), arg(args, 1), cx).await),
        "findLatestHeadMarker" => text(
            storage
                .find_latest_head_marker(arg(args, 0), arg(args, 1), cx)
                .await,
        ),
        "scanEntries" => text(
            storage
                .scan_entries(&arg(args, 0), arg(args, 1), cursor(args, 2).as_ref(), cx)
                .await,
        ),
        "task" => text(storage.task(arg(args, 0), cx).await),
        "scanTasks" => text(
            storage
                .scan_tasks(&arg(args, 0), arg(args, 1), cursor(args, 2).as_ref(), cx)
                .await,
        ),
        "submission" => text(storage.submission(arg(args, 0), cx).await),
        "scanSubmissions" => text(
            storage
                .scan_submissions(&arg(args, 0), arg(args, 1), cursor(args, 2).as_ref(), cx)
                .await,
        ),
        "submissionByRequest" => {
            let request: String = arg(args, 1);
            text(
                storage
                    .submission_by_request(arg(args, 0), &request, cx)
                    .await,
            )
        }
        "findDocument" => text(storage.find_document(&arg(args, 0), arg(args, 1), cx).await),
        "document" => text(storage.document(arg(args, 0), arg(args, 1), cx).await),
        "scanDocuments" => text(
            storage
                .scan_documents(&arg(args, 0), arg(args, 1), cursor(args, 2).as_ref(), cx)
                .await,
        ),
        other => panic!("unexpected traced method {other}"),
    }
}

/// Commit the traced history, checking every minted ID and sequence.
async fn replay_history(storage: &dyn Storage) {
    for step in trace()["history"].as_array().unwrap() {
        match step["op"].as_str().unwrap() {
            "mint" => assert_eq!(
                storage.mint_id().await.unwrap(),
                step["result"].as_u64().unwrap()
            ),
            "commit" => {
                let writes: Vec<StorageWrite> = from_json(&step["writes"]).unwrap();
                let seq = storage.commit(&writes, cx()).await.unwrap();
                assert_eq!(
                    seq.get(),
                    step["result"].as_u64().unwrap(),
                    "{}",
                    step["writes"]
                );
            }
            other => panic!("unexpected history step {other}"),
        }
    }
}

/// Run the traced read plan; every result must equal the TS text exactly.
async fn replay_reads(storage: &dyn Storage) {
    let mut mismatches = Vec::new();
    for step in trace()["reads"].as_array().unwrap() {
        let method = step["method"].as_str().unwrap();
        let actual = call(storage, method, &step["args"]).await;
        let expected = match step.get("error") {
            Some(error) => Err(error.as_str().unwrap().to_owned()),
            None => Ok(step["result"].as_str().unwrap().to_owned()),
        };
        if actual != expected {
            mismatches.push(format!(
                "{method}{}:\n  rust {actual:?}\n  ts   {expected:?}",
                step["args"]
            ));
        }
    }
    assert!(
        mismatches.is_empty(),
        "{} read(s) differ:\n{}",
        mismatches.len(),
        mismatches.join("\n")
    );
}

fn copy_dir(source: &Path, target: &Path) {
    std::fs::create_dir_all(target).unwrap();
    for entry in std::fs::read_dir(source).unwrap() {
        let entry = entry.unwrap();
        std::fs::copy(entry.path(), target.join(entry.file_name())).unwrap();
    }
}

fn path_str(path: &Path) -> &str {
    path.to_str().unwrap()
}

async fn open_jsonl(directory: &Path) -> Arc<dyn Storage> {
    Arc::new(
        open_native_jsonl_storage(path_str(directory), cx(), JsonlStorageOptions::default())
            .await
            .unwrap(),
    )
}

#[tokio::test]
async fn memory_storage_reads_the_ts_history_identically() {
    let storage = MemoryStorage::new();
    replay_history(&storage).await;
    replay_reads(&storage).await;
}

#[tokio::test]
async fn reads_ts_written_jsonl_identically() {
    let temp = tempfile::tempdir().unwrap();
    let directory = temp.path().join("jsonl");
    copy_dir(&fixtures().join("jsonl"), &directory);
    let storage = open_jsonl(&directory).await;
    replay_reads(&*storage).await;
    // The minted-but-uncommitted ID 17 is not persisted.
    assert_eq!(storage.mint_id().await.unwrap(), 17);
    storage.close(cx()).await.unwrap();
}

fn files(directory: &Path) -> Vec<(String, Vec<u8>)> {
    let mut files: Vec<(String, Vec<u8>)> = std::fs::read_dir(directory)
        .unwrap()
        .map(|entry| {
            let entry = entry.unwrap();
            (
                entry.file_name().into_string().unwrap(),
                std::fs::read(entry.path()).unwrap(),
            )
        })
        .collect();
    files.sort();
    files
}

#[tokio::test]
async fn writes_jsonl_files_byte_identical_to_ts() {
    let temp = tempfile::tempdir().unwrap();
    let directory = temp.path().join("jsonl");
    let storage = open_jsonl(&directory).await;
    replay_history(&*storage).await;
    storage.close(cx()).await.unwrap();
    // The TS fixture was reopened (recovery may reclaim) and closed once more.
    open_jsonl(&directory).await.close(cx()).await.unwrap();
    let expected = files(&fixtures().join("jsonl"));
    let actual = files(&directory);
    let names = |files: &[(String, Vec<u8>)]| {
        files
            .iter()
            .map(|(name, _)| name.clone())
            .collect::<Vec<_>>()
    };
    assert_eq!(names(&actual), names(&expected));
    for ((name, actual), (_, expected)) in actual.iter().zip(&expected) {
        assert_eq!(
            String::from_utf8_lossy(actual),
            String::from_utf8_lossy(expected),
            "{name}"
        );
    }
}
