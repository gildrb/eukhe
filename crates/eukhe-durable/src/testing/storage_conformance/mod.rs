//! Port of `testing/storage-conformance.ts`: runner-independent cases every
//! [`Storage`] backend must pass.
//!
//! Records and queries are written as the TS object literals (JSON) and
//! converted with `from_json`; results are compared through `to_json`, so a
//! case reads like its TS original. `toEqual` is JSON equality, `toMatchObject`
//! is [`assert_match_object`], and `rejects.toThrow(text)` is [`rejects`].

mod documents;
mod progress;
mod records;
mod tasks;

use std::future::Future;
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::Arc;
use std::time::Duration;

use eukhe_chord::context::{Context, BACKGROUND_CONTEXT};
use eukhe_chord::json::{from_json, to_json, JsonValue};
use futures::future::BoxFuture;
use serde::de::DeserializeOwned;
use serde::Serialize;
use serde_json::json;

use super::types::{StorageConformanceCase, StorageConformanceOptions, StorageTest};
use crate::errors::StorageError;
use crate::types::{Storage, StorageWrite};

/// How long a case may go without a completed storage call (Vitest's
/// default per-test timeout).
const STALL_TIMEOUT_MS: u64 = 5_000;

/// The reserved root conversation ID (`ROOT_CONVERSATION_ID`) as JSON.
const ROOT: u64 = 1;

fn cx() -> &'static Context {
    &BACKGROUND_CONTEXT
}

/// `value[a][b]…` for in-place (copy-on-write) mutation; array segments are
/// decimal indexes.
#[track_caller]
fn at<'a>(value: &'a mut JsonValue, path: &[&str]) -> &'a mut JsonValue {
    path.iter().fold(value, |value, segment| {
        let found = if value.is_array() {
            let index: usize = segment.parse().expect("an array index");
            value.as_array_mut().and_then(|array| array.get_mut(index))
        } else {
            value
                .as_object_mut()
                .and_then(|object| object.get_mut(segment))
        };
        found.expect("an existing JSON path")
    })
}

/// A JSON literal as a [`JsonValue`].
fn v(value: impl Into<serde_json::Value>) -> JsonValue {
    JsonValue::from(value.into())
}

/// A typed record, query, or ID from its TS JSON literal.
#[track_caller]
fn q<T: DeserializeOwned>(value: impl Into<JsonValue>) -> T {
    let value = value.into();
    match from_json(&value) {
        Ok(typed) => typed,
        Err(error) => panic!("invalid conformance literal {value}: {error}"),
    }
}

/// A typed ID from its number.
#[track_caller]
fn id<T: DeserializeOwned>(number: u64) -> T {
    q(json!(number))
}

/// The JSON a record serializes to.
#[track_caller]
fn j<T: Serialize + ?Sized>(value: &T) -> JsonValue {
    match to_json(value) {
        Ok(json) => json,
        Err(error) => panic!("unserializable storage result: {error}"),
    }
}

/// A numeric ID or sequence result as a number.
#[track_caller]
fn n<T: Serialize + ?Sized>(value: &T) -> u64 {
    let json = j(value);
    match json.as_u64() {
        Some(number) => number,
        None => panic!("expected a numeric value, got {json}"),
    }
}

/// An awaited storage call that must succeed.
#[track_caller]
fn ok<T>(result: Result<T, StorageError>) -> T {
    match result {
        Ok(value) => value,
        Err(error) => panic!("unexpected storage failure: {error}"),
    }
}

/// `await expect(operation).rejects.toThrow(includes)`; returns the error.
async fn rejects<T, F>(operation: F, includes: &str) -> StorageError
where
    F: Future<Output = Result<T, StorageError>>,
{
    match operation.await {
        Ok(_) => panic!("expected a rejection containing {includes:?}, but it resolved"),
        Err(error) => {
            let message = error.to_string();
            assert!(
                message.contains(includes),
                "expected a rejection containing {includes:?}, got {message:?}"
            );
            error
        }
    }
}

/// Jest `toMatchObject`: every expected object property matches recursively;
/// arrays match element-wise with equal length; other values are equal.
fn matches_object(actual: &JsonValue, expected: &JsonValue) -> bool {
    match (actual, expected) {
        (JsonValue::Object(actual), JsonValue::Object(expected)) => {
            expected.iter().all(|(key, expected)| {
                actual
                    .get(key)
                    .is_some_and(|actual| matches_object(actual, expected))
            })
        }
        (JsonValue::Array(actual), JsonValue::Array(expected)) => {
            actual.len() == expected.len()
                && actual
                    .iter()
                    .zip(expected.iter())
                    .all(|(actual, expected)| matches_object(actual, expected))
        }
        _ => actual == expected,
    }
}

#[track_caller]
fn assert_match_object(actual: &JsonValue, expected: &JsonValue) {
    assert!(
        matches_object(actual, expected),
        "expected {actual} to match object {expected}"
    );
}

/// `await storage.mintId()` as a number.
async fn mint(storage: &dyn Storage) -> u64 {
    ok(storage.mint_id().await)
}

/// `storage.commit(writes)` with the writes as TS literals; resolves to the
/// commit sequence as a number.
async fn commit(storage: &dyn Storage, writes: serde_json::Value) -> Result<u64, StorageError> {
    let writes: Vec<StorageWrite> = q(writes);
    storage.commit(&writes, cx()).await.map(|seq| n(&seq))
}

/// `createRoot`.
async fn create_root(storage: &dyn Storage) -> u64 {
    ok(commit(
        storage,
        json!([{ "type": "conversation", "value": { "id": ROOT } }]),
    )
    .await);
    ROOT
}

/// `pendingTask(id, conversationId)`.
fn pending_task(id: u64, conversation_id: u64) -> serde_json::Value {
    json!({
        "id": id,
        "conversationId": conversation_id,
        "kind": "test.task",
        "version": 1,
        "input": { "value": id },
        "state": { "status": "pending", "checkpoint": { "phase": "ready" } },
        "background": false,
        "abortRequested": false,
    })
}

/// `entry(id, conversationId, kind, extra)`.
fn entry(id: u64, conversation_id: u64, kind: &str, extra: serde_json::Value) -> serde_json::Value {
    with(
        json!({ "id": id, "conversationId": conversation_id, "kind": kind }),
        extra,
    )
}

/// `{ ...base, ...extra }`.
fn with(mut base: serde_json::Value, extra: serde_json::Value) -> serde_json::Value {
    if let (Some(base), serde_json::Value::Object(extra)) = (base.as_object_mut(), extra) {
        base.extend(extra);
    }
    base
}

/// `items.map(({ id }) => id)`.
fn ids<T: Serialize>(items: &[T]) -> JsonValue {
    items.iter().map(|item| j(item)["id"].clone()).collect()
}

/// Builds cases bound to one provider. `completed[i]` counts the storage
/// calls of case `list[i]` that completed (its [`progress::Progress`]
/// watchdog signal).
struct Cases {
    options: StorageConformanceOptions,
    list: Vec<StorageConformanceCase>,
    completed: Vec<Arc<AtomicU64>>,
}

impl Cases {
    fn case<F, Fut>(&mut self, name: &'static str, test: F)
    where
        F: Fn(Arc<dyn Storage>) -> Fut + Send + Sync + 'static,
        Fut: Future<Output = ()> + Send + 'static,
    {
        let with_storage = Arc::clone(&self.options.with_storage);
        let test = Arc::new(test);
        let completed = Arc::new(AtomicU64::new(0));
        self.completed.push(Arc::clone(&completed));
        self.list.push(StorageConformanceCase {
            name,
            run: Arc::new(move || {
                let test = Arc::clone(&test);
                let completed = Arc::clone(&completed);
                let body: StorageTest = Box::new(move |storage| {
                    Box::pin(test(Arc::new(progress::Progress::new(storage, completed))))
                });
                with_storage(body)
            }),
        });
    }

    fn all(options: StorageConformanceOptions) -> Self {
        let mut cases = Self {
            options,
            list: Vec::new(),
            completed: Vec::new(),
        };
        records::add_cases(&mut cases);
        tasks::add_cases(&mut cases);
        documents::add_cases(&mut cases);
        cases
    }
}

/// Creates runner-independent cases. The provider must call and await its
/// test exactly once per case with a fresh storage.
#[must_use]
pub fn create_storage_conformance(
    options: StorageConformanceOptions,
) -> Vec<StorageConformanceCase> {
    Cases::all(options).list
}

/// Run every case against `options.with_storage`, concurrently, the Rust
/// counterpart of `registerStorageConformance`. A case fails when no
/// storage call of it completes for 5 s (Vitest's default timeout). A fixed
/// budget for the whole case measured the disk instead: a case of 50
/// fsync-and-reopen commits takes 2.5 s on an idle disk and more than 5 s
/// under a parallel build's IO load.
///
/// # Panics
///
/// Panics after all cases ran when any failed or stalled, listing them under
/// `suite`.
pub async fn run_storage_conformance(suite: &str, options: StorageConformanceOptions) {
    let Cases {
        list, completed, ..
    } = Cases::all(options);
    let stall = Duration::from_millis(STALL_TIMEOUT_MS);
    let mut running: Vec<(&'static str, BoxFuture<'static, Result<(), String>>)> = Vec::new();
    for (case, completed) in list.iter().zip(completed) {
        let task = tokio::spawn(case.run());
        running.push((case.name, Box::pin(watch(task, completed, stall))));
    }
    let mut failures = Vec::new();
    for (name, outcome) in running {
        if let Err(message) = outcome.await {
            failures.push(format!("{suite} > {name}: {message}"));
        }
    }
    assert!(
        failures.is_empty(),
        "{} conformance case(s) failed:\n{}",
        failures.len(),
        failures.join("\n")
    );
}

/// Await one case; fail it (and abort it) once `stall` passes with no
/// storage call completed.
async fn watch(
    mut task: tokio::task::JoinHandle<()>,
    completed: Arc<AtomicU64>,
    stall: Duration,
) -> Result<(), String> {
    let mut seen = completed.load(Ordering::SeqCst);
    loop {
        match tokio::time::timeout(stall, &mut task).await {
            Ok(Ok(())) => return Ok(()),
            Ok(Err(error)) => return Err(panic_message(error)),
            Err(_) => {
                let now = completed.load(Ordering::SeqCst);
                if now == seen {
                    task.abort();
                    return Err(format!(
                        "stalled: no storage call completed for {} ms ({now} completed)",
                        stall.as_millis()
                    ));
                }
                seen = now;
            }
        }
    }
}

fn panic_message(error: tokio::task::JoinError) -> String {
    match error.try_into_panic() {
        Ok(panic) => panic
            .downcast_ref::<String>()
            .cloned()
            .or_else(|| panic.downcast_ref::<&str>().map(|text| (*text).to_owned()))
            .unwrap_or_else(|| "panicked".to_owned()),
        Err(error) => error.to_string(),
    }
}
