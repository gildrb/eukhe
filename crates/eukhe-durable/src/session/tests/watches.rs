//! Port of `test/session-watches.test.ts`.

use std::future::Future;
use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering};
use std::sync::{Arc, Mutex, PoisonError};

use eukhe_chord::context::{
    create_context_key, with_abort_signal, with_cancel, with_context_value, AbortController,
    Context, BACKGROUND_CONTEXT,
};
use eukhe_chord::delta::{apply_immutable, Op};
use eukhe_chord::json::JsonValue;
use futures::FutureExt;

use super::support::{
    context, document_changes, flush, json, open_test_session, ops_json, Deferred, TestSession,
};
use crate::documents::{DocDefinition, SessionDoc};
use crate::session::{
    ObservedDocumentValue, Ops, Session, WatchEnd, WatchListener, WatchListenerError,
};

const STATE_DOC: SessionDoc<JsonValue> = match SessionDoc::define(DocDefinition {
    kind: "watch.state",
    version: 1,
    initial: || json(r#"{"value":0,"items":["a","b"],"retained":{"label":"stable"}}"#),
    migrate: None,
    checkpoint_when: None,
}) {
    Ok(token) => token,
    Err(_) => panic!("valid definition"),
};

const OLD_DOC: SessionDoc<JsonValue> = match SessionDoc::define(DocDefinition {
    kind: "watch.migration",
    version: 1,
    initial: || json(r#"{"value":3}"#),
    migrate: None,
    checkpoint_when: None,
}) {
    Ok(token) => token,
    Err(_) => panic!("valid definition"),
};

const CURRENT_DOC: SessionDoc<JsonValue> = match SessionDoc::define(DocDefinition {
    kind: "watch.migration",
    version: 2,
    initial: || json(r#"{"value":0,"migrated":false}"#),
    migrate: Some(|value, _| {
        Ok(json(&format!(
            r#"{{"value":{},"migrated":true}}"#,
            value.get("value").cloned().unwrap_or_default()
        )))
    }),
    checkpoint_when: None,
}) {
    Ok(token) => token,
    Err(_) => panic!("valid definition"),
};

type Shared<T> = Arc<Mutex<T>>;

fn lock<T>(shared: &Shared<T>) -> std::sync::MutexGuard<'_, T> {
    shared.lock().unwrap_or_else(PoisonError::into_inner)
}

fn listener<F, Fut>(f: F) -> WatchListener<ObservedDocumentValue>
where
    F: Fn(ObservedDocumentValue, Ops, Context) -> Fut + Send + Sync + 'static,
    Fut: Future<Output = Result<(), WatchListenerError>> + Send + 'static,
{
    Arc::new(move |value, ops, cx| f(value, ops, cx).boxed())
}

fn noop() -> WatchListener<ObservedDocumentValue> {
    listener(|_, _, _| async { Ok(()) })
}

fn error(message: &str) -> Arc<std::io::Error> {
    Arc::new(std::io::Error::other(message.to_owned()))
}

/// `value?.value ?? -1`.
fn number(value: &ObservedDocumentValue) -> f64 {
    value
        .as_ref()
        .and_then(|object| object.get("value"))
        .and_then(JsonValue::as_f64)
        .unwrap_or(-1.0)
}

/// TS `toBe` on `Readonly<State> | null`.
fn same(left: &ObservedDocumentValue, right: &ObservedDocumentValue) -> bool {
    match (left, right) {
        (Some(left), Some(right)) => Arc::ptr_eq(left, right),
        (None, None) => true,
        _ => false,
    }
}

fn as_json(value: &ObservedDocumentValue) -> JsonValue {
    value.clone().map_or(JsonValue::Null, JsonValue::Object)
}

/// `[["r", value]]`.
fn root_replacement(value: &ObservedDocumentValue) -> JsonValue {
    JsonValue::Array(Arc::new(vec![JsonValue::Array(Arc::new(vec![
        JsonValue::from("r"),
        as_json(value),
    ]))]))
}

async fn set_value(session: &Session, value: i32) {
    session
        .commit(
            move |tx| async move {
                tx.doc(&STATE_DOC, ()).await?.set("value", value)?;
                Ok(())
            },
            context(),
        )
        .await
        .unwrap();
}

async fn retire(session: &Session) {
    session
        .commit(
            |tx| async move {
                tx.retire_doc(&STATE_DOC, ()).await?;
                Ok(())
            },
            context(),
        )
        .await
        .unwrap();
}

async fn create_state() -> TestSession {
    let test = open_test_session();
    test.session
        .commit(
            |tx| async move {
                tx.doc(&STATE_DOC, ()).await?;
                Ok(())
            },
            context(),
        )
        .await
        .unwrap();
    test
}

async fn watch(session: &Session) -> crate::session::DocumentWatch {
    session
        .watch_doc(&STATE_DOC, (), context())
        .await
        .unwrap()
        .unwrap()
}

#[tokio::test]
async fn never_creates_an_absent_document() {
    let TestSession {
        session, storage, ..
    } = open_test_session();
    let commits = storage.commit_count();
    assert!(session
        .watch_doc(&STATE_DOC, (), context())
        .await
        .unwrap()
        .is_none());
    assert_eq!(storage.commit_count(), commits);
    assert_eq!(storage.mint_count(), 0);
}

#[tokio::test]
async fn keeps_the_acquisition_revision_until_start_and_delivers_exact_committed_frames() {
    let TestSession {
        session,
        publications,
        ..
    } = create_state().await;
    let watch = watch(&session).await;
    let initial = watch.value();
    set_value(&session, 1).await;
    flush().await;
    let first_published = document_changes(&publications.last()).remove(0);
    set_value(&session, 2).await;
    flush().await;
    let second_published = document_changes(&publications.last()).remove(0);
    assert!(same(&watch.value(), &initial));

    let inline = Arc::new(AtomicBool::new(true));
    // Listener assertions are recorded and checked here: a panic inside the
    // spawned delivery would not fail the test.
    let violations = Arc::new(AtomicUsize::new(0));
    let deliveries: Shared<Vec<(ObservedDocumentValue, Ops)>> = Arc::default();
    {
        let (inline, violations, deliveries, observed) = (
            Arc::clone(&inline),
            Arc::clone(&violations),
            Arc::clone(&deliveries),
            watch.clone(),
        );
        watch
            .start(listener(move |value, ops, _| {
                if inline.load(Ordering::SeqCst) || !same(&observed.value(), &value) {
                    violations.fetch_add(1, Ordering::SeqCst);
                }
                lock(&deliveries).push((value, ops));
                async { Ok(()) }
            }))
            .unwrap();
    }
    inline.store(false, Ordering::SeqCst);
    assert_eq!(lock(&deliveries).len(), 0);
    flush().await;
    assert_eq!(violations.load(Ordering::SeqCst), 0);
    let deliveries = lock(&deliveries).clone();
    assert_eq!(
        deliveries
            .iter()
            .map(|(value, _)| number(value))
            .collect::<Vec<_>>(),
        vec![1.0, 2.0]
    );
    assert!(same(&deliveries[0].0, &first_published.value));
    assert!(Arc::ptr_eq(&deliveries[0].1, &first_published.ops));
    assert!(same(&deliveries[1].0, &second_published.value));
    assert!(Arc::ptr_eq(&deliveries[1].1, &second_published.ops));
    assert!((number(&initial) - 0.0).abs() < f64::EPSILON);
    watch.stop().await;
}

#[tokio::test]
async fn serializes_callbacks_and_buffers_exact_frames_committed_while_one_is_in_flight() {
    let TestSession { session, .. } = create_state().await;
    let watch = watch(&session).await;
    let entered = Deferred::new();
    let release = Deferred::new();
    let values: Shared<Vec<f64>> = Arc::default();
    let active = Arc::new(AtomicUsize::new(0));
    let max_active = Arc::new(AtomicUsize::new(0));
    {
        let (entered, release, values, active, max_active) = (
            entered.clone(),
            release.clone(),
            Arc::clone(&values),
            Arc::clone(&active),
            Arc::clone(&max_active),
        );
        watch
            .start(listener(move |value, _, _| {
                let now = active.fetch_add(1, Ordering::SeqCst) + 1;
                max_active.fetch_max(now, Ordering::SeqCst);
                let count = {
                    let mut values = lock(&values);
                    values.push(number(&value));
                    values.len()
                };
                let (entered, release, active) =
                    (entered.clone(), release.clone(), Arc::clone(&active));
                async move {
                    if count == 1 {
                        entered.resolve();
                        release.wait().await;
                    }
                    active.fetch_sub(1, Ordering::SeqCst);
                    Ok(())
                }
            }))
            .unwrap();
    }
    set_value(&session, 1).await;
    entered.wait().await;
    for value in 2..=20 {
        set_value(&session, value).await;
    }
    assert_eq!(*lock(&values), vec![1.0]);
    release.resolve();
    flush().await;
    assert_eq!(max_active.load(Ordering::SeqCst), 1);
    assert_eq!(*lock(&values), (1..=20).map(f64::from).collect::<Vec<_>>());
    watch.stop().await;
}

#[tokio::test]
async fn allows_a_listener_to_initiate_a_later_session_commit() {
    let TestSession { session, .. } = create_state().await;
    let watch = watch(&session).await;
    let completed = Deferred::new();
    let values: Shared<Vec<f64>> = Arc::default();
    {
        let (session, completed, values) =
            (session.clone(), completed.clone(), Arc::clone(&values));
        watch
            .start(listener(move |value, _, _| {
                let current = number(&value);
                lock(&values).push(current);
                let (session, completed) = (session.clone(), completed.clone());
                async move {
                    if (current - 1.0).abs() < f64::EPSILON {
                        set_value(&session, 2).await;
                    } else {
                        completed.resolve();
                    }
                    Ok(())
                }
            }))
            .unwrap();
    }
    set_value(&session, 1).await;
    completed.wait().await;
    assert_eq!(*lock(&values), vec![1.0, 2.0]);
    watch.stop().await;
}

#[tokio::test]
async fn collapses_101_pending_commits_to_one_root_replacement() {
    let TestSession { session, .. } = create_state().await;
    let watch = watch(&session).await;
    for value in 1..=101 {
        set_value(&session, value).await;
    }
    let deliveries: Shared<Vec<(f64, JsonValue)>> = Arc::default();
    {
        let deliveries = Arc::clone(&deliveries);
        watch
            .start(listener(move |value, ops, _| {
                lock(&deliveries).push((number(&value), ops_json(&ops)));
                async { Ok(()) }
            }))
            .unwrap();
    }
    flush().await;
    assert_eq!(
        *lock(&deliveries),
        vec![(101.0, root_replacement(&watch.value()))]
    );
    watch.stop().await;
}

#[tokio::test]
async fn never_folds_the_in_flight_frame_into_an_overflow_reset() {
    let TestSession { session, .. } = create_state().await;
    let watch = watch(&session).await;
    let entered = Deferred::new();
    let release = Deferred::new();
    let deliveries: Shared<Vec<(f64, JsonValue)>> = Arc::default();
    {
        let (entered, release, deliveries) =
            (entered.clone(), release.clone(), Arc::clone(&deliveries));
        watch
            .start(listener(move |value, ops, _| {
                let count = {
                    let mut deliveries = lock(&deliveries);
                    deliveries.push((number(&value), ops_json(&ops)));
                    deliveries.len()
                };
                let (entered, release) = (entered.clone(), release.clone());
                async move {
                    if count == 1 {
                        entered.resolve();
                        release.wait().await;
                    }
                    Ok(())
                }
            }))
            .unwrap();
    }
    set_value(&session, 1).await;
    entered.wait().await;
    for value in 2..=102 {
        set_value(&session, value).await;
    }
    release.resolve();
    flush().await;
    let deliveries = lock(&deliveries).clone();
    assert!((deliveries[0].0 - 1.0).abs() < f64::EPSILON);
    assert_eq!(deliveries[1], (102.0, root_replacement(&watch.value())));
    assert_eq!(deliveries.len(), 2);
    watch.stop().await;
}

#[tokio::test]
async fn folds_retirement_into_an_overflow_reset_and_then_closes() {
    let TestSession { session, .. } = create_state().await;
    let watch = watch(&session).await;
    for value in 1..=100 {
        set_value(&session, value).await;
    }
    retire(&session).await;
    let deliveries: Shared<Vec<(JsonValue, JsonValue)>> = Arc::default();
    {
        let deliveries = Arc::clone(&deliveries);
        watch
            .start(listener(move |value, ops, _| {
                lock(&deliveries).push((as_json(&value), ops_json(&ops)));
                async { Ok(()) }
            }))
            .unwrap();
    }
    assert_eq!(watch.closed().await, WatchEnd::Retired);
    assert_eq!(
        *lock(&deliveries),
        vec![(JsonValue::Null, root_replacement(&None))]
    );
}

#[tokio::test]
async fn delivers_replayable_structural_no_op_commits_instead_of_suppressing_them() {
    let TestSession { session, .. } = create_state().await;
    let watch = watch(&session).await;
    let initial = watch.value();
    session
        .commit(
            |tx| async move {
                let items = tx.doc(&STATE_DOC, ()).await?.child("items")?;
                let first = items.shift()?.expect("a first item");
                items.unshift([first])?;
                Ok(())
            },
            context(),
        )
        .await
        .unwrap();
    let newest = session.snapshot(&STATE_DOC, (), context()).await.unwrap();
    assert!(!same(&newest, &initial));
    assert_eq!(as_json(&newest), as_json(&initial));
    let violations = Arc::new(AtomicUsize::new(0));
    let batches: Shared<Vec<Ops>> = Arc::default();
    {
        let (newest, violations, batches) = (
            newest.clone(),
            Arc::clone(&violations),
            Arc::clone(&batches),
        );
        watch
            .start(listener(move |value, ops, _| {
                if !same(&value, &newest) {
                    violations.fetch_add(1, Ordering::SeqCst);
                }
                lock(&batches).push(ops);
                async { Ok(()) }
            }))
            .unwrap();
    }
    flush().await;
    assert_eq!(violations.load(Ordering::SeqCst), 0);
    let batches = lock(&batches).clone();
    assert_eq!(batches.len(), 1);
    assert!(!batches[0].is_empty());
    watch.stop().await;
}

#[tokio::test]
async fn preserves_commit_context_values_without_inheriting_producer_cancellation() {
    let TestSession { session, .. } = create_state().await;
    let watch = watch(&session).await;
    let key = create_context_key::<String>("watch-test");
    let parent_controller = AbortController::new();
    let commit_context = with_context_value(
        &key,
        "newest-commit".to_owned(),
        &with_abort_signal(&parent_controller.signal(), &BACKGROUND_CONTEXT),
    );
    let entered = Deferred::new();
    let release = Deferred::new();
    let delivery_context: Shared<Option<Context>> = Arc::default();
    {
        let (entered, release, delivery_context) = (
            entered.clone(),
            release.clone(),
            Arc::clone(&delivery_context),
        );
        watch
            .start(listener(move |_, _, delivered| {
                *lock(&delivery_context) = Some(delivered);
                entered.resolve();
                let release = release.clone();
                async move {
                    release.wait().await;
                    Ok(())
                }
            }))
            .unwrap();
    }
    session
        .commit(
            |tx| async move {
                tx.doc(&STATE_DOC, ()).await?.set("value", 1)?;
                Ok(())
            },
            &commit_context,
        )
        .await
        .unwrap();
    entered.wait().await;
    let delivered = lock(&delivery_context).clone().unwrap();
    assert_eq!(delivered.value(&key).as_deref(), Some("newest-commit"));
    assert!(delivered.abort_signal().is_none());
    parent_controller.abort(Some(error("caller finished")));
    let stopped = watch.stop();
    assert_eq!(stopped.await, WatchEnd::Stopped);
    assert!(delivered.abort_signal().is_none());
    release.resolve();
}

#[tokio::test]
async fn keeps_earlier_immutable_revisions_stable() {
    let TestSession { session, .. } = create_state().await;
    let watch = watch(&session).await;
    let initial = watch.value();
    let delivered: Shared<Option<ObservedDocumentValue>> = Arc::default();
    {
        let delivered = Arc::clone(&delivered);
        watch
            .start(listener(move |value, _, _| {
                *lock(&delivered) = Some(value);
                async { Ok(()) }
            }))
            .unwrap();
    }
    set_value(&session, 1).await;
    flush().await;
    let delivered = lock(&delivered).clone().unwrap();
    assert!(same(&delivered, &watch.value()));
    assert!(!same(&delivered, &initial));
    assert!(as_json(&delivered)["retained"].strict_equals(&as_json(&initial)["retained"]));
    assert!((number(&initial) - 0.0).abs() < f64::EPSILON);
    watch.stop().await;
}

#[tokio::test]
async fn delivers_retirement_and_does_not_follow_recreation() {
    let TestSession { session, .. } = create_state().await;
    let old_watch = watch(&session).await;
    let values: Shared<Vec<JsonValue>> = Arc::default();
    {
        let values = Arc::clone(&values);
        old_watch
            .start(listener(move |value, _, _| {
                lock(&values).push(as_json(&value));
                async { Ok(()) }
            }))
            .unwrap();
    }
    session
        .commit(
            |tx| async move {
                tx.retire_doc(&STATE_DOC, ()).await?;
                tx.doc(&STATE_DOC, ()).await?.set("value", 10)?;
                Ok(())
            },
            context(),
        )
        .await
        .unwrap();
    assert_eq!(old_watch.closed().await, WatchEnd::Retired);
    assert_eq!(*lock(&values), vec![JsonValue::Null]);
    assert!(old_watch.value().is_none());

    let replacement = watch(&session).await;
    assert!((number(&replacement.value()) - 10.0).abs() < f64::EPSILON);
    set_value(&session, 11).await;
    flush().await;
    assert!(old_watch.value().is_none());
    replacement.stop().await;
}

#[tokio::test]
async fn session_close_discards_retirement_buffered_before_start() {
    let TestSession { session, .. } = create_state().await;
    let watch = watch(&session).await;
    let baseline = watch.value();
    retire(&session).await;
    session.close(context()).await.unwrap();
    assert_eq!(watch.closed().await, WatchEnd::SessionClosed);
    assert!(same(&watch.value(), &baseline));
    let error = watch.start(noop()).unwrap_err();
    assert!(error.to_string().contains("stopped"), "{error}");
}

#[tokio::test]
async fn session_close_discards_retirement_behind_an_in_flight_callback() {
    let TestSession { session, .. } = create_state().await;
    let watch = watch(&session).await;
    let entered = Deferred::new();
    let release = Deferred::new();
    let values: Shared<Vec<Option<f64>>> = Arc::default();
    {
        let (entered, release, values) = (entered.clone(), release.clone(), Arc::clone(&values));
        watch
            .start(listener(move |value, _, _| {
                lock(&values).push(value.is_some().then(|| number(&value)));
                entered.resolve();
                let release = release.clone();
                async move {
                    release.wait().await;
                    Ok(())
                }
            }))
            .unwrap();
    }
    set_value(&session, 1).await;
    entered.wait().await;
    retire(&session).await;
    session.close(context()).await.unwrap();
    assert_eq!(watch.closed().await, WatchEnd::SessionClosed);
    release.resolve();
    flush().await;
    assert_eq!(*lock(&values), vec![Some(1.0)]);
}

#[tokio::test]
async fn supports_idempotent_stop_and_rejects_repeated_or_late_start() {
    let TestSession { session, .. } = create_state().await;
    let started = watch(&session).await;
    started.start(noop()).unwrap();
    let error = started.start(noop()).unwrap_err();
    assert!(error.to_string().contains("already started"), "{error}");
    // TS `second toBe first` (one shared promise): Rust futures have no
    // identity, so both stops must settle to the same terminal result.
    let first = started.stop();
    let second = started.stop();
    assert_eq!(second.await, WatchEnd::Stopped);
    assert_eq!(first.await, WatchEnd::Stopped);

    let stopped = watch(&session).await;
    stopped.stop().await;
    let error = stopped.start(noop()).unwrap_err();
    assert!(error.to_string().contains("stopped"), "{error}");
}

#[tokio::test]
async fn cancels_acquisition_without_leaking_a_registered_watch() {
    let TestSession {
        session, storage, ..
    } = create_state().await;
    session.unload_documents().await.unwrap();
    let gate = storage.hold_find_document();
    let (child, cancel) = with_cancel(context());
    let acquisition = tokio::spawn(session.watch_doc(&STATE_DOC, (), &child));
    gate.entered().await;
    cancel.cancel(Some(error("cancel acquisition")));
    gate.release();
    let Err(error) = acquisition.await.unwrap() else {
        panic!("acquisition fails");
    };
    assert!(error.to_string().contains("cancel acquisition"), "{error}");
    session.close(context()).await.unwrap();
}

#[tokio::test]
async fn cancels_future_delivery_without_aborting_an_in_flight_callback() {
    let TestSession { session, .. } = create_state().await;
    let (child, cancel) = with_cancel(context());
    let watch = session
        .watch_doc(&STATE_DOC, (), &child)
        .await
        .unwrap()
        .unwrap();
    let entered = Deferred::new();
    let release = Deferred::new();
    let delivery_context: Shared<Option<Context>> = Arc::default();
    {
        let (entered, release, delivery_context) = (
            entered.clone(),
            release.clone(),
            Arc::clone(&delivery_context),
        );
        watch
            .start(listener(move |_, _, delivered| {
                *lock(&delivery_context) = Some(delivered);
                entered.resolve();
                let release = release.clone();
                async move {
                    release.wait().await;
                    Ok(())
                }
            }))
            .unwrap();
    }
    set_value(&session, 1).await;
    entered.wait().await;
    cancel.cancel(None);
    assert_eq!(watch.closed().await, WatchEnd::Cancelled);
    assert!(lock(&delivery_context)
        .as_ref()
        .unwrap()
        .abort_signal()
        .is_none());
    release.resolve();
}

#[tokio::test]
async fn session_close_stops_future_delivery_without_joining_an_in_flight_callback() {
    let TestSession { session, .. } = create_state().await;
    let watch = watch(&session).await;
    let entered = Deferred::new();
    let release = Deferred::new();
    let delivery_context: Shared<Option<Context>> = Arc::default();
    {
        let (entered, release, delivery_context) = (
            entered.clone(),
            release.clone(),
            Arc::clone(&delivery_context),
        );
        watch
            .start(listener(move |_, _, delivered| {
                *lock(&delivery_context) = Some(delivered);
                entered.resolve();
                let release = release.clone();
                async move {
                    release.wait().await;
                    Ok(())
                }
            }))
            .unwrap();
    }
    set_value(&session, 1).await;
    entered.wait().await;
    session.close(context()).await.unwrap();
    assert!(lock(&delivery_context)
        .as_ref()
        .unwrap()
        .abort_signal()
        .is_none());
    assert_eq!(watch.closed().await, WatchEnd::SessionClosed);
    release.resolve();
}

#[tokio::test]
async fn settles_listener_failure_on_only_the_affected_watch() {
    let TestSession { session, .. } = create_state().await;
    let failed = watch(&session).await;
    let healthy = watch(&session).await;
    failed
        .start(listener(|_, _, _| async {
            Err(error("listener failed") as WatchListenerError)
        }))
        .unwrap();
    let healthy_calls = Arc::new(AtomicUsize::new(0));
    {
        let healthy_calls = Arc::clone(&healthy_calls);
        healthy
            .start(listener(move |_, _, _| {
                healthy_calls.fetch_add(1, Ordering::SeqCst);
                async { Ok(()) }
            }))
            .unwrap();
    }
    set_value(&session, 1).await;
    let end = failed.closed().await;
    assert_eq!(end.reason(), "listener_error");
    if let WatchEnd::ListenerError(error) = &end {
        assert_eq!(error.to_string(), "listener failed");
    }
    flush().await;
    assert_eq!(healthy_calls.load(Ordering::SeqCst), 1);
    healthy.stop().await;
}

#[tokio::test]
async fn hydrates_migration_without_writing_and_observes_the_later_exact_edit() {
    let TestSession {
        session, storage, ..
    } = open_test_session();
    session
        .commit(
            |tx| async move {
                tx.doc(&OLD_DOC, ()).await?;
                Ok(())
            },
            context(),
        )
        .await
        .unwrap();
    session.unload_documents().await.unwrap();
    let commits = storage.commit_count();
    let watch = session
        .watch_doc(&CURRENT_DOC, (), context())
        .await
        .unwrap()
        .unwrap();
    assert_eq!(
        as_json(&watch.value()),
        json(r#"{"value":3,"migrated":true}"#)
    );
    assert_eq!(storage.commit_count(), commits);
    let values: Shared<Vec<f64>> = Arc::default();
    {
        let values = Arc::clone(&values);
        watch
            .start(listener(move |value, _, _| {
                lock(&values).push(number(&value));
                async { Ok(()) }
            }))
            .unwrap();
    }
    session
        .commit(
            |tx| async move {
                tx.doc(&CURRENT_DOC, ()).await?;
                Ok(())
            },
            context(),
        )
        .await
        .unwrap();
    flush().await;
    assert_eq!(*lock(&values), Vec::<f64>::new());
    session
        .commit(
            |tx| async move {
                tx.doc(&CURRENT_DOC, ()).await?.set("value", 4)?;
                Ok(())
            },
            context(),
        )
        .await
        .unwrap();
    flush().await;
    assert_eq!(*lock(&values), vec![4.0]);
    watch.stop().await;
}

#[tokio::test]
async fn can_replay_every_delivered_exact_operation_batch_from_the_acquisition_revision() {
    let TestSession { session, .. } = create_state().await;
    let watch = watch(&session).await;
    let replica: Shared<JsonValue> = Arc::new(Mutex::new(as_json(&watch.value())));
    let violations = Arc::new(AtomicUsize::new(0));
    {
        let (replica, violations) = (Arc::clone(&replica), Arc::clone(&violations));
        watch
            .start(listener(move |value, ops: Ops, _| {
                let mut replica = lock(&replica);
                let ops: &[Op] = &ops;
                *replica = apply_immutable(&replica, ops).expect("replayable ops");
                if *replica != as_json(&value) {
                    violations.fetch_add(1, Ordering::SeqCst);
                }
                async { Ok(()) }
            }))
            .unwrap();
    }
    session
        .commit(
            |tx| async move {
                let state = tx.doc(&STATE_DOC, ()).await?;
                state.set("value", 3)?;
                state
                    .child("items")?
                    .splice(0, 1, std::iter::empty::<JsonValue>())?;
                Ok(())
            },
            context(),
        )
        .await
        .unwrap();
    flush().await;
    assert_eq!(violations.load(Ordering::SeqCst), 0);
    assert_eq!(*lock(&replica), as_json(&watch.value()));
    watch.stop().await;
}

#[tokio::test]
async fn continues_after_the_tracker_cache_unloads() {
    let TestSession {
        session, storage, ..
    } = create_state().await;
    let watch = watch(&session).await;
    let baseline = watch.value();
    let reads = storage.document_read_count();
    session.unload_documents().await.unwrap();
    let reloaded = session.snapshot(&STATE_DOC, (), context()).await.unwrap();
    assert_eq!(as_json(&reloaded), as_json(&baseline));
    // TS `not.toBe(baseline)`: Rust MemoryStorage hands back the stored
    // `Arc`, so a reload may share the object; the read count below proves
    // the value came from Storage.
    assert!(storage.document_read_count() > reads);
    watch.start(noop()).unwrap();
    set_value(&session, 7).await;
    flush().await;
    assert!((number(&watch.value()) - 7.0).abs() < f64::EPSILON);
    watch.stop().await;
}
