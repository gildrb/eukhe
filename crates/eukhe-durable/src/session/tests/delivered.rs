//! `CommittedWatch::delivered()`, an eukhe addition without a TS test.

use std::sync::{Arc, Mutex, PoisonError};

use eukhe_chord::json::JsonValue;
use futures::FutureExt;

use super::support::{context, flush, json, open_test_session, Deferred, TestSession};
use crate::documents::{DocDefinition, SessionDoc};
use crate::session::{DocumentWatch, ObservedDocumentValue, Session, WatchEnd, WatchListener};

const STATE_DOC: SessionDoc<JsonValue> = match SessionDoc::define(DocDefinition {
    kind: "delivered.state",
    version: 1,
    initial: || json(r#"{"value":0}"#),
    migrate: None,
    checkpoint_when: None,
}) {
    Ok(token) => token,
    Err(_) => panic!("valid definition"),
};

type Values = Arc<Mutex<Vec<f64>>>;

fn values_of(values: &Values) -> Vec<f64> {
    values
        .lock()
        .unwrap_or_else(PoisonError::into_inner)
        .clone()
}

fn number(value: &ObservedDocumentValue) -> f64 {
    value
        .as_ref()
        .and_then(|object| object.get("value"))
        .and_then(JsonValue::as_f64)
        .unwrap_or(-1.0)
}

/// Records every delivered value; the first delivery waits for `gate` when given.
fn recording(
    values: &Values,
    gate: Option<(Deferred, Deferred)>,
) -> WatchListener<ObservedDocumentValue> {
    let values = Arc::clone(values);
    Arc::new(move |value, _, _| {
        let count = {
            let mut values = values.lock().unwrap_or_else(PoisonError::into_inner);
            values.push(number(&value));
            values.len()
        };
        let gate = gate.clone();
        async move {
            if let (1, Some((entered, release))) = (count, gate) {
                entered.resolve();
                release.wait().await;
            }
            Ok(())
        }
        .boxed()
    })
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

async fn create_state() -> (TestSession, DocumentWatch) {
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
    let watch = test
        .session
        .watch_doc(&STATE_DOC, (), context())
        .await
        .unwrap()
        .unwrap();
    (test, watch)
}

#[tokio::test]
async fn resolves_after_every_frame_committed_before_the_call_reached_the_listener() {
    let (TestSession { session, .. }, watch) = create_state().await;
    let values = Values::default();
    watch.start(recording(&values, None)).unwrap();
    for value in 1..=20 {
        set_value(&session, value).await;
    }
    watch.delivered().await;
    assert_eq!(
        values_of(&values),
        (1..=20).map(f64::from).collect::<Vec<_>>()
    );
    // Nothing is queued: resolves at once.
    watch.delivered().await;
    watch.stop().await;
}

#[tokio::test]
async fn waits_for_a_slow_listener_to_settle_the_last_frame() {
    let (TestSession { session, .. }, watch) = create_state().await;
    let values = Values::default();
    let (entered, release) = (Deferred::new(), Deferred::new());
    watch
        .start(recording(&values, Some((entered.clone(), release.clone()))))
        .unwrap();
    for value in 1..=3 {
        set_value(&session, value).await;
    }
    entered.wait().await;
    let delivered = tokio::spawn(watch.delivered());
    flush().await;
    assert!(!delivered.is_finished());
    assert_eq!(values_of(&values), vec![1.0]);
    release.resolve();
    delivered.await.unwrap();
    assert_eq!(values_of(&values), vec![1.0, 2.0, 3.0]);
    watch.stop().await;
}

#[tokio::test]
async fn waits_for_start_then_covers_an_overflow_replacement() {
    let (TestSession { session, .. }, watch) = create_state().await;
    for value in 1..=101 {
        set_value(&session, value).await;
    }
    let delivered = tokio::spawn(watch.delivered());
    flush().await;
    assert!(!delivered.is_finished());
    let values = Values::default();
    watch.start(recording(&values, None)).unwrap();
    delivered.await.unwrap();
    assert_eq!(values_of(&values), vec![101.0]);
    watch.stop().await;
}

#[tokio::test]
async fn stop_resolves_pending_calls_and_later_calls_resolve_at_once() {
    let (TestSession { session, .. }, watch) = create_state().await;
    let values = Values::default();
    let (entered, release) = (Deferred::new(), Deferred::new());
    watch
        .start(recording(&values, Some((entered.clone(), release))))
        .unwrap();
    set_value(&session, 1).await;
    set_value(&session, 2).await;
    entered.wait().await;
    let delivered = tokio::spawn(watch.delivered());
    flush().await;
    assert!(!delivered.is_finished());
    assert_eq!(watch.stop().await, WatchEnd::Stopped);
    delivered.await.unwrap();
    set_value(&session, 3).await;
    watch.delivered().await;
    assert_eq!(values_of(&values), vec![1.0]);
}
