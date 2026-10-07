//! Port of `test/context.test.ts`.

use std::sync::Arc;

use eukhe_chord::context::{
    await_with_context, create_context_key, with_abort_signal, with_cancel, with_context_value,
    without_abort_signal, AbortController, AbortReason, BACKGROUND_CONTEXT, TODO_CONTEXT,
};

#[derive(Debug, thiserror::Error)]
#[error("{0}")]
struct Reason(&'static str);

fn reason(text: &'static str) -> AbortReason {
    Arc::new(Reason(text))
}

fn reason_text(reason: Option<AbortReason>) -> Option<String> {
    reason.map(|reason| reason.to_string())
}

#[test]
fn provides_distinct_empty_root_contexts() {
    let key = create_context_key::<String>("value");
    assert_ne!(TODO_CONTEXT.to_string(), BACKGROUND_CONTEXT.to_string());
    assert!(TODO_CONTEXT.abort_signal().is_none());
    assert_eq!(TODO_CONTEXT.value(&key), None);
    assert_eq!(
        BACKGROUND_CONTEXT.to_string(),
        "[Context BACKGROUND_CONTEXT]"
    );
    assert_eq!(TODO_CONTEXT.to_string(), "[Context TODO_CONTEXT]");
}

#[test]
fn layers_typed_values_without_modifying_parents() {
    let first_key = create_context_key::<String>("first");
    let second_key = create_context_key::<i32>("second");
    let first = with_context_value(&first_key, "one".to_owned(), &BACKGROUND_CONTEXT);
    let second = with_context_value(&second_key, 2, &first);
    let replaced = with_context_value(&first_key, "updated".to_owned(), &second);

    assert_eq!(BACKGROUND_CONTEXT.value(&first_key), None);
    assert_eq!(first.value(&first_key).as_deref(), Some("one"));
    assert_eq!(first.value(&second_key), None);
    assert_eq!(second.value(&first_key).as_deref(), Some("one"));
    assert_eq!(second.value(&second_key), Some(2));
    assert_eq!(replaced.value(&first_key).as_deref(), Some("updated"));
    assert_eq!(second.value(&first_key).as_deref(), Some("one"));
    assert_eq!(
        replaced.to_string(),
        "[Context BACKGROUND_CONTEXT].WithValue(first).WithValue(second).WithValue(first)"
    );
}

#[test]
fn inherits_parent_cancellation_and_isolates_child_cancellation() {
    let parent_controller = AbortController::new();
    let parent = with_abort_signal(&parent_controller.signal(), &BACKGROUND_CONTEXT);
    let (child, child_cancel) = with_cancel(&parent);
    let (sibling, _sibling_cancel) = with_cancel(&parent);
    // The JS abort listener: a token cancelled when the child aborts.
    let child_listener = child
        .abort_signal()
        .expect("child signal")
        .cancellation_token();

    child_cancel.cancel(Some(reason("child")));
    let child_signal = child.abort_signal().expect("child signal");
    assert!(child_signal.aborted());
    assert_eq!(reason_text(child_signal.reason()).as_deref(), Some("child"));
    assert!(!sibling.abort_signal().expect("sibling signal").aborted());
    assert!(!parent.abort_signal().expect("parent signal").aborted());
    assert!(child_listener.is_cancelled());

    parent_controller.abort(Some(reason("parent")));
    let sibling_signal = sibling.abort_signal().expect("sibling signal");
    assert!(sibling_signal.aborted());
    assert_eq!(
        reason_text(sibling_signal.reason()).as_deref(),
        Some("parent")
    );
}

#[test]
fn masks_caller_cancellation_for_mandatory_cleanup() {
    let controller = AbortController::new();
    let key = create_context_key::<String>("value");
    let context = with_context_value(
        &key,
        "preserved".to_owned(),
        &with_abort_signal(&controller.signal(), &BACKGROUND_CONTEXT),
    );
    let cleanup = without_abort_signal(&context);

    controller.abort(None);
    assert!(context.abort_signal().expect("signal").aborted());
    assert!(cleanup.abort_signal().is_none());
    assert_eq!(cleanup.value(&key).as_deref(), Some("preserved"));
}

#[tokio::test]
async fn stops_waiting_when_the_invocation_is_cancelled() {
    let controller = AbortController::new();
    let context = with_abort_signal(&controller.signal(), &BACKGROUND_CONTEXT);
    let (resolve_work, work) = tokio::sync::oneshot::channel::<&'static str>();
    let work = tokio::spawn(work);
    let (sender, receiver) = tokio::sync::oneshot::channel::<()>();
    let waiting = tokio::spawn({
        let context = context.clone();
        async move {
            let pending = std::future::pending::<()>();
            let _ = sender.send(());
            await_with_context(pending, &context).await
        }
    });
    receiver.await.expect("waiter started");
    let cancellation = reason("cancelled");
    controller.abort(Some(Arc::clone(&cancellation)));
    let rejected = waiting.await.expect("waiter").expect_err("cancelled");
    assert!(Arc::ptr_eq(&rejected, &cancellation));
    resolve_work.send("completed later").expect("work receiver");
    assert_eq!(
        work.await.expect("work").expect("resolved"),
        "completed later"
    );
    let completed = await_with_context(async { "completed" }, &BACKGROUND_CONTEXT).await;
    assert_eq!(completed.expect("not cancelled"), "completed");
}
