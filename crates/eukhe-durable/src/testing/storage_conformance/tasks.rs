//! Task and submission record cases.

use eukhe_chord::json::JsonValue;
use serde_json::json;

use super::{commit, create_root, cx, id, ids, j, mint, ok, pending_task, q, v, with, Cases};
use crate::types::{Cursor, Storage};

pub(super) fn add_cases(cases: &mut Cases) {
    add_task_cases(cases);
    add_submission_cases(cases);
}

/// `(await storage.scanTasks(query, limit, undefined, context)).items` as JSON.
async fn scan_tasks(s: &dyn Storage, query: serde_json::Value, limit: usize) -> JsonValue {
    j(&ok(s.scan_tasks(&q(query), limit, None, cx()).await).items)
}

#[expect(
    clippy::too_many_lines,
    reason = "TS conformance cases, kept whole and in TS order"
)]
fn add_task_cases(cases: &mut Cases) {
    cases.case(
        "replaces complete task records and pages filtered task scans",
        |storage| async move {
            let s = &*storage;
            let root_id = create_root(s).await;
            let first_id = mint(s).await;
            let second_id = mint(s).await;
            let third_id = mint(s).await;
            let first = with(pending_task(first_id, root_id), json!({ "memos": { "winner": "first" } }));
            let second = with(pending_task(second_id, root_id), json!({ "background": true }));
            let third = with(pending_task(third_id, root_id), json!({ "abortRequested": true }));
            ok(commit(
                s,
                json!([
                    { "type": "task", "value": first },
                    { "type": "task", "value": second },
                    { "type": "task", "value": third },
                ]),
            )
            .await);

            let running = with(
                first.clone(),
                json!({
                    "state": { "status": "running", "checkpoint": { "phase": "effect", "attempt": 1 } },
                    "abortRequested": true,
                }),
            );
            ok(commit(s, json!([{ "type": "task", "value": running }])).await);
            assert_eq!(j(&ok(s.task(id(first_id), cx()).await)), v(running));
            let terminal = json!({
                "id": first_id,
                "conversationId": root_id,
                "kind": first["kind"],
                "version": first["version"],
                "input": first["input"],
                "state": { "status": "terminal", "outcome": { "status": "completed", "result": { "entryId": 99 } } },
                "background": false,
                "abortRequested": true,
            });
            ok(commit(s, json!([{ "type": "task", "value": terminal }])).await);
            assert_eq!(j(&ok(s.task(id(first_id), cx()).await)), v(terminal.clone()));

            let pending = q(json!({ "status": "pending" }));
            let pending_page = ok(s.scan_tasks(&pending, 1, None, cx()).await);
            assert_eq!(ids(&pending_page.items), v(json!([second_id])));
            assert!(pending_page.next.is_some());
            assert_eq!(
                ids(&ok(s
                    .scan_tasks(&pending, 1, pending_page.next.as_ref(), cx())
                    .await)
                .items),
                v(json!([third_id]))
            );
            assert_eq!(
                scan_tasks(s, json!({ "status": "terminal", "abortRequested": true }), 10).await,
                v(json!([terminal]))
            );
            assert_eq!(
                ids(&ok(s.scan_tasks(&q(json!({ "background": true })), 10, None, cx()).await).items),
                v(json!([second_id]))
            );
        },
    );

    cases.case(
        "stores owners and scans waiting and completing tasks by status",
        |storage| async move {
            let s = &*storage;
            let root_id = create_root(s).await;
            let owner_id = mint(s).await;
            let waiting_id = mint(s).await;
            let completing_id = mint(s).await;
            let owner = pending_task(owner_id, root_id);
            let waiting = with(
                pending_task(waiting_id, root_id),
                json!({
                    "owner": owner_id,
                    "state": { "status": "waiting", "checkpoint": { "phase": "next" }, "on": [owner_id], "policy": "allSettled" },
                    "memos": { "kept": true },
                }),
            );
            let mut base = pending_task(completing_id, root_id);
            base.as_object_mut()
                .expect("task literal is an object")
                .remove("state");
            let completing = with(
                base,
                json!({
                    "owner": owner_id,
                    "state": { "status": "completing", "outcome": { "status": "failed", "error": { "message": "held" } } },
                }),
            );
            let writes: Vec<serde_json::Value> = [&owner, &waiting, &completing]
                .into_iter()
                .map(|value| json!({ "type": "task", "value": value }))
                .collect();
            ok(commit(s, serde_json::Value::Array(writes)).await);
            assert_eq!(j(&ok(s.task(id(waiting_id), cx()).await)), v(waiting.clone()));
            assert_eq!(j(&ok(s.task(id(completing_id), cx()).await)), v(completing.clone()));
            let scan = |status: &'static str| scan_tasks(s, json!({ "status": status }), 10);
            assert_eq!(scan("waiting").await, v(json!([waiting])));
            assert_eq!(scan("completing").await, v(json!([completing])));
            let pending = scan("pending").await;
            assert_eq!(
                ids(pending.as_array().expect("an array")),
                v(json!([owner_id]))
            );
            let terminal = with(
                completing.clone(),
                json!({ "state": { "status": "terminal", "outcome": completing["state"]["outcome"] } }),
            );
            ok(commit(s, json!([{ "type": "task", "value": terminal }])).await);
            assert_eq!(scan("completing").await, v(json!([])));
            assert_eq!(scan("terminal").await, v(json!([terminal])));
        },
    );
}

/// Every submission ID of a scan, paging one item at a time.
async fn submission_ids(s: &dyn Storage, query: serde_json::Value) -> JsonValue {
    let query = q(query);
    let mut found = Vec::new();
    let mut cursor: Option<Cursor> = None;
    loop {
        let page = ok(s.scan_submissions(&query, 1, cursor.as_ref(), cx()).await);
        found.extend(page.items.iter().map(|item| j(item)["id"].clone()));
        cursor = page.next;
        if cursor.is_none() {
            break;
        }
    }
    found.into_iter().collect()
}

#[expect(
    clippy::too_many_lines,
    reason = "TS conformance cases, kept whole and in TS order"
)]
fn add_submission_cases(cases: &mut Cases) {
    cases.case(
        "indexes request IDs per conversation and replaces complete submission records",
        |storage| async move {
            let s = &*storage;
            let root_id = create_root(s).await;
            let second_conversation_id = mint(s).await;
            ok(commit(
                s,
                json!([{ "type": "conversation", "value": { "id": second_conversation_id } }]),
            )
            .await);
            let first_id = mint(s).await;
            let second_id = mint(s).await;
            let other_conversation_id = mint(s).await;
            let first = json!({ "id": first_id, "conversationId": root_id, "requestId": "same", "type": "input", "status": "queued" });
            let second = json!({ "id": second_id, "conversationId": root_id, "requestId": "other", "type": "input", "status": "queued" });
            let other_conversation = json!({
                "id": other_conversation_id,
                "conversationId": second_conversation_id,
                "requestId": "same",
                "type": "input",
                "status": "queued",
            });
            ok(commit(
                s,
                json!([
                    { "type": "submission", "value": first },
                    { "type": "submission", "value": second },
                    { "type": "submission", "value": other_conversation },
                ]),
            )
            .await);
            assert_eq!(
                j(&ok(s.submission_by_request(id(root_id), "same", cx()).await)),
                v(first)
            );
            assert_eq!(
                j(&ok(s
                    .submission_by_request(id(second_conversation_id), "same", cx())
                    .await)),
                v(other_conversation)
            );

            let placed_entry = mint(s).await;
            let placed_second = with(second, json!({ "status": "placed", "entry": placed_entry }));
            ok(commit(s, json!([{ "type": "submission", "value": placed_second }])).await);
            assert_eq!(
                j(&ok(s.submission(id(second_id), cx()).await)),
                v(placed_second.clone())
            );
            assert_eq!(
                j(&ok(s.submission_by_request(id(root_id), "other", cx()).await)),
                v(placed_second.clone())
            );

            assert_eq!(
                submission_ids(s, json!({})).await,
                v(json!([first_id, second_id, other_conversation_id]))
            );
            assert_eq!(
                submission_ids(s, json!({ "conversationId": root_id })).await,
                v(json!([first_id, second_id]))
            );
            // A status change moves the record between status scans.
            assert_eq!(
                submission_ids(s, json!({ "status": "queued" })).await,
                v(json!([first_id, other_conversation_id]))
            );
            assert_eq!(
                submission_ids(s, json!({ "status": "placed" })).await,
                v(json!([second_id]))
            );
            assert_eq!(
                submission_ids(s, json!({ "conversationId": second_conversation_id, "status": "queued" })).await,
                v(json!([other_conversation_id]))
            );
            assert_eq!(
                submission_ids(s, json!({ "conversationId": second_conversation_id, "status": "placed" })).await,
                v(json!([]))
            );
            assert_eq!(
                j(&ok(s
                    .scan_submissions(&q(json!({ "status": "placed" })), 10, None, cx())
                    .await)
                .items),
                v(json!([placed_second]))
            );
        },
    );

    cases.case(
        "stores passive write submissions without input-only lifecycle states",
        |storage| async move {
            let s = &*storage;
            let root_id = create_root(s).await;
            let done_id = mint(s).await;
            let failed_id = mint(s).await;
            let queued_done = json!({ "id": done_id, "conversationId": root_id, "requestId": "passive-done", "type": "write", "status": "queued" });
            let queued_failed = json!({ "id": failed_id, "conversationId": root_id, "requestId": "passive-failed", "type": "write", "status": "queued" });
            ok(commit(
                s,
                json!([
                    { "type": "submission", "value": queued_done },
                    { "type": "submission", "value": queued_failed },
                ]),
            )
            .await);

            let done_entry = mint(s).await;
            let done = with(queued_done, json!({ "status": "done", "entry": done_entry }));
            let unanswered = with(
                queued_failed,
                json!({ "status": "unanswered", "reason": "closed", "detail": { "retryable": false } }),
            );
            ok(commit(
                s,
                json!([
                    { "type": "submission", "value": done },
                    { "type": "submission", "value": unanswered },
                ]),
            )
            .await);
            assert_eq!(j(&ok(s.submission(id(done_id), cx()).await)), v(done.clone()));
            assert_eq!(
                j(&ok(s.submission_by_request(id(root_id), "passive-done", cx()).await)),
                v(done)
            );
            assert_eq!(
                j(&ok(s.submission(id(failed_id), cx()).await)),
                v(unanswered.clone())
            );
            assert_eq!(
                j(&ok(s.submission_by_request(id(root_id), "passive-failed", cx()).await)),
                v(unanswered)
            );
        },
    );
}
