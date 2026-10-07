//! Root, commit atomicity, detachment, entry, and conversation cases.

use eukhe_chord::json::JsonValue;
use serde_json::json;

use super::{
    at, commit, create_root, cx, entry, id, ids, j, mint, n, ok, q, rejects, v, with, Cases, ROOT,
};
use crate::types::Cursor;

pub(super) fn add_cases(cases: &mut Cases) {
    add_commit_cases(cases);
    add_detach_cases(cases);
    add_entry_cases(cases);
    add_conversation_cases(cases);
    add_fork_history_case(cases);
}

fn add_commit_cases(cases: &mut Cases) {
    cases.case(
        "reserves ID 1 for the immutable root conversation",
        |storage| async move {
            let s = &*storage;
            assert_eq!(mint(s).await, 2);
            assert_eq!(create_root(s).await, ROOT);
            assert_eq!(
                j(&ok(s.conversation(id(ROOT), cx()).await)),
                v(json!({ "id": ROOT }))
            );
            rejects(
                commit(
                    s,
                    json!([{ "type": "conversation", "value": { "id": ROOT } }]),
                ),
                &format!("ID {ROOT} already belongs to conversation"),
            )
            .await;
        },
    );

    cases.case(
        "commits mixed table writes atomically and rolls all of them back on failure",
        |storage| async move {
            let s = &*storage;
            let root_id = create_root(s).await;
            let entry_id = mint(s).await;
            let task_id = mint(s).await;
            let submission_id = mint(s).await;
            let task = super::pending_task(task_id, root_id);
            let input = json!({
                "id": submission_id,
                "conversationId": root_id,
                "requestId": "request-1",
                "type": "input",
                "status": "placed",
                "entry": entry_id,
            });
            let initial_seq = ok(commit(
                s,
                json!([
                    { "type": "entry", "value": entry(entry_id, root_id, "user", json!({ "data": { "text": "hello" } })) },
                    { "type": "task", "value": task },
                    { "type": "submission", "value": input },
                ]),
            )
            .await);

            let stored = ok(s.entry(id(entry_id), cx()).await).expect("entry is stored");
            assert_eq!(
                j(&stored.entry),
                v(entry(entry_id, root_id, "user", json!({ "data": { "text": "hello" } })))
            );
            assert_eq!(n(&stored.commit_seq), initial_seq);
            assert_eq!(j(&ok(s.task(id(task_id), cx()).await)), v(task.clone()));
            assert_eq!(
                j(&ok(s.submission(id(submission_id), cx()).await)),
                v(input.clone())
            );

            let transient_entry_id = mint(s).await;
            let running_task = with(
                task.clone(),
                json!({ "state": { "status": "running", "checkpoint": { "phase": "effect" } } }),
            );
            let done_input = with(
                input.clone(),
                json!({ "status": "done", "answer": transient_entry_id }),
            );
            rejects(
                commit(
                    s,
                    json!([
                        { "type": "task", "value": running_task },
                        { "type": "submission", "value": done_input },
                        { "type": "entry", "value": entry(transient_entry_id, root_id, "assistant", json!({})) },
                        { "type": "conversation", "value": { "id": root_id } },
                    ]),
                ),
                &format!("ID {root_id} already belongs to conversation"),
            )
            .await;

            assert_eq!(j(&ok(s.task(id(task_id), cx()).await)), v(task));
            assert_eq!(j(&ok(s.submission(id(submission_id), cx()).await)), v(input));
            assert!(ok(s.entry(id(transient_entry_id), cx()).await).is_none());
            let after_rollback_id = mint(s).await;
            let after_rollback_seq = ok(commit(
                s,
                json!([{ "type": "entry", "value": entry(after_rollback_id, root_id, "after-rollback", json!({})) }]),
            )
            .await);
            assert!(after_rollback_seq > initial_seq);
        },
    );
}

/// Rust adaptation: callers own their values, so "mutating the caller's
/// object after commit" becomes copy-on-write mutation of the shared
/// [`JsonValue`]s the writes were built from, and of values read back.
fn add_detach_cases(cases: &mut Cases) {
    cases.case(
        "detaches retained writes and every returned record",
        |storage| async move {
            let s = &*storage;
            let root_id = create_root(s).await;
            let entry_id = mint(s).await;
            let task_id = mint(s).await;
            let submission_id = mint(s).await;
            let mut entry_data = v(json!({ "nested": [1, 2] }));
            let mut checkpoint = v(json!({ "phase": "ready", "nested": { "count": 1 } }));
            let mut detail = v(json!({ "codes": ["initial"] }));
            let stored_entry = entry(entry_id, root_id, "note", json!({ "data": entry_data }));
            let stored_task = with(
                super::pending_task(task_id, root_id),
                json!({ "state": { "status": "pending", "checkpoint": checkpoint } }),
            );
            let stored_input = json!({
                "id": submission_id,
                "conversationId": root_id,
                "type": "input",
                "status": "unanswered",
                "reason": "failed",
                "detail": detail,
            });
            ok(commit(
                s,
                json!([
                    { "type": "entry", "value": stored_entry },
                    { "type": "task", "value": stored_task },
                    { "type": "submission", "value": stored_input },
                ]),
            )
            .await);

            push(at(&mut entry_data, &["nested"]), v(3));
            set(at(&mut checkpoint, &["nested"]), "count", v(2));
            push(at(&mut detail, &["codes"]), v("mutated"));
            assert_detached(s, entry_id, task_id, submission_id).await;

            let mut read_entry = j(&ok(s.entry(id(entry_id), cx()).await));
            push(at(&mut read_entry, &["entry", "data", "nested"]), v(9));
            let mut read_task = j(&ok(s.task(id(task_id), cx()).await));
            if read_task["state"]["status"].as_str() != Some("terminal") {
                set(
                    at(&mut read_task, &["state", "checkpoint", "nested"]),
                    "count",
                    v(9),
                );
            }
            let mut read_input = j(&ok(s.submission(id(submission_id), cx()).await));
            push(
                at(&mut read_input, &["detail", "codes"]),
                v("read mutation"),
            );

            assert_detached(s, entry_id, task_id, submission_id).await;
        },
    );

    cases.case(
        "detaches prototype-like JSON keys without changing object prototypes",
        |storage| async move {
            let s = &*storage;
            let root_id = create_root(s).await;
            let entry_id = mint(s).await;
            let mut data = JsonValue::parse(
                r#"{"__proto__":{"polluted":false},"constructor":{"label":"stored"},"toString":"value"}"#,
            )
            .expect("valid JSON");
            ok(commit(
                s,
                json!([{ "type": "entry", "value": entry(entry_id, root_id, "note", json!({ "data": data })) }]),
            )
            .await);

            set(at(&mut data, &["__proto__"]), "polluted", v(true));
            set(at(&mut data, &["constructor"]), "label", v("mutated"));
            let mut first_read = j(&ok(s.entry(id(entry_id), cx()).await))["entry"]["data"].clone();
            // Rust has no prototypes: the keys must stay ordinary own keys.
            assert!(first_read
                .as_object()
                .is_some_and(|object| object.contains_key("__proto__")));
            assert_eq!(first_read["__proto__"], v(json!({ "polluted": false })));
            assert_eq!(first_read["constructor"], v(json!({ "label": "stored" })));
            assert_eq!(first_read["toString"], v("value"));
            assert!(JsonValue::object().get("polluted").is_none());

            set(at(&mut first_read, &["__proto__"]), "polluted", v(true));
            let second_read = j(&ok(s.entry(id(entry_id), cx()).await))["entry"]["data"].clone();
            assert_eq!(second_read["__proto__"], v(json!({ "polluted": false })));
            assert_eq!(second_read["constructor"], v(json!({ "label": "stored" })));
            assert_eq!(second_read["toString"], v("value"));
        },
    );
}

async fn assert_detached(
    s: &dyn crate::types::Storage,
    entry_id: u64,
    task_id: u64,
    submission_id: u64,
) {
    assert_eq!(
        j(&ok(s.entry(id(entry_id), cx()).await))["entry"]["data"],
        v(json!({ "nested": [1, 2] }))
    );
    assert_eq!(
        j(&ok(s.task(id(task_id), cx()).await))["state"],
        v(
            json!({ "status": "pending", "checkpoint": { "phase": "ready", "nested": { "count": 1 } } })
        )
    );
    assert_eq!(
        j(&ok(s.submission(id(submission_id), cx()).await))["detail"],
        v(json!({ "codes": ["initial"] }))
    );
}

/// `array.push(item)` on a copy-on-write JSON array.
#[track_caller]
fn push(array: &mut JsonValue, item: JsonValue) {
    array.as_array_mut().expect("an array").push(item);
}

/// `object[key] = value` on a copy-on-write JSON object.
#[track_caller]
fn set(object: &mut JsonValue, key: &str, value: JsonValue) {
    object
        .as_object_mut()
        .expect("an object")
        .insert(key, value);
}

fn add_entry_cases(cases: &mut Cases) {
    cases.case(
        "indexes entries committed out of ID order",
        |storage| async move {
            let s = &*storage;
            let root_id = create_root(s).await;
            ok(commit(
            s,
            json!([
                { "type": "entry", "value": entry(30, root_id, "message", json!({})) },
                { "type": "entry", "value": entry(10, root_id, "message", json!({})) },
                { "type": "entry", "value": entry(20, root_id, "marker", json!({ "head": 10 })) },
            ]),
        )
        .await);

            let page = ok(s
                .scan_entries(&q(json!({ "conversationId": root_id })), 10, None, cx())
                .await);
            assert_eq!(ids(&page.items), v(json!([30, 20, 10])));
            assert_eq!(
                j(&ok(s
                    .find_latest_head_marker(id(root_id), None, cx())
                    .await))["id"],
                v(20)
            );
        },
    );

    cases.case(
        "continues an entry cursor below its last item after a newer commit",
        |storage| async move {
            let s = &*storage;
            let root_id = create_root(s).await;
            let oldest_id = mint(s).await;
            let middle_id = mint(s).await;
            let newest_id = mint(s).await;
            ok(commit(
                s,
                json!([
                    { "type": "entry", "value": entry(oldest_id, root_id, "message", json!({})) },
                    { "type": "entry", "value": entry(middle_id, root_id, "message", json!({})) },
                    { "type": "entry", "value": entry(newest_id, root_id, "message", json!({})) },
                ]),
            )
            .await);

            let query = q(json!({ "conversationId": root_id }));
            let first = ok(s.scan_entries(&query, 2, None, cx()).await);
            assert_eq!(ids(&first.items), v(json!([newest_id, middle_id])));
            let appended_id = mint(s).await;
            ok(commit(
                s,
                json!([{ "type": "entry", "value": entry(appended_id, root_id, "message", json!({})) }]),
            )
            .await);
            let second = ok(s.scan_entries(&query, 2, first.next.as_ref(), cx()).await);
            assert_eq!(ids(&second.items), v(json!([oldest_id])));
            assert!(second.next.is_none());
        },
    );
}

fn add_conversation_cases(cases: &mut Cases) {
    cases.case(
        "paginates conversations by opaque cursor in ascending ID order",
        |storage| async move {
            let s = &*storage;
            let root_id = create_root(s).await;
            let second_id = mint(s).await;
            let third_id = mint(s).await;
            ok(commit(
                s,
                json!([
                    { "type": "conversation", "value": { "id": third_id } },
                    { "type": "conversation", "value": { "id": second_id } },
                ]),
            )
            .await);

            let query = q(json!({}));
            let first = ok(s.scan_conversations(&query, 2, None, cx()).await);
            assert_eq!(ids(&first.items), v(json!([root_id, second_id])));
            let next = first.next.as_ref().expect("a next cursor");
            let round_tripped: Cursor =
                q(JsonValue::parse(&j(next).to_string()).expect("cursor JSON parses"));
            let second = ok(s
                .scan_conversations(&query, 2, Some(&round_tripped), cx())
                .await);
            assert_eq!(ids(&second.items), v(json!([third_id])));
            assert!(second.next.is_none());
        },
    );

    cases.case(
        "filters and pages conversations by durable owner edges",
        |storage| async move {
            let s = &*storage;
            let root_id = create_root(s).await;
            let other_owner_id = mint(s).await;
            let first_task_id = mint(s).await;
            let second_task_id = mint(s).await;
            let first_id = mint(s).await;
            let second_id = mint(s).await;
            let third_id = mint(s).await;
            ok(commit(
                s,
                json!([
                    { "type": "conversation", "value": { "id": other_owner_id } },
                    { "type": "conversation", "value": { "id": first_id, "owner": { "conversationId": root_id, "taskId": first_task_id } } },
                    { "type": "conversation", "value": { "id": second_id, "owner": { "conversationId": root_id, "taskId": second_task_id } } },
                    { "type": "conversation", "value": { "id": third_id, "owner": { "conversationId": other_owner_id, "taskId": first_task_id } } },
                ]),
            )
            .await);

            let by_root = q(json!({ "ownerConversationId": root_id }));
            let first = ok(s.scan_conversations(&by_root, 1, None, cx()).await);
            assert_eq!(ids(&first.items), v(json!([first_id])));
            assert!(first.next.is_some());
            let second = ok(s
                .scan_conversations(&by_root, 1, first.next.as_ref(), cx())
                .await);
            assert_eq!(ids(&second.items), v(json!([second_id])));
            assert!(second.next.is_none());
            assert_eq!(
                ids(&ok(s
                    .scan_conversations(&q(json!({ "ownerTaskId": first_task_id })), 10, None, cx())
                    .await)
                .items),
                v(json!([first_id, third_id]))
            );
            assert_eq!(
                ids(&ok(s
                    .scan_conversations(
                        &q(json!({ "ownerConversationId": root_id, "ownerTaskId": first_task_id })),
                        10,
                        None,
                        cx(),
                    )
                    .await)
                .items),
                v(json!([first_id]))
            );
        },
    );
}

#[expect(clippy::too_many_lines, reason = "one TS conformance case, kept whole")]
fn add_fork_history_case(cases: &mut Cases) {
    cases.case(
        "scans deep fork history newest-first through every ancestor cap",
        |storage| async move {
            let s = &*storage;
            let root_id = create_root(s).await;
            let root_first = mint(s).await;
            let root_fork_point = mint(s).await;
            let root_excluded_same_commit = mint(s).await;
            let root_entries_seq = ok(commit(
                s,
                json!([
                    { "type": "entry", "value": entry(root_first, root_id, "message", json!({})) },
                    { "type": "entry", "value": entry(root_fork_point, root_id, "marker", json!({ "head": root_first })) },
                    { "type": "entry", "value": entry(root_excluded_same_commit, root_id, "message", json!({})) },
                ]),
            )
            .await);
            let child_id = mint(s).await;
            ok(commit(
                s,
                json!([{ "type": "conversation", "value": { "id": child_id, "parent": { "conversationId": root_id, "at": root_fork_point } } }]),
            )
            .await);
            let child_fork_point = mint(s).await;
            let child_excluded = mint(s).await;
            ok(commit(
                s,
                json!([
                    { "type": "entry", "value": entry(child_fork_point, child_id, "note", json!({})) },
                    { "type": "entry", "value": entry(child_excluded, child_id, "message", json!({})) },
                ]),
            )
            .await);
            let root_excluded_later = mint(s).await;
            ok(commit(
                s,
                json!([{ "type": "entry", "value": entry(root_excluded_later, root_id, "message", json!({})) }]),
            )
            .await);
            let grandchild_id = mint(s).await;
            ok(commit(
                s,
                json!([{ "type": "conversation", "value": { "id": grandchild_id, "parent": { "conversationId": child_id, "at": child_fork_point } } }]),
            )
            .await);
            let grandchild_head = mint(s).await;
            let grandchild_tail = mint(s).await;
            let grandchild_entries_seq = ok(commit(
                s,
                json!([
                    { "type": "entry", "value": entry(grandchild_head, grandchild_id, "marker", json!({ "head": grandchild_head })) },
                    { "type": "entry", "value": entry(grandchild_tail, grandchild_id, "message", json!({})) },
                ]),
            )
            .await);
            let child_excluded_later = mint(s).await;
            ok(commit(
                s,
                json!([{ "type": "entry", "value": entry(child_excluded_later, child_id, "message", json!({})) }]),
            )
            .await);

            let query = q(json!({ "conversationId": grandchild_id }));
            let first = ok(s.scan_entries(&query, 2, None, cx()).await);
            assert_eq!(ids(&first.items), v(json!([grandchild_tail, grandchild_head])));
            let second = ok(s.scan_entries(&query, 2, first.next.as_ref(), cx()).await);
            assert_eq!(ids(&second.items), v(json!([child_fork_point, root_fork_point])));
            let third = ok(s.scan_entries(&query, 2, second.next.as_ref(), cx()).await);
            assert_eq!(ids(&third.items), v(json!([root_first])));
            assert!(third.next.is_none());

            let current_marker =
                j(&ok(s.find_latest_head_marker(id(grandchild_id), None, cx()).await));
            assert_eq!(current_marker["id"], v(grandchild_head));
            assert_eq!(current_marker["head"], v(grandchild_head));
            let historical_marker = j(&ok(s
                .find_latest_head_marker(id(grandchild_id), Some(id(child_fork_point)), cx())
                .await));
            assert_eq!(historical_marker["id"], v(root_fork_point));
            assert_eq!(historical_marker["head"], v(root_first));
            assert!(ok(s
                .find_latest_head_marker(id(grandchild_id), Some(id(root_first)), cx())
                .await)
            .is_none());

            let active = q(json!({ "conversationId": grandchild_id, "minEntryId": current_marker["head"] }));
            let active_first = ok(s.scan_entries(&active, 1, None, cx()).await);
            assert_eq!(ids(&active_first.items), v(json!([grandchild_tail])));
            assert!(active_first.next.is_some());
            let active_second = ok(s
                .scan_entries(&active, 1, active_first.next.as_ref(), cx())
                .await);
            assert_eq!(ids(&active_second.items), v(json!([grandchild_head])));
            assert!(active_second.next.is_none());

            assert_eq!(
                ids(&ok(s
                    .scan_entries(
                        &q(json!({
                            "conversationId": grandchild_id,
                            "minEntryId": historical_marker["head"],
                            "maxEntryId": child_fork_point,
                        })),
                        10,
                        None,
                        cx(),
                    )
                    .await)
                .items),
                v(json!([child_fork_point, root_fork_point, root_first]))
            );

            let stored = ok(s.entry(id(root_first), cx()).await).expect("root entry");
            assert_eq!(j(&stored.entry), v(entry(root_first, root_id, "message", json!({}))));
            assert_eq!(n(&stored.commit_seq), root_entries_seq);
            let seq_of = |found: Option<crate::types::StoredEntry>| {
                n(&found.expect("entry is stored").commit_seq)
            };
            assert_eq!(seq_of(ok(s.entry(id(root_fork_point), cx()).await)), root_entries_seq);
            assert_eq!(seq_of(ok(s.entry(id(grandchild_head), cx()).await)), grandchild_entries_seq);
            assert_eq!(seq_of(ok(s.entry(id(grandchild_tail), cx()).await)), grandchild_entries_seq);
            assert!(ok(s.entry(id(999_999), cx()).await).is_none());

            let visible = ok(s.entry_in(id(grandchild_id), id(root_first), cx()).await)
                .expect("visible root entry");
            assert_eq!(j(&visible.entry), v(entry(root_first, root_id, "message", json!({}))));
            assert_eq!(n(&visible.commit_seq), root_entries_seq);
            assert_eq!(
                j(&ok(s.entry_in(id(grandchild_id), id(child_fork_point), cx()).await)
                    .expect("visible child entry")
                    .entry)["conversationId"],
                v(child_id)
            );
            assert_eq!(
                seq_of(ok(s.entry_in(id(grandchild_id), id(grandchild_tail), cx()).await)),
                grandchild_entries_seq
            );
            for (conversation, hidden) in [
                (grandchild_id, root_excluded_same_commit),
                (grandchild_id, root_excluded_later),
                (grandchild_id, child_excluded),
                (grandchild_id, child_excluded_later),
                (root_id, grandchild_head),
                (grandchild_id, 999_999),
            ] {
                assert!(ok(s.entry_in(id(conversation), id(hidden), cx()).await).is_none());
            }
            rejects(
                s.entry_in(id(999_999), id(root_first), cx()),
                "Unknown conversation",
            )
            .await;
            rejects(
                s.scan_entries(&q(json!({ "conversationId": 999_999 })), 10, None, cx()),
                "Unknown conversation",
            )
            .await;
        },
    );
}
