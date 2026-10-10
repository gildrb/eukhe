//! Document lifecycle, history, copy, and indexing cases, then the
//! cross-table identity, ID namespace, and close cases.

use eukhe_chord::json::JsonValue;
use serde_json::json;

use super::at;
use super::{
    assert_match_object, commit, create_root, cx, entry, id, ids, j, mint, ok, pending_task, q,
    rejects, v, with, Cases, ROOT,
};
use crate::types::{Storage, StoredDocument};

pub(super) fn add_cases(cases: &mut Cases) {
    add_history_cases(cases);
    add_copy_case(cases);
    add_current_only_case(cases);
    add_address_case(cases);
    add_atomic_cases(cases);
    add_identity_case(cases);
    add_namespace_cases(cases);
}

/// `storage.document(id, at)`, `at` being `"current"` or a sequence.
async fn document(
    s: &dyn Storage,
    document_id: u64,
    at: serde_json::Value,
) -> Option<StoredDocument> {
    ok(s.document(id(document_id), q(at), cx()).await)
}

/// `storage.document(id, at)` as JSON (`null` when absent).
async fn document_json(s: &dyn Storage, document_id: u64, at: serde_json::Value) -> JsonValue {
    j(&document(s, document_id, at).await)
}

/// `storage.findDocument(address, at)` as JSON (`null` when absent).
async fn find_document(
    s: &dyn Storage,
    address: serde_json::Value,
    at: serde_json::Value,
) -> JsonValue {
    j(&ok(s.find_document(&q(address), q(at), cx()).await))
}

/// The IDs of `storage.scanDocuments(query, limit)`.
async fn scan_document_ids(s: &dyn Storage, query: serde_json::Value, limit: usize) -> JsonValue {
    ids(&ok(s.scan_documents(&q(query), limit, None, cx()).await).items)
}

#[expect(
    clippy::too_many_lines,
    reason = "TS conformance cases, kept whole and in TS order"
)]
fn add_history_cases(cases: &mut Cases) {
    cases.case(
        "reconstructs rewindable documents and preserves half-open incarnations",
        |storage| async move {
            let s = &*storage;
            let root_id = create_root(s).await;
            let first_id = mint(s).await;
            let first_record = json!({
                "id": first_id,
                "kind": "conversation.notes",
                "scope": { "kind": "conversation", "conversationId": root_id },
                "history": "rewindable",
                "fork": "asOf",
            });
            let mut initial = v(json!({ "items": ["a"], "nested": { "count": 1 } }));
            let created_at = ok(commit(
                s,
                json!([{ "type": "document.create", "record": first_record, "content": { "kind": "base", "version": 1, "value": initial } }]),
            )
            .await);
            let mut appended = v(json!(["b"]));
            let ops = json!([["p", ["items"], 1, 0, appended], ["s", ["nested", "count"], 2]]);
            let changed_at = ok(commit(
                s,
                json!([{ "type": "document.change", "id": first_id, "content": { "kind": "delta", "version": 1, "ops": ops } }]),
            )
            .await);

            // Rust adaptation: copy-on-write mutation of the caller's values.
            at(&mut initial, &["items"])
                .as_array_mut()
                .expect("an array")
                .push(v("caller mutation"));
            appended
                .as_array_mut()
                .expect("an array")
                .push(v("caller mutation"));
            assert_match_object(
                &document_json(s, first_id, json!(created_at)).await,
                &v(json!({ "version": 1, "value": { "items": ["a"], "nested": { "count": 1 } }, "deltasSinceBase": 0 })),
            );
            let mut changed = document_json(s, first_id, json!(changed_at)).await;
            assert_eq!(
                changed["value"],
                v(json!({ "items": ["a", "b"], "nested": { "count": 2 } }))
            );
            assert_eq!(changed["deltasSinceBase"], v(1));
            at(&mut changed, &["value", "items"])
                .as_array_mut()
                .expect("an array")
                .push(v("read mutation"));
            assert_eq!(
                document_json(s, first_id, json!("current")).await["value"],
                v(json!({ "items": ["a", "b"], "nested": { "count": 2 } }))
            );

            let checkpoint_at = ok(commit(
                s,
                json!([{ "type": "document.change", "id": first_id, "content": { "kind": "base", "version": 2, "value": { "items": ["checkpoint"], "nested": { "count": 3 } } } }]),
            )
            .await);
            let replaced_at = ok(commit(
                s,
                json!([{ "type": "document.change", "id": first_id, "content": { "kind": "delta", "version": 2, "ops": [["r", { "items": ["replacement"], "nested": { "count": 4 } }]] } }]),
            )
            .await);
            assert_match_object(
                &document_json(s, first_id, json!(changed_at)).await,
                &v(json!({ "version": 1, "value": { "items": ["a", "b"], "nested": { "count": 2 } } })),
            );
            assert_match_object(
                &document_json(s, first_id, json!(checkpoint_at)).await,
                &v(json!({ "version": 2, "value": { "items": ["checkpoint"], "nested": { "count": 3 } }, "deltasSinceBase": 0 })),
            );
            assert_match_object(
                &document_json(s, first_id, json!(replaced_at)).await,
                &v(json!({ "value": { "items": ["replacement"], "nested": { "count": 4 } }, "deltasSinceBase": 1 })),
            );
            assert_eq!(
                document_json(s, first_id, json!("current")).await["deltasSinceBase"],
                v(1)
            );

            let second_id = mint(s).await;
            let retired_at = ok(commit(
                s,
                json!([
                    {
                        "type": "document.create",
                        "record": with(first_record.clone(), json!({ "id": second_id })),
                        "content": { "kind": "base", "version": 1, "value": { "items": ["new"] } },
                    },
                    { "type": "document.retire", "id": first_id },
                    { "type": "document.change", "id": first_id, "content": { "kind": "delta", "version": 2, "ops": [["s", ["retiring"], true]] } },
                ]),
            )
            .await);
            let address = json!({ "kind": first_record["kind"], "scope": first_record["scope"] });
            assert_eq!(
                find_document(s, address.clone(), json!(changed_at)).await["id"],
                v(first_id)
            );
            assert_match_object(
                &find_document(s, address, json!(retired_at)).await,
                &v(json!({ "id": second_id, "createdAt": retired_at })),
            );
            assert_eq!(
                scan_document_ids(s, json!({ "scope": first_record["scope"], "at": changed_at }), 10).await,
                v(json!([first_id]))
            );
            assert_eq!(
                scan_document_ids(s, json!({ "scope": first_record["scope"], "at": retired_at }), 10).await,
                v(json!([second_id]))
            );
            assert!(document(s, first_id, json!(retired_at)).await.is_none());
            assert_eq!(
                document_json(s, second_id, json!("current")).await["value"],
                v(json!({ "items": ["new"] }))
            );
        },
    );

    cases.case(
        "streams long document tails across root replacement deltas",
        |storage| async move {
            let s = &*storage;
            let root_id = create_root(s).await;
            let document_id = mint(s).await;
            let record = json!({
                "id": document_id,
                "kind": "conversation.long-tail",
                "scope": { "kind": "conversation", "conversationId": root_id },
                "history": "rewindable",
                "fork": "asOf",
            });
            let rows = |value: &dyn Fn(u64) -> serde_json::Value| -> serde_json::Value {
                (0..512).map(value).collect()
            };
            let initial = json!({
                "revision": 0,
                "rows": rows(&|value| json!({ "value": value, "stable": format!("row-{value}") })),
            });
            let created_at = ok(commit(
                s,
                json!([{ "type": "document.create", "record": record, "content": { "kind": "base", "version": 1, "value": initial } }]),
            )
            .await);
            let mut before_replacement = initial.clone();
            let mut before_replacement_at = created_at;
            for revision in 1..=24_i64 {
                let index = revision * 17 % 512;
                before_replacement["rows"][usize::try_from(index).expect("small index")]["value"] = json!(-revision);
                before_replacement["revision"] = json!(revision);
                before_replacement_at = ok(commit(s, set_row_change(document_id, index, revision)).await);
            }

            let mut replacement = json!({
                "revision": 100,
                "rows": rows(&|value| json!({ "value": 10_000 + value, "stable": format!("new-{value}") })),
            });
            let replacement_snapshot = replacement.clone();
            let replacement_at = ok(commit(
                s,
                json!([{ "type": "document.change", "id": document_id, "content": { "kind": "delta", "version": 1, "ops": [["r", replacement]] } }]),
            )
            .await);
            replacement["rows"][0]["value"] = json!(-999);

            let mut current = replacement_snapshot.clone();
            for revision in 101..=124_i64 {
                let index = revision * 19 % 512;
                current["rows"][usize::try_from(index).expect("small index")]["value"] = json!(-revision);
                current["revision"] = json!(revision);
                ok(commit(s, set_row_change(document_id, index, revision)).await);
            }

            assert_eq!(document_json(s, document_id, json!(created_at)).await["value"], v(initial));
            assert_eq!(
                document_json(s, document_id, json!(before_replacement_at)).await["value"],
                v(before_replacement)
            );
            assert_eq!(
                document_json(s, document_id, json!(replacement_at)).await["value"],
                v(replacement_snapshot)
            );
            let mut read = document_json(s, document_id, json!("current")).await;
            assert_eq!(read["value"], v(current.clone()));
            at(&mut read, &["value", "rows", "0"])
                .as_object_mut()
                .expect("an object")
                .insert("value", v(-1_000));
            assert_eq!(
                document_json(s, document_id, json!("current")).await["value"],
                v(current)
            );
        },
    );
}

/// One delta setting `rows[index].value = -revision` and `revision`.
fn set_row_change(document_id: u64, index: i64, revision: i64) -> serde_json::Value {
    json!([{
        "type": "document.change",
        "id": document_id,
        "content": {
            "kind": "delta",
            "version": 1,
            "ops": [["s", ["rows", index, "value"], -revision], ["s", ["revision"], revision]],
        },
    }])
}

#[expect(clippy::too_many_lines, reason = "one TS conformance case, kept whole")]
fn add_copy_case(cases: &mut Cases) {
    cases.case(
        "copies stored document bases independently and rejects ambiguous sources",
        |storage| async move {
            let s = &*storage;
            let root_id = create_root(s).await;
            let child_id = mint(s).await;
            let second_child_id = mint(s).await;
            ok(commit(
                s,
                json!([
                    { "type": "conversation", "value": { "id": child_id } },
                    { "type": "conversation", "value": { "id": second_child_id } },
                ]),
            )
            .await);
            let source_id = mint(s).await;
            let source_record = json!({
                "id": source_id,
                "kind": "copy.source",
                "scope": { "kind": "conversation", "conversationId": root_id },
                "history": "rewindable",
                "fork": "asOf",
            });
            let created_at = ok(commit(
                s,
                json!([{ "type": "document.create", "record": source_record, "content": { "kind": "base", "version": 2, "value": { "count": 1, "rows": [{ "value": "base" }] } } }]),
            )
            .await);
            ok(commit(
                s,
                json!([{
                    "type": "document.change",
                    "id": source_id,
                    "content": { "kind": "delta", "version": 2, "ops": [["s", ["count"], 2], ["p", ["rows"], 1, 0, [{ "value": "current" }]]] },
                }]),
            )
            .await);
            let historical_copy_id = mint(s).await;
            let current_copy_id = mint(s).await;
            let retired_copy_id = mint(s).await;
            let child_record = |document_id: u64, conversation_id: u64| {
                json!({
                    "id": document_id,
                    "kind": "copy.source",
                    "scope": { "kind": "conversation", "conversationId": conversation_id },
                    "history": "rewindable",
                    "fork": "asOf",
                })
            };
            ok(commit(
                s,
                json!([
                    { "type": "document.copy", "record": child_record(historical_copy_id, child_id), "source": { "id": source_id, "at": created_at } },
                    { "type": "document.copy", "record": child_record(current_copy_id, second_child_id), "source": { "id": source_id, "at": "current" } },
                    { "type": "document.copy", "record": child_record(retired_copy_id, root_id), "source": { "id": source_id, "at": "current" } },
                    { "type": "document.retire", "id": retired_copy_id },
                ]),
            )
            .await);
            assert_match_object(
                &document_json(s, historical_copy_id, json!("current")).await,
                &v(json!({ "version": 2, "value": { "count": 1, "rows": [{ "value": "base" }] } })),
            );
            let current_copy = json!({ "count": 2, "rows": [{ "value": "base" }, { "value": "current" }] });
            assert_match_object(
                &document_json(s, current_copy_id, json!("current")).await,
                &v(json!({ "version": 2, "value": current_copy })),
            );
            assert!(document(s, retired_copy_id, json!("current")).await.is_none());

            ok(commit(
                s,
                json!([
                    { "type": "document.change", "id": source_id, "content": { "kind": "base", "version": 2, "value": { "count": 99, "rows": [] } } },
                    { "type": "document.retire", "id": source_id },
                ]),
            )
            .await);
            assert_eq!(
                document_json(s, current_copy_id, json!("current")).await["value"],
                v(current_copy.clone())
            );

            let latest_source_id = mint(s).await;
            let latest_copy_id = mint(s).await;
            let latest_source = json!({
                "id": latest_source_id,
                "kind": "copy.latest",
                "scope": { "kind": "conversation", "conversationId": root_id },
                "history": "latest",
                "fork": "current",
            });
            ok(commit(
                s,
                json!([{ "type": "document.create", "record": latest_source, "content": { "kind": "base", "version": 4, "value": { "retained": "copy" } } }]),
            )
            .await);
            ok(commit(
                s,
                json!([{
                    "type": "document.copy",
                    "record": with(latest_source.clone(), json!({ "id": latest_copy_id, "scope": { "kind": "conversation", "conversationId": child_id } })),
                    "source": { "id": latest_source_id, "at": "current" },
                }]),
            )
            .await);
            ok(commit(
                s,
                json!([
                    { "type": "document.change", "id": latest_source_id, "content": { "kind": "base", "version": 4, "value": { "retained": "source-only" } } },
                    { "type": "document.retire", "id": latest_source_id },
                ]),
            )
            .await);
            assert_match_object(
                &document_json(s, latest_copy_id, json!("current")).await,
                &v(json!({ "version": 4, "value": { "retained": "copy" } })),
            );

            let conflict_id = mint(s).await;
            let conflict_error = commit(
                s,
                json!([
                    { "type": "document.copy", "record": child_record(conflict_id, child_id), "source": { "id": current_copy_id, "at": "current" } },
                    { "type": "document.retire", "id": current_copy_id },
                ]),
            )
            .await;
            // Rejected without effect: the copy and the retirement in the same batch are both absent.
            assert!(conflict_error.is_err());
            assert!(document(s, conflict_id, json!("current")).await.is_none());
            assert_eq!(
                document_json(s, current_copy_id, json!("current")).await["value"],
                v(current_copy)
            );

            let mismatch_id = mint(s).await;
            let mismatch_error = commit(
                s,
                json!([{
                    "type": "document.copy",
                    "record": with(child_record(mismatch_id, child_id), json!({ "kind": "copy.mismatch" })),
                    "source": { "id": current_copy_id, "at": "current" },
                }]),
            )
            .await;
            assert!(mismatch_error.is_err());
            assert!(document(s, mismatch_id, json!("current")).await.is_none());
        },
    );
}

fn add_current_only_case(cases: &mut Cases) {
    cases.case(
        "uses bases for version transitions and rejects historical reads of current-only documents",
        |storage| async move {
            let s = &*storage;
            create_root(s).await;
            let document_id = mint(s).await;
            let record = json!({ "id": document_id, "kind": "session.settings", "scope": { "kind": "session" } });
            ok(commit(
                s,
                json!([{ "type": "document.create", "record": record, "content": { "kind": "base", "version": 1, "value": { "count": 1 } } }]),
            )
            .await);
            ok(commit(
                s,
                json!([{ "type": "document.change", "id": document_id, "content": { "kind": "delta", "version": 1, "ops": [["s", ["count"], 2]] } }]),
            )
            .await);
            let migrated_at = ok(commit(
                s,
                json!([{ "type": "document.change", "id": document_id, "content": { "kind": "base", "version": 2, "value": { "count": 3 } } }]),
            )
            .await);
            assert_match_object(
                &document_json(s, document_id, json!("current")).await,
                &v(json!({ "version": 2, "value": { "count": 3 } })),
            );
            rejects(
                s.document(id(document_id), q(json!(migrated_at)), cx()),
                "does not retain historical content",
            )
            .await;

            rejects(
                commit(
                    s,
                    json!([{ "type": "document.change", "id": document_id, "content": { "kind": "delta", "version": 1, "ops": [["s", ["count"], 4]] } }]),
                ),
                "version transition requires a base",
            )
            .await;
            assert_eq!(
                document_json(s, document_id, json!("current")).await["value"],
                v(json!({ "count": 3 }))
            );
            ok(commit(s, json!([{ "type": "document.retire", "id": document_id }])).await);
            assert!(document(s, document_id, json!("current")).await.is_none());
        },
    );
}

fn add_address_case(cases: &mut Cases) {
    cases.case(
        "indexes logical addresses and exact-scope scans independently",
        |storage| async move {
            let s = &*storage;
            let root_id = create_root(s).await;
            let first_id = mint(s).await;
            let second_id = mint(s).await;
            let conversation_id = mint(s).await;
            let task_id = mint(s).await;
            let task_singleton_id = mint(s).await;
            let task_family_id = mint(s).await;
            let task_other_kind_id = mint(s).await;
            let created_at = ok(commit(
                s,
                json!([
                    { "type": "task", "value": pending_task(task_id, root_id) },
                    {
                        "type": "document.create",
                        "record": { "id": first_id, "kind": "cache", "scope": { "kind": "session" }, "key": "__proto__" },
                        "content": { "kind": "base", "version": 1, "value": { "owner": "first" } },
                    },
                    {
                        "type": "document.create",
                        "record": { "id": second_id, "kind": "cache", "scope": { "kind": "session" }, "key": "constructor" },
                        "content": { "kind": "base", "version": 1, "value": { "owner": "second" } },
                    },
                    {
                        "type": "document.create",
                        "record": {
                            "id": conversation_id,
                            "kind": "cache",
                            "scope": { "kind": "conversation", "conversationId": root_id },
                            "history": "latest",
                            "fork": "current",
                            "key": "__proto__",
                        },
                        "content": { "kind": "base", "version": 1, "value": { "owner": "conversation" } },
                    },
                    {
                        "type": "document.create",
                        "record": { "id": task_singleton_id, "kind": "task.cache", "scope": { "kind": "task", "taskId": task_id } },
                        "content": { "kind": "base", "version": 1, "value": { "owner": "singleton" } },
                    },
                    {
                        "type": "document.create",
                        "record": { "id": task_family_id, "kind": "task.cache", "scope": { "kind": "task", "taskId": task_id }, "key": "member" },
                        "content": { "kind": "base", "version": 1, "value": { "owner": "family" } },
                    },
                    {
                        "type": "document.create",
                        "record": { "id": task_other_kind_id, "kind": "task.other", "scope": { "kind": "task", "taskId": task_id } },
                        "content": { "kind": "base", "version": 1, "value": { "owner": "other" } },
                    },
                ]),
            )
            .await);

            assert_eq!(
                find_document(s, json!({ "kind": "cache", "scope": { "kind": "session" }, "key": "__proto__" }), json!("current")).await["id"],
                v(first_id)
            );
            let session = q(json!({ "scope": { "kind": "session" }, "at": "current" }));
            assert_eq!(ok(s.scan_documents(&session, 1, None, cx()).await).items.len(), 1);
            let first = ok(s.scan_documents(&session, 1, None, cx()).await);
            let second = ok(s.scan_documents(&session, 1, first.next.as_ref(), cx()).await);
            let mut both = first.items;
            both.extend(second.items);
            assert_eq!(ids(&both), v(json!([first_id, second_id])));
            assert_eq!(
                scan_document_ids(s, json!({ "scope": { "kind": "conversation", "conversationId": root_id }, "at": "current" }), 10).await,
                v(json!([conversation_id]))
            );
            assert_eq!(
                find_document(s, json!({ "kind": "task.cache", "scope": { "kind": "task", "taskId": task_id } }), json!("current")).await["id"],
                v(task_singleton_id)
            );
            assert_eq!(
                find_document(s, json!({ "kind": "task.cache", "scope": { "kind": "task", "taskId": task_id }, "key": "member" }), json!("current")).await["id"],
                v(task_family_id)
            );
            assert_eq!(
                scan_document_ids(s, json!({ "scope": { "kind": "task", "taskId": task_id }, "at": "current", "kind": "task.cache" }), 10).await,
                v(json!([task_singleton_id, task_family_id]))
            );
            rejects(
                s.document(id(task_singleton_id), q(json!(created_at)), cx()),
                "does not retain historical content",
            )
            .await;
        },
    );
}

#[expect(
    clippy::too_many_lines,
    reason = "TS conformance cases, kept whole and in TS order"
)]
fn add_atomic_cases(cases: &mut Cases) {
    cases.case(
        "keeps document lifecycle failures atomic and gives create-plus-retire an empty lifetime",
        |storage| async move {
            let s = &*storage;
            let root_id = create_root(s).await;
            let first_id = mint(s).await;
            let second_id = mint(s).await;
            let record = json!({ "id": first_id, "kind": "singleton", "scope": { "kind": "session" } });
            ok(commit(
                s,
                json!([{ "type": "document.create", "record": record, "content": { "kind": "base", "version": 1, "value": { "value": 1 } } }]),
            )
            .await);
            rejects(
                commit(
                    s,
                    json!([
                        { "type": "document.create", "record": with(record.clone(), json!({ "id": second_id })), "content": { "kind": "base", "version": 1, "value": { "value": 2 } } },
                        { "type": "document.change", "id": first_id, "content": { "kind": "delta", "version": 1, "ops": [] } },
                    ]),
                ),
                "already has a current incarnation",
            )
            .await;
            assert_eq!(
                document_json(s, first_id, json!("current")).await["value"],
                v(json!({ "value": 1 }))
            );
            assert!(document(s, second_id, json!("current")).await.is_none());

            let empty_id = mint(s).await;
            let empty_at = ok(commit(
                s,
                json!([
                    {
                        "type": "document.create",
                        "record": {
                            "id": empty_id,
                            "kind": "singleton",
                            "key": "empty",
                            "scope": { "kind": "conversation", "conversationId": root_id },
                            "history": "rewindable",
                            "fork": "initial",
                        },
                        "content": { "kind": "base", "version": 1, "value": {} },
                    },
                    { "type": "document.retire", "id": empty_id },
                ]),
            )
            .await);
            assert!(document(s, empty_id, json!("current")).await.is_none());
            assert!(document(s, empty_id, json!(empty_at)).await.is_none());
            assert!(find_document(
                s,
                json!({ "kind": "singleton", "scope": { "kind": "conversation", "conversationId": root_id }, "key": "empty" }),
                json!(empty_at),
            )
            .await
            .is_null());
        },
    );

    cases.case(
        "rolls back record tables and secondary indexes when a document command fails",
        |storage| async move {
            let s = &*storage;
            let root_id = create_root(s).await;
            let task_id = mint(s).await;
            let submission_id = mint(s).await;
            let document_id = mint(s).await;
            let task = pending_task(task_id, root_id);
            let submission = json!({ "id": submission_id, "conversationId": root_id, "requestId": "atomic", "type": "input", "status": "queued" });
            let record = json!({ "id": document_id, "kind": "atomic", "scope": { "kind": "session" } });
            let baseline_seq = ok(commit(
                s,
                json!([
                    { "type": "task", "value": task },
                    { "type": "submission", "value": submission },
                    { "type": "document.create", "record": record, "content": { "kind": "base", "version": 1, "value": { "count": 1 } } },
                ]),
            )
            .await);

            let entry_id = mint(s).await;
            let conflicting_document_id = mint(s).await;
            rejects(
                commit(
                    s,
                    json!([
                        { "type": "task", "value": with(task.clone(), json!({ "state": { "status": "running", "checkpoint": { "phase": "effect" } } })) },
                        { "type": "submission", "value": with(submission.clone(), json!({ "status": "unanswered", "reason": "failed" })) },
                        { "type": "entry", "value": entry(entry_id, root_id, "transient", json!({})) },
                        {
                            "type": "document.create",
                            "record": with(record.clone(), json!({ "id": conflicting_document_id })),
                            "content": { "kind": "base", "version": 1, "value": { "count": 2 } },
                        },
                    ]),
                ),
                "already has a current incarnation",
            )
            .await;

            assert_eq!(j(&ok(s.task(id(task_id), cx()).await)), v(task.clone()));
            assert_eq!(
                j(&ok(s.scan_tasks(&q(json!({ "status": "pending" })), 10, None, cx()).await).items),
                v(json!([task]))
            );
            assert_eq!(
                j(&ok(s.submission_by_request(id(root_id), "atomic", cx()).await)),
                v(submission)
            );
            assert!(ok(s.entry(id(entry_id), cx()).await).is_none());
            assert!(document(s, conflicting_document_id, json!("current")).await.is_none());
            assert_eq!(
                find_document(s, json!({ "kind": record["kind"], "scope": record["scope"] }), json!("current")).await["id"],
                v(document_id)
            );
            let after_rollback_seq = ok(commit(
                s,
                json!([{ "type": "document.change", "id": document_id, "content": { "kind": "delta", "version": 1, "ops": [["s", ["count"], 3]] } }]),
            )
            .await);
            assert!(after_rollback_seq > baseline_seq);
        },
    );
}

/// Rust adaptation: Rust strings cannot hold the TS lone surrogates
/// `"\ud800"`/`"\ud801"`, so the identities are the astral characters whose
/// UTF-16 forms start with those surrogates; lossless indexing must still
/// keep them apart.
fn add_identity_case(cases: &mut Cases) {
    cases.case("keeps indexed string identities lossless", |storage| async move {
        let s = &*storage;
        let root_id = create_root(s).await;
        let first = "\u{10000}";
        let second = "\u{10400}";
        let first_task_id = mint(s).await;
        let second_task_id = mint(s).await;
        let first_submission_id = mint(s).await;
        let second_submission_id = mint(s).await;
        let first_kind_document_id = mint(s).await;
        let second_kind_document_id = mint(s).await;
        let first_key_document_id = mint(s).await;
        let second_key_document_id = mint(s).await;
        ok(commit(
            s,
            json!([
                { "type": "task", "value": with(pending_task(first_task_id, root_id), json!({ "kind": first })) },
                { "type": "task", "value": with(pending_task(second_task_id, root_id), json!({ "kind": second })) },
                { "type": "submission", "value": { "id": first_submission_id, "conversationId": root_id, "requestId": first, "type": "input", "status": "queued" } },
                { "type": "submission", "value": { "id": second_submission_id, "conversationId": root_id, "requestId": second, "type": "input", "status": "queued" } },
                {
                    "type": "document.create",
                    "record": { "id": first_kind_document_id, "kind": first, "scope": { "kind": "session" } },
                    "content": { "kind": "base", "version": 1, "value": { "identity": "first kind" } },
                },
                {
                    "type": "document.create",
                    "record": { "id": second_kind_document_id, "kind": second, "scope": { "kind": "session" } },
                    "content": { "kind": "base", "version": 1, "value": { "identity": "second kind" } },
                },
                {
                    "type": "document.create",
                    "record": { "id": first_key_document_id, "kind": "family", "key": first, "scope": { "kind": "session" } },
                    "content": { "kind": "base", "version": 1, "value": { "identity": "first key" } },
                },
                {
                    "type": "document.create",
                    "record": { "id": second_key_document_id, "kind": "family", "key": second, "scope": { "kind": "session" } },
                    "content": { "kind": "base", "version": 1, "value": { "identity": "second key" } },
                },
            ]),
        )
        .await);

        assert_eq!(
            ids(&ok(s.scan_tasks(&q(json!({ "kind": first })), 10, None, cx()).await).items),
            v(json!([first_task_id]))
        );
        assert_eq!(
            ids(&ok(s.scan_tasks(&q(json!({ "kind": second })), 10, None, cx()).await).items),
            v(json!([second_task_id]))
        );
        assert_eq!(j(&ok(s.task(id(first_task_id), cx()).await))["kind"], v(first));
        assert_eq!(j(&ok(s.task(id(second_task_id), cx()).await))["kind"], v(second));
        let by_first = j(&ok(s.submission_by_request(id(root_id), first, cx()).await));
        assert_eq!(by_first["requestId"], v(first));
        assert_eq!(by_first["id"], v(first_submission_id));
        assert_eq!(
            j(&ok(s.submission_by_request(id(root_id), second, cx()).await))["id"],
            v(second_submission_id)
        );
        assert_eq!(
            find_document(s, json!({ "kind": first, "scope": { "kind": "session" } }), json!("current")).await["id"],
            v(first_kind_document_id)
        );
        assert_eq!(
            find_document(s, json!({ "kind": second, "scope": { "kind": "session" } }), json!("current")).await["id"],
            v(second_kind_document_id)
        );
        assert_eq!(
            find_document(s, json!({ "kind": "family", "key": first, "scope": { "kind": "session" } }), json!("current")).await["id"],
            v(first_key_document_id)
        );
        assert_eq!(
            find_document(s, json!({ "kind": "family", "key": second, "scope": { "kind": "session" } }), json!("current")).await["id"],
            v(second_key_document_id)
        );
        assert_eq!(
            scan_document_ids(s, json!({ "scope": { "kind": "session" }, "at": "current", "kind": first }), 10).await,
            v(json!([first_kind_document_id]))
        );
    });
}

fn add_namespace_cases(cases: &mut Cases) {
    cases.case(
        "keeps one global record ID namespace and rejects exhausted ID minting",
        |storage| async move {
            let s = &*storage;
            let root_id = create_root(s).await;
            let explicit_entry_id = 100;
            ok(commit(
                s,
                json!([{ "type": "entry", "value": entry(explicit_entry_id, root_id, "message", json!({})) }]),
            )
            .await);
            assert_eq!(mint(s).await, 101);
            rejects(
                commit(
                    s,
                    json!([{ "type": "task", "value": pending_task(explicit_entry_id, root_id) }]),
                ),
                &format!("ID {explicit_entry_id} already belongs to entry"),
            )
            .await;

            ok(commit(
                s,
                json!([{ "type": "entry", "value": entry(9_007_199_254_740_991, root_id, "last-id", json!({})) }]),
            )
            .await);
            rejects(s.mint_id(), "ID space is exhausted").await;
            rejects(s.mint_id(), "ID space is exhausted").await;
        },
    );

    cases.case(
        "rejects every operation after close",
        |storage| async move {
            let s = &*storage;
            create_root(s).await;
            ok(s.close(cx()).await);
            rejects(s.conversation(id(ROOT), cx()), "closed").await;
            rejects(s.commit(&[], cx()), "closed").await;
            rejects(s.mint_id(), "closed").await;
        },
    );
}
