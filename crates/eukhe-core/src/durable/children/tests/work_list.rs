//! A split child given items hands back its work list: a child with items
//! left (left with a reason or never accounted for) settles `stopped`, and
//! its parent gets a report naming each item left, also after a reply of
//! its own (the pilot's children replied "items still not handled" and
//! read as a success); a child that did every item settles as before.

use super::super::work_list::{LeftItem, LeftWhy, Stopped};
use super::*;

/// One parent turn that splits `a` and `b`, the left half given `items`;
/// returns the left child's row once its task prompt went out.
async fn split_with_items(
    opened: &Opened,
    setup: &Setup,
    host: &FakeHost,
    items: &[&str],
) -> ChildRow {
    let reply = request_turn(
        opened,
        setup,
        "rlm.split",
        json!({
            "left": { "scope": ["a"], "task": "do the left half", "name": "left", "items": items },
            "right": { "scope": ["b"], "task": "do the right half", "name": "right" },
        }),
    )
    .await;
    assert!(!reply.starts_with("error:"), "{reply}");
    eventually(|| async { host.prompt_keys().len() == 2 }).await;
    let state = read_children(&opened.harness, ROOT_CONVERSATION_ID, cx())
        .await
        .unwrap();
    state
        .children
        .values()
        .find(|row| row.session_name == "left")
        .cloned()
        .expect("the split admitted the left child")
}

/// The left child replies, accounts for its items with `account`, and
/// answers; returns its row once its task ended.
async fn hand_back(
    opened: &Opened,
    host: &FakeHost,
    left: &ChildRow,
    account: ItemAccount,
) -> ChildRow {
    let marked = mark_child_replied(
        &opened.harness,
        ROOT_CONVERSATION_ID,
        vec![left.session_id.clone()],
    )
    .await
    .unwrap();
    assert!(marked, "the running child takes the reply's mark");
    lock(&host.state)
        .items
        .insert(left.session_id.clone(), account);
    host.settle(
        &left.session_id,
        RlmChildRunState::Answered {
            answer_preview: Some("done".to_owned()),
        },
        None,
    );
    opened
        .harness
        .wait_for_task(TaskId::<Value>::from_number(left.task_id), cx())
        .await
        .unwrap();
    opened.root.wait_for_idle(cx()).await.unwrap();
    row_of(&opened.harness, left.task_id).await.unwrap()
}

fn account(marks: &[(&str, ItemMark)]) -> ItemAccount {
    ItemAccount {
        items: marks
            .iter()
            .map(|(id, mark)| ((*id).to_owned(), mark.clone()))
            .collect(),
    }
}

/// A child given S2, M1 and U4 that did S2, left M1 with a reason and never
/// accounted for U4 settles `stopped` with both; its parent gets the
/// stopped report although the child replied, and its roster row and
/// `rlm.collect` name the items left. Its task prompt lists its items.
#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn a_child_with_items_left_hands_back_stopped_with_them() {
    let setup = setup();
    let host = FakeHost::new();
    let opened = open(Arc::new(MemoryStorage::new()), &setup, Arc::clone(&host)).await;
    let left = split_with_items(&opened, &setup, &host, &["S2", "M1", "U4"]).await;
    let prompt = lock(&host.state)
        .prompts
        .iter()
        .find(|prompt| prompt.session_id == left.session_id)
        .map(|prompt| prompt.prompt.clone());
    assert_eq!(
        prompt.as_deref(),
        Some(
            "do the left half\n\nItems: S2, M1, U4.\nAccount for each before your hand-back: `await rlm.items(done=[...], left={\"<id>\": \"<why>\"})`; call it again as items change (the latest account of an item counts). An item not accounted done reaches your parent as left, and your hand-back as stopped."
        )
    );
    setup.faux.append_responses(vec![answer("noted")]);
    let row = hand_back(
        &opened,
        &host,
        &left,
        account(&[
            ("S2", ItemMark::Done),
            (
                "M1",
                ItemMark::Left {
                    reason: "too risky".to_owned(),
                },
            ),
        ]),
    )
    .await;
    assert_eq!(
        (row.status, row.stopped),
        (
            ChildStatus::Stopped,
            Some(Stopped {
                items: 3,
                left: vec![
                    LeftItem {
                        id: "M1".to_owned(),
                        why: LeftWhy::Left {
                            reason: "too risky".to_owned(),
                        },
                    },
                    LeftItem {
                        id: "U4".to_owned(),
                        why: LeftWhy::Unaccounted,
                    },
                ],
            })
        )
    );
    assert_eq!(
        user_texts(&opened.root, "[child-").await,
        ["[child-stopped: 2 of 3 items left child:left]\n\nResume your work using the result below.\n\nStopped: 2 of 3 items left:\n- M1 (left: too risky)\n- U4 (no account)\n\nLast assistant text: done"]
    );
    let summary = "stopped: 2 of 3 items left: M1 (left: too risky), U4 (no account)";
    let listed = handle(&opened, "rlm.list_subagents", json!({}))
        .await
        .unwrap();
    let roster: Vec<(Value, Value)> = listed["subagents"]
        .as_array()
        .unwrap()
        .iter()
        .filter(|entry| entry["session_name"] == "left")
        .map(|entry| (entry["status"].clone(), entry["items_left"].clone()))
        .collect();
    assert_eq!(roster, [(json!("stopped"), json!(summary))]);
    let collected = handle(
        &opened,
        "rlm.collect",
        json!({ "targets": ["left"], "timeout_ms": 0 }),
    )
    .await
    .unwrap();
    assert_eq!(
        (
            collected["results"][0]["status"].clone(),
            collected["results"][0]["items_left"].clone()
        ),
        (json!("stopped"), json!(summary))
    );
    opened.harness.close(cx()).await.unwrap();
}

/// A child that accounted every item done and replied settles `done`
/// without a notice, as a child given no items does.
#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn a_child_that_did_every_item_settles_done() {
    let setup = setup();
    let host = FakeHost::new();
    let opened = open(Arc::new(MemoryStorage::new()), &setup, Arc::clone(&host)).await;
    let left = split_with_items(&opened, &setup, &host, &["S2", "M1"]).await;
    let row = hand_back(
        &opened,
        &host,
        &left,
        account(&[("S2", ItemMark::Done), ("M1", ItemMark::Done)]),
    )
    .await;
    assert_eq!((row.status, row.stopped), (ChildStatus::Done, None));
    assert_eq!(
        user_texts(&opened.root, "[child-").await,
        Vec::<String>::new()
    );
    opened.harness.close(cx()).await.unwrap();
}

/// `rlm.items` merges a child's account into its own document: a later
/// account of an item replaces the earlier one, and the run's outcome
/// reads it back; an item both done and left, or left without a reason,
/// is refused.
#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn rlm_items_keeps_the_latest_account_of_each_item() {
    let setup = setup();
    let opened = open(Arc::new(MemoryStorage::new()), &setup, FakeHost::new()).await;
    let first = handle(
        &opened,
        "rlm.items",
        json!({ "done": ["S2"], "left": { "M1": "too risky" } }),
    )
    .await
    .unwrap();
    let second = handle(&opened, "rlm.items", json!({ "done": ["M1"] }))
        .await
        .unwrap();
    let refused = [
        json!({ "done": ["U4"], "left": { "U4": "later" } }),
        json!({ "left": { "U4": " " } }),
    ];
    let mut errors = Vec::new();
    for data in refused {
        errors.push(
            handle(&opened, "rlm.items", data)
                .await
                .map_err(|error| error.to_string())
                .err(),
        );
    }
    assert_eq!(
        (
            first,
            second,
            errors,
            super::super::items_account(&opened.harness, ROOT_CONVERSATION_ID, cx())
                .await
                .unwrap()
        ),
        (
            json!({ "accounted": 2 }),
            json!({ "accounted": 2 }),
            vec![
                Some("rlm.items names U4 both done and left".to_owned()),
                Some("rlm.items left needs a reason for U4".to_owned()),
            ],
            Some(account(&[("S2", ItemMark::Done), ("M1", ItemMark::Done)])),
        )
    );
    opened.harness.close(cx()).await.unwrap();
}

/// A child with items left that an abort meets after its integration,
/// while its checks wait, stays `stopped` with them: the abort keeps what
/// landed and never reads the child as done.
#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn an_abort_during_the_checks_keeps_a_stopped_child_stopped() {
    let setup = setup();
    let host = FakeHost::new();
    lock(&host.state).handback = Some(RlmChildHandback {
        handback: ScopedHandback {
            taken: vec!["a/x.txt".to_owned()],
            outside: Vec::new(),
            conflicts: Vec::new(),
            kept: None,
            patch: vec![None, Some(1), None],
        },
        child_check: CheckRun::None,
        parent_check: CheckRun::None,
    });
    host.checks_open.send_replace(false);
    let opened = open(Arc::new(MemoryStorage::new()), &setup, Arc::clone(&host)).await;
    let left = split_with_items(&opened, &setup, &host, &["S2", "M1"]).await;
    lock(&host.state)
        .items
        .insert(left.session_id.clone(), account(&[("S2", ItemMark::Done)]));
    host.settle(
        &left.session_id,
        RlmChildRunState::Answered {
            answer_preview: Some("done".to_owned()),
        },
        None,
    );
    eventually(|| async {
        row_of(&opened.harness, left.task_id)
            .await
            .is_some_and(|row| row.handback.is_some())
    })
    .await;

    crate::durable::children::cancel_tree(&opened.harness, ROOT_CONVERSATION_ID, cx())
        .await
        .unwrap();
    opened
        .harness
        .wait_for_task(TaskId::<Value>::from_number(left.task_id), cx())
        .await
        .unwrap();
    let row = row_of(&opened.harness, left.task_id).await.unwrap();
    assert_eq!(
        (row.status, row.stopped),
        (
            ChildStatus::Stopped,
            Some(Stopped {
                items: 2,
                left: vec![LeftItem {
                    id: "M1".to_owned(),
                    why: LeftWhy::Unaccounted,
                }],
            })
        )
    );
    opened.root.wait_for_idle(cx()).await.unwrap();
    opened.harness.close(cx()).await.unwrap();
}

/// A help leaf given items (`rlm.spawn` `items`) that did one of two
/// hands back stopped with the other, as a split child does.
#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn a_help_leaf_with_items_left_hands_back_stopped() {
    let setup = setup();
    let host = FakeHost::new();
    let opened = open(Arc::new(MemoryStorage::new()), &setup, Arc::clone(&host)).await;
    let reply = spawn_turn(
        &opened,
        &setup,
        "review the handlers",
        json!({ "name": "reader", "items": ["R1", "R2"] }),
    )
    .await;
    assert!(reply.contains("rlm_child_id"), "{reply}");
    eventually(|| async { !host.prompt_keys().is_empty() }).await;
    let leaf = read_children(&opened.harness, ROOT_CONVERSATION_ID, cx())
        .await
        .unwrap()
        .children
        .values()
        .find(|row| row.session_name == "reader")
        .cloned()
        .expect("the spawn admitted the leaf");
    setup.faux.append_responses(vec![answer("noted")]);
    let row = hand_back(&opened, &host, &leaf, account(&[("R1", ItemMark::Done)])).await;
    assert_eq!(
        (row.status, row.stopped),
        (
            ChildStatus::Stopped,
            Some(Stopped {
                items: 2,
                left: vec![LeftItem {
                    id: "R2".to_owned(),
                    why: LeftWhy::Unaccounted,
                }],
            })
        )
    );
    assert_eq!(
        user_texts(&opened.root, "[child-").await,
        ["[child-stopped: 1 of 2 items left child:reader]\n\nResume your work using the result below.\n\nStopped: 1 of 2 items left:\n- R2 (no account)\n\nLast assistant text: done"]
    );
    opened.harness.close(cx()).await.unwrap();
}
