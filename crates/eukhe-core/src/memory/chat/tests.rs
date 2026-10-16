//! The planner's merge order, sawtooths, compaction view and work queue
//! are secured by the Bend laws (`LAWS.bend`, `PROOF.bend`) and by the
//! bridge test ([`super::bridge`]), which runs this code and the Bend model
//! on the same scenarios. What stays here is what the model leaves out:
//! node steps, zoom, free nodes, and the load from the logs.

use super::*;
use crate::memory::store::MergeRecord;

fn meta(kind: Kind) -> MessageMeta {
    MessageMeta {
        kind,
        size: 0,
        date: String::new(),
        file: 0,
        offset: 0,
        len: 0,
    }
}

fn chat_with(total: u64) -> Chat {
    let mut chat = Chat::default();
    for _ in 0..total {
        chat.push_message(meta(Kind::User));
    }
    chat
}

fn part(l: u32, i: u64) -> Part {
    Part { l, i }
}

/// A message compresses its own text; a merge joins its built halves.
#[test]
fn a_node_is_built_from_its_message_or_its_halves() {
    let mut chat = chat_with(4);
    chat.insert_node(part(0, 0), "a");
    chat.insert_node(part(0, 1), "b\nc");
    assert_eq!(
        (
            chat.step(part(0, 2)),
            chat.step(part(1, 0)),
            chat.step(part(1, 1)),
            chat.step(part(0, 4)),
        ),
        (
            Some(Step::Compress { message: 2 }),
            Some(Step::Merge {
                left: Arc::from("a"),
                right: Arc::from("b\nc"),
            }),
            None,
            None,
        )
    );
}

#[test]
fn zoom_opens_lines_and_messages() {
    let mut chat = chat_with(4);
    for (i, text) in ["a", "b", "c\nd", "e"].iter().enumerate() {
        chat.insert_node(part(0, i as u64), text);
    }
    chat.insert_node(part(1, 0), "ab");
    assert_eq!(
        chat.zoom(0, 4),
        Zoom::Lines("0+2|ab\n2+2|(not summarized yet: zoom it)".to_string())
    );
    assert_eq!(chat.zoom(2, 2), Zoom::Lines("2+1|c d\n3+1|e".to_string()));
    assert_eq!(chat.zoom(3, 1), Zoom::Message(3));
    // `n` a power of 2, `id % n == 0`, `id + n <= T`.
    assert_eq!(chat.zoom(1, 2), Zoom::NoLine);
    assert_eq!(chat.zoom(0, 3), Zoom::NoLine);
    assert_eq!(chat.zoom(4, 1), Zoom::NoLine);
    assert_eq!(chat.zoom(0, 8), Zoom::NoLine);
    assert_eq!(chat.zoom(u64::MAX - 1, 2), Zoom::NoLine);
}

/// A node's input is its message, labeled, or its two children joined by
/// a newline.
#[test]
fn a_nodes_input_is_its_message_or_its_children() {
    let merge = Step::Merge {
        left: Arc::from("a"),
        right: Arc::from("b\nc"),
    };
    assert_eq!(
        [
            Step::Compress { message: 3 }
                .input(|id| Ok((Kind::User, format!("hi {id}"))))
                .unwrap(),
            merge
                .input(|_| unreachable!("a merge reads no message"))
                .unwrap(),
        ],
        ["user: hi 3".to_string(), "a\nb\nc".to_string()]
    );
}

fn loaded(total: u64, nodes: Vec<NodeRecord>, merges: Vec<MergeRecord>) -> Loaded {
    Loaded {
        messages: (0..total).map(|_| meta(Kind::User)).collect(),
        nodes,
        merges,
        scopes: std::collections::HashMap::new(),
        problems: Vec::new(),
    }
}

fn node(l: u32, i: u64, text: &str) -> NodeRecord {
    NodeRecord {
        l,
        i,
        text: text.to_string(),
        size: text.len(),
    }
}

/// A chat from before the merge batches were logged imports its saved
/// view once: the view is the saved one, and the merges that build it are
/// handed to the owner to log.
#[test]
fn an_old_chat_imports_its_saved_view_as_merges() {
    let mut problems = Vec::new();
    let (chat, unlogged) = Chat::from_loaded(
        loaded(
            5,
            vec![
                node(0, 0, "a"),
                node(0, 1, "b"),
                node(1, 0, "ab"),
                node(3, 0, "foreign"),
            ],
            Vec::new(),
        ),
        Some(vec![part(2, 0), part(0, 4)]),
        &mut problems,
    );
    assert_eq!(
        (chat.view().parts().to_vec(), unlogged, problems.len()),
        (
            vec![part(2, 0), part(0, 4)],
            vec![MergeRecord::of(&[part(1, 0), part(1, 1), part(2, 0)])],
            1
        )
    );
}

/// The view is the fold of the messages and the logged merge batches:
/// the saved view (stale, missing, or broken) is only a cache, and a
/// merge whose halves are not in the view is skipped.
#[test]
fn the_view_folds_from_the_logged_merges() {
    let nodes = || vec![node(0, 0, "a"), node(0, 1, "b"), node(1, 0, "ab")];
    let merges = || {
        vec![
            MergeRecord::of(&[part(1, 0)]),
            MergeRecord::of(&[part(2, 1)]),
        ]
    };
    let mut problems = Vec::new();
    let views: Vec<(Vec<Part>, Vec<MergeRecord>)> = [
        None,
        Some(vec![part(0, 0), part(0, 1), part(0, 2)]),
        Some(vec![part(0, 0), part(0, 2)]),
    ]
    .into_iter()
    .map(|saved| {
        let (chat, unlogged) =
            Chat::from_loaded(loaded(3, nodes(), merges()), saved, &mut problems);
        (chat.view().parts().to_vec(), unlogged)
    })
    .collect();
    let folded = (vec![part(1, 0), part(0, 2)], Vec::new());
    assert_eq!(
        (views, problems.len()),
        (vec![folded.clone(), folded.clone(), folded], 3)
    );
}

/// A restart keeps the live view (§3.2, §7.3), shrinking included: a
/// batch that could not reach the floor goes on at the next message after
/// a restart as it would have without one. Before the batch lines carried
/// `open`, the reloaded view under its ceiling only appended, and the next
/// message's batch differed from the live one.
#[test]
fn a_restart_keeps_a_shrinking_view_shrinking() {
    let budgets = Budgets {
        ceiling: 2000,
        floor: 1000,
        compaction_ceiling: 100_000,
        compaction_floor: 50_000,
        jobs: 8,
    };
    let text = "x".repeat(500);
    let mut live = Chat {
        budgets,
        ..Chat::default()
    };
    let mut nodes = Vec::new();
    let mut records = Vec::new();
    let build = |chat: &mut Chat, nodes: &mut Vec<NodeRecord>, l: u32, i: u64| {
        chat.insert_node(part(l, i), &text);
        nodes.push(node(l, i, &text));
    };
    for id in 0..4 {
        live.push_message(meta(Kind::User));
        build(&mut live, &mut nodes, 0, id);
    }
    build(&mut live, &mut nodes, 1, 0);
    // Message 4 (a placeholder line) passes the ceiling; its batch merges
    // 0+2 and stays over the floor.
    let (_, batch) = live.push_message(meta(Kind::User));
    records.extend(batch.map(|batch| batch.record()));
    build(&mut live, &mut nodes, 1, 1);
    assert_eq!(
        records,
        vec![MergeRecord {
            merge: vec![(1, 0)],
            open: true,
            t: Some(5),
        }]
    );
    let mut problems = Vec::new();
    let (reloaded, unlogged) =
        Chat::from_loaded(loaded(5, nodes, records.clone()), None, &mut problems);
    let mut reloaded = Chat {
        budgets,
        ..reloaded
    };
    let live_next = live.push_message(meta(Kind::User)).1;
    let reloaded_next = reloaded.push_message(meta(Kind::User)).1;
    assert_eq!(
        (
            unlogged,
            problems,
            reloaded_next.clone(),
            reloaded.view().parts().to_vec()
        ),
        (
            Vec::new(),
            Vec::<String>::new(),
            live_next,
            live.view().parts().to_vec()
        )
    );
    assert!(reloaded_next.is_some_and(|batch| batch.merged == vec![part(1, 1)]));
    // A batch line from before `open` and `t` were logged still reads.
    assert_eq!(
        serde_json::from_str::<MergeRecord>(r#"{"merge":[[1,0]]}"#).unwrap(),
        MergeRecord::of(&[part(1, 0)])
    );
    assert_eq!(
        serde_json::to_string(&records[0]).unwrap(),
        r#"{"merge":[[1,0]],"open":true,"t":5}"#
    );
}
