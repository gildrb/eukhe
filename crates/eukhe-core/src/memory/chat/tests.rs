use super::*;
use crate::memory::store::MergeRecord;
use crate::memory::PLACEHOLDER;

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

fn line() -> String {
    "x".repeat(500)
}

/// Build node `part` and every ancestor whose sibling is built, each
/// `line()` long: the tree as an always-caught-up compactor grows it.
fn build_up(chat: &mut Chat, mut part: Part) {
    chat.insert_node(part, &line());
    while part.l < 62 {
        let sibling = Part {
            l: part.l,
            i: part.i ^ 1,
        };
        if chat.nodes.node_text(sibling).is_none() {
            return;
        }
        part = Part {
            l: part.l + 1,
            i: part.i / 2,
        };
        chat.insert_node(part, &line());
    }
}

/// The spec's merge order, written independently of [`View::fit`]: merge
/// the pair with the largest `(T - last) / 2^l` whose parent is built, the
/// oldest among equals, until the parts' lines fit `floor` bytes.
fn reference_batch(chat: &Chat, mut parts: Vec<Part>, total: u64, floor: usize) -> Vec<Part> {
    let size = |parts: &[Part]| -> usize {
        parts
            .iter()
            .map(|part| line_text(*part, &chat.nodes).len())
            .sum()
    };
    while size(&parts) > floor {
        let mut best: Option<(usize, u64, u32)> = None;
        for at in 0..parts.len().saturating_sub(1) {
            let (left, right) = (parts[at], parts[at + 1]);
            let parent = part(left.l + 1, left.i / 2);
            if left.l != right.l || left.i % 2 != 0 || chat.nodes.node_text(parent).is_none() {
                continue;
            }
            let age = total - (right.end() - 1);
            // age / 2^l > best_age / 2^best_l, cross-multiplied.
            let better = best.is_none_or(|(_, best_age, best_l)| {
                u128::from(age) << best_l > u128::from(best_age) << left.l
            });
            if better {
                best = Some((at, age, left.l));
            }
        }
        let Some((at, _, _)) = best else {
            break;
        };
        parts[at] = part(parts[at].l + 1, parts[at].i / 2);
        parts.remove(at + 1);
    }
    parts
}

/// Up to [`JOBS`] messages compress at once: a message's node starts once
/// fewer than [`JOBS`] lines before it are unbuilt.
#[test]
fn messages_compress_in_parallel_up_to_jobs_unbuilt_lines() {
    let mut chat = chat_with(10);
    let first: Vec<Part> = (0..JOBS as u64).map(|i| part(0, i)).collect();
    assert_eq!(chat.candidates(), first);
    for running in &first[..3] {
        chat.mark_busy(*running);
    }
    assert_eq!(
        chat.candidates(),
        (3..JOBS as u64).map(|i| part(0, i)).collect::<Vec<_>>()
    );
    chat.insert_node(part(0, 0), "user: a");
    chat.release(part(0, 1));
    chat.release(part(0, 2));
    assert_eq!(
        chat.candidates(),
        (1..=JOBS as u64).map(|i| part(0, i)).collect::<Vec<_>>()
    );
}

/// A merge starts once both its halves are built, even with unbuilt
/// lines before its end elsewhere.
#[test]
fn merges_start_once_both_halves_are_built() {
    let mut chat = chat_with(4);
    chat.insert_node(part(0, 0), "a");
    chat.insert_node(part(0, 1), "b");
    chat.insert_node(part(0, 3), "d");
    assert_eq!(chat.candidates(), vec![part(0, 2), part(1, 0)]);
    chat.insert_node(part(0, 2), "c");
    assert_eq!(chat.candidates(), vec![part(1, 0), part(1, 1)]);
}

/// At most [`JOBS`] nodes run at once.
#[test]
fn the_pump_starts_at_most_jobs_nodes() {
    let pairs = JOBS as u64 + 2;
    let mut chat = chat_with(2 * pairs);
    for i in 0..2 * pairs {
        chat.insert_node(part(0, i), "x");
    }
    let all: Vec<Part> = (0..JOBS as u64).map(|i| part(1, i)).collect();
    assert_eq!(chat.candidates(), all);
    for running in &all[..3] {
        chat.mark_busy(*running);
    }
    assert_eq!(chat.candidates(), all[3..]);
    chat.release(all[0]);
    assert_eq!(
        chat.candidates(),
        [all[0]]
            .into_iter()
            .chain(all[3..].iter().copied())
            .collect::<Vec<_>>()
    );
}

/// A compaction's view: the lines before a message (the message comes
/// whole in the task), or up to a merge's last message, in the agent's
/// `id+n|text` form, stopping at the first unbuilt line.
#[test]
fn the_compactor_sees_the_view_up_to_the_node() {
    let mut chat = chat_with(4);
    chat.insert_node(part(0, 0), "a");
    chat.insert_node(part(0, 1), "b\nc");
    chat.insert_node(part(0, 3), "d");
    assert_eq!(
        (
            chat.step(part(0, 2)),
            chat.context(part(0, 2)),
            chat.step(part(1, 0)),
            chat.context(part(1, 0)),
            chat.context(part(0, 4)),
        ),
        (
            Some(Step::Compress { message: 2 }),
            "<chat>\n0+1|a\n1+1|b c\n</chat>".to_string(),
            Some(Step::Merge {
                left: Arc::from("a"),
                right: Arc::from("b\nc"),
            }),
            "<chat>\n0+1|a\n1+1|b c\n</chat>".to_string(),
            "<chat>\n0+1|a\n1+1|b c\n</chat>".to_string(),
        )
    );
}

/// A batch as (merged pairs, bytes before, bytes after).
fn batch_shape(batch: Option<Batch>) -> Option<(usize, usize, usize)> {
    batch.map(|batch| (batch.merged.len(), batch.before, batch.after))
}

/// §3.2's sawtooth: each message only appends its line until the view
/// passes 128,000 bytes; then ONE batch merges the most due built pairs,
/// oldest first among equals, down to at most 64,000 bytes.
#[test]
fn the_view_grows_to_the_ceiling_then_one_batch_merges_it_to_the_floor() {
    let mut chat = Chat::default();
    let crossing = (VIEW_CEILING / line().len()) as u64 + 1;
    let mut batches = Vec::new();
    let mut expected = Vec::new();
    for id in 0..crossing {
        let mut appended = chat.view.parts().to_vec();
        let (_, batch) = chat.push_message(meta(Kind::User));
        if id == crossing - 1 {
            appended.push(part(0, id));
            expected = reference_batch(&chat, appended, crossing, VIEW_FLOOR);
        }
        batches.push(batch_shape(batch));
        build_up(&mut chat, part(0, id));
    }
    // The crossing message's line is still a placeholder when it lands.
    let mut want = vec![None; crossing as usize - 1];
    want.push(Some((
        129,
        128_000 + PLACEHOLDER.len(),
        63_500 + PLACEHOLDER.len(),
    )));
    assert_eq!(
        (batches, chat.view.parts().to_vec(), chat.shrinking),
        (want, expected, false)
    );
    // The next message only appends again.
    let (_, batch) = chat.push_message(meta(Kind::User));
    assert_eq!(
        (batch_shape(batch), chat.view.size()),
        (None, 64_000 + PLACEHOLDER.len())
    );
}

/// A batch merges only pairs whose parent is built; when that cannot
/// reach the floor, every later message merges what it can until it does.
#[test]
fn a_batch_merges_only_built_parents_and_resumes_at_each_message() {
    let mut chat = Chat::default();
    let crossing = (VIEW_CEILING / line().len()) as u64 + 1;
    let mut last = None;
    for id in 0..crossing {
        // When the batch comes, only `(1, 0..40)` are built above level 0.
        if id == crossing - 1 {
            for i in 0..40 {
                chat.insert_node(part(1, i), &line());
            }
        }
        let (_, batch) = chat.push_message(meta(Kind::User));
        chat.insert_node(part(0, id), &line());
        last = batch_shape(batch);
    }
    let first_batch = (last, chat.shrinking);
    let stalled = batch_shape(chat.push_message(meta(Kind::User)).1);
    chat.insert_node(part(0, crossing), &line());
    for i in 40..60 {
        chat.insert_node(part(1, i), &line());
    }
    let resumed = batch_shape(chat.push_message(meta(Kind::User)).1);
    let mut parts: Vec<Part> = (0..60).map(|i| part(1, i)).collect();
    parts.extend((120..=crossing + 1).map(|i| part(0, i)));
    assert_eq!(
        (first_batch, stalled, resumed, chat.view.parts().to_vec()),
        (
            (
                Some((40, 128_000 + PLACEHOLDER.len(), 108_000 + PLACEHOLDER.len())),
                true
            ),
            None,
            Some((20, 109_000 + PLACEHOLDER.len(), 99_000 + PLACEHOLDER.len())),
            parts
        )
    );
}

/// Every part of `fine` lies inside one part of `coarse`, and both tile
/// the same messages.
fn coarsens(coarse: &[Part], fine: &[Part]) -> bool {
    let mut at = 0;
    for old in fine {
        while at < coarse.len() && coarse[at].end() < old.end() {
            at += 1;
        }
        let Some(new) = coarse.get(at) else {
            return false;
        };
        if new.start() > old.start() || old.end() > new.end() {
            return false;
        }
    }
    coarse.last().map(|part| part.end()) == fine.last().map(|part| part.end())
}

/// §4's compaction view: merged to 16,000 bytes once, then the chat's new
/// lines appended (its start unchanged), merged again past 32,000 bytes or
/// when the chat's view merges; it is always the chat's view, coarser.
#[test]
fn the_compaction_view_keeps_its_own_sawtooth() {
    let mut chat = Chat::default();
    let mut violations = Vec::new();
    let (mut own_merges, mut chat_merges) = (0, 0);
    for id in 0..1_200u64 {
        let old = chat.compaction.parts().to_vec();
        let (_, batch) = chat.push_message(meta(Kind::User));
        let new = chat.compaction.parts().to_vec();
        let size = chat.compaction.size();
        if !coarsens(&new, chat.view.parts()) {
            violations.push(format!("at {id}: not a coarser chat view"));
        }
        if batch.is_some() {
            chat_merges += 1;
            if size > COMPACTION_FLOOR {
                violations.push(format!("at {id}: rebased only to {size} bytes"));
            }
        } else if new.starts_with(&old) {
            if new.len() != old.len() + 1 {
                violations.push(format!("at {id}: appended {} lines", new.len() - old.len()));
            }
        } else {
            own_merges += 1;
            if size > COMPACTION_FLOOR {
                violations.push(format!("at {id}: merged only to {size} bytes"));
            }
        }
        build_up(&mut chat, part(0, id));
        let size = chat.compaction.size();
        if size > COMPACTION_CEILING {
            violations.push(format!("at {id}: {size} bytes"));
        }
    }
    assert_eq!(
        (violations, own_merges > 0, chat_merges > 0),
        (Vec::<String>::new(), true, true)
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

/// A source that fits in [`NODE`] bytes is its own node: a short
/// message verbatim at level 0, two short children joined by a newline
/// above.
#[test]
fn free_nodes_need_no_model() {
    let compress = Step::Compress { message: 0 };
    let merge = |left: &str, right: &str| Step::Merge {
        left: Arc::from(left),
        right: Arc::from(right),
    };
    let half = "y".repeat(NODE / 2);
    assert_eq!(
        [
            free_text(Some((Kind::User, "hi")), &compress),
            free_text(Some((Kind::Echo, &"x".repeat(NODE - 6))), &compress),
            free_text(Some((Kind::Echo, &"x".repeat(NODE - 5))), &compress),
            free_text(None, &merge("a", "b")),
            free_text(None, &merge(&half, &half[1..])),
            free_text(None, &merge(&half, &half)),
        ],
        [
            Some("user: hi".to_string()),
            Some(format!("echo: {}", "x".repeat(NODE - 6))),
            None,
            Some("a\nb".to_string()),
            Some(format!("{half}\n{}", &half[1..])),
            None,
        ]
    );
}

fn loaded(total: u64, nodes: Vec<NodeRecord>, merges: &[&[Part]]) -> Loaded {
    Loaded {
        messages: (0..total).map(|_| meta(Kind::User)).collect(),
        nodes,
        merges: merges.iter().map(|batch| MergeRecord::of(batch)).collect(),
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
            &[],
        ),
        Some(vec![part(2, 0), part(0, 4)]),
        &mut problems,
    );
    assert_eq!(
        (chat.view().parts().to_vec(), unlogged, problems.len()),
        (
            vec![part(2, 0), part(0, 4)],
            vec![part(1, 0), part(1, 1), part(2, 0)],
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
    let merges: &[&[Part]] = &[&[part(1, 0)], &[part(2, 1)]];
    let mut problems = Vec::new();
    let views: Vec<(Vec<Part>, Vec<Part>)> = [
        None,
        Some(vec![part(0, 0), part(0, 1), part(0, 2)]),
        Some(vec![part(0, 0), part(0, 2)]),
    ]
    .into_iter()
    .map(|saved| {
        let (chat, unlogged) = Chat::from_loaded(loaded(3, nodes(), merges), saved, &mut problems);
        (chat.view().parts().to_vec(), unlogged)
    })
    .collect();
    let folded = (vec![part(1, 0), part(0, 2)], Vec::new());
    assert_eq!(
        (views, problems.len()),
        (vec![folded.clone(), folded.clone(), folded], 3)
    );
}
