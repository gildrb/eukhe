//! The memory tree as a reader browses it (the `/memory` tree and the
//! dashboard): one level at a time -- the view's lines, the two lines a
//! line opens into, or the one message under a one-message line -- each
//! line with its time span, the kinds of its messages and its summary.
//! Display only: it reads the owner's state and changes nothing.

use std::collections::BTreeMap;

use eukhe_types::daemon::{
    MemoryKindCount, MemoryTreeLevel, MemoryTreeMessage, MemoryTreeNode, MemoryZoom,
};

use super::chat::Chat;
use super::store::Store;
use super::view::{NodeTexts, Part};

/// The tree level `node` opens (`None`: the view's lines).
///
/// # Errors
///
/// Returns an error when a message under a one-message line cannot be
/// read back.
pub(crate) fn level(
    chat: &Chat,
    store: &Store,
    node: Option<MemoryZoom>,
) -> anyhow::Result<MemoryTreeLevel> {
    let Some(MemoryZoom { id, count }) = node else {
        return Ok(MemoryTreeLevel::Lines {
            nodes: chat
                .view()
                .parts()
                .iter()
                .map(|part| tree_node(chat, *part))
                .collect(),
        });
    };
    // The rule `zoom(id, n)` resolves lines by.
    let valid = count.is_power_of_two()
        && id.is_multiple_of(count)
        && id.checked_add(count).is_some_and(|end| end <= chat.total());
    if !valid {
        return Ok(MemoryTreeLevel::NoLine);
    }
    if count == 1 {
        let meta = chat
            .message(id)
            .ok_or_else(|| anyhow::anyhow!("message {id} is not indexed"))?;
        let record = store.read_message(meta)?;
        return Ok(MemoryTreeLevel::Message {
            message: MemoryTreeMessage {
                id,
                kind: record.kind.as_str().to_string(),
                date: meta.date.clone(),
                text: record.text,
            },
        });
    }
    let l = count.trailing_zeros() - 1;
    let i = id / count * 2;
    Ok(MemoryTreeLevel::Lines {
        nodes: [Part { l, i }, Part { l, i: i + 1 }]
            .into_iter()
            .map(|part| tree_node(chat, part))
            .collect(),
    })
}

/// One line of the tree: its span's dates, its kinds (most frequent
/// first, ties by name) and its summary when built.
fn tree_node(chat: &Chat, part: Part) -> MemoryTreeNode {
    let end = part.end().min(chat.total());
    let date = |id: u64| chat.message(id).map(|meta| meta.date.clone());
    let mut kinds: BTreeMap<&'static str, u64> = BTreeMap::new();
    for id in part.start()..end {
        if let Some(meta) = chat.message(id) {
            *kinds.entry(meta.kind.as_str()).or_default() += 1;
        }
    }
    let mut kinds: Vec<MemoryKindCount> = kinds
        .into_iter()
        .map(|(kind, count)| MemoryKindCount {
            kind: kind.to_string(),
            count,
        })
        .collect();
    // Stable: equal counts keep the name order.
    kinds.sort_by_key(|kind| std::cmp::Reverse(kind.count));
    MemoryTreeNode {
        id: part.start(),
        count: part.count(),
        first_date: date(part.start()).unwrap_or_default(),
        last_date: date(end.saturating_sub(1)).unwrap_or_default(),
        kinds,
        summary: chat.nodes().node_text(part).map(str::to_string),
    }
}

#[cfg(test)]
mod tests {
    use eukhe_types::daemon::{
        MemoryKindCount, MemoryTreeLevel, MemoryTreeMessage, MemoryTreeNode, MemoryZoom,
    };

    use crate::memory::compactor::tests::Scripted;
    use crate::memory::service::ImportItem;
    use crate::memory::{Kind, Memory};

    fn kinds(pairs: &[(&str, u64)]) -> Vec<MemoryKindCount> {
        pairs
            .iter()
            .map(|(kind, count)| MemoryKindCount {
                kind: (*kind).to_string(),
                count: *count,
            })
            .collect()
    }

    /// The view level lists every view line dated and labelled; a line
    /// opens into its two halves, a one-message line into the message,
    /// and a bad line answers `NoLine`.
    #[tokio::test]
    async fn levels_open_down_to_the_message() {
        let dir = tempfile::tempdir().unwrap();
        let memory = Memory::open(dir.path(), Scripted::with(Vec::new()))
            .await
            .unwrap();
        let item = |kind: Kind, text: &str, date: &str| ImportItem {
            kind,
            text: text.to_string(),
            date: date.to_string(),
        };
        memory
            .import(vec![
                item(Kind::User, "hi", "2026-10-01T09:00:00.000+02:00"),
                item(Kind::Talk, "hello", "2026-10-01T09:00:05.000+02:00"),
                item(Kind::User, "list files", "2026-10-02T10:00:00.000+02:00"),
            ])
            .await
            .unwrap();
        // Short messages are their own lines: settled once built.
        memory.settled_render().await.unwrap();

        let node = |id: u64, text: &str, kind: &str, date: &str| MemoryTreeNode {
            id,
            count: 1,
            first_date: date.to_string(),
            last_date: date.to_string(),
            kinds: kinds(&[(kind, 1)]),
            summary: Some(text.to_string()),
        };
        assert_eq!(
            memory.tree(None).await.unwrap(),
            MemoryTreeLevel::Lines {
                nodes: vec![
                    node(0, "user: hi", "user", "2026-10-01T09:00:00.000+02:00"),
                    node(1, "talk: hello", "talk", "2026-10-01T09:00:05.000+02:00"),
                    node(
                        2,
                        "user: list files",
                        "user",
                        "2026-10-02T10:00:00.000+02:00"
                    ),
                ]
            }
        );
        assert_eq!(
            memory
                .tree(Some(MemoryZoom { id: 0, count: 2 }))
                .await
                .unwrap(),
            MemoryTreeLevel::Lines {
                nodes: vec![
                    node(0, "user: hi", "user", "2026-10-01T09:00:00.000+02:00"),
                    node(1, "talk: hello", "talk", "2026-10-01T09:00:05.000+02:00"),
                ]
            }
        );
        assert_eq!(
            memory
                .tree(Some(MemoryZoom { id: 2, count: 1 }))
                .await
                .unwrap(),
            MemoryTreeLevel::Message {
                message: MemoryTreeMessage {
                    id: 2,
                    kind: "user".to_string(),
                    date: "2026-10-02T10:00:00.000+02:00".to_string(),
                    text: "list files".to_string(),
                }
            }
        );
        for bad in [(1, 2), (0, 3), (2, 2), (4, 1)] {
            assert_eq!(
                memory
                    .tree(Some(MemoryZoom {
                        id: bad.0,
                        count: bad.1
                    }))
                    .await
                    .unwrap(),
                MemoryTreeLevel::NoLine,
                "{bad:?}"
            );
        }
    }

    /// A wide line counts its kinds, most frequent first (ties by name),
    /// spans the dates of its first and last message, and carries its
    /// (here free) merged summary.
    #[tokio::test]
    async fn wide_lines_count_kinds_and_span_dates() {
        let dir = tempfile::tempdir().unwrap();
        let memory = Memory::open(dir.path(), Scripted::with(Vec::new()))
            .await
            .unwrap();
        let messages = [
            (Kind::User, "a"),
            (Kind::Tool, "t1"),
            (Kind::Echo, "e1"),
            (Kind::Tool, "t2"),
            (Kind::Talk, "b"),
            (Kind::User, "c"),
            (Kind::User, "d"),
            (Kind::Work, "[W] done"),
        ];
        memory
            .import(
                messages
                    .iter()
                    .enumerate()
                    .map(|(at, (kind, text))| ImportItem {
                        kind: *kind,
                        text: (*text).to_string(),
                        date: format!("2026-10-0{}T09:00:00.000+02:00", at + 1),
                    })
                    .collect(),
            )
            .await
            .unwrap();
        memory.settled_render().await.unwrap();
        assert_eq!(
            memory
                .tree(Some(MemoryZoom { id: 0, count: 8 }))
                .await
                .unwrap(),
            MemoryTreeLevel::Lines {
                nodes: vec![
                    MemoryTreeNode {
                        id: 0,
                        count: 4,
                        first_date: "2026-10-01T09:00:00.000+02:00".to_string(),
                        last_date: "2026-10-04T09:00:00.000+02:00".to_string(),
                        kinds: kinds(&[("tool", 2), ("echo", 1), ("user", 1)]),
                        summary: Some("user: a\ntool: t1\necho: e1\ntool: t2".to_string()),
                    },
                    MemoryTreeNode {
                        id: 4,
                        count: 4,
                        first_date: "2026-10-05T09:00:00.000+02:00".to_string(),
                        last_date: "2026-10-08T09:00:00.000+02:00".to_string(),
                        kinds: kinds(&[("user", 2), ("talk", 1), ("work", 1)]),
                        summary: Some("talk: b\nuser: c\nuser: d\nwork: [W] done".to_string()),
                    },
                ]
            }
        );
    }
}
