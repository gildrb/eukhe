//! A split child's work list: the items its parent names (`rlm.split`
//! `items`), the child's account of each (`rlm.items`, kept in the child's
//! own `eukhe.rlm.items` document and read back with its run's outcome),
//! and the hand-back the parent's watch reads from the two through the
//! compiled core (`eukhe_bend::rules::work_list`): finished only when every
//! item is accounted done, else stopped with the items left.

use std::collections::BTreeMap;

use anyhow::{anyhow, bail};
use eukhe_bend::rules::work_list::{outcome, Outcome};
use eukhe_chord::context::Context;
use eukhe_chord::json::{from_json, to_json};
use eukhe_durable::documents::{ConversationDoc, DocDefinition};
use eukhe_durable::session::{SessionResult, Tx};
use eukhe_durable::types::{ConversationId, DocumentReader, LatestFork};
use serde::{Deserialize, Serialize};
use serde_json::Value;

use crate::durable::goals::read_doc;

/// How a child accounts for one item.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(
    tag = "kind",
    rename_all = "camelCase",
    rename_all_fields = "camelCase"
)]
pub enum ItemMark {
    Done,
    /// Not done, and why.
    Left {
        reason: String,
    },
}

/// A child's account of its items, by item id; a later account of an item
/// replaces the earlier one.
#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ItemAccount {
    #[serde(default)]
    pub items: BTreeMap<String, ItemMark>,
}

pub(crate) static ITEMS_DOC: ConversationDoc<ItemAccount> = match ConversationDoc::define(
    DocDefinition {
        kind: "eukhe.rlm.items",
        version: 1,
        initial: ItemAccount::default,
        migrate: None,
        checkpoint_when: None,
    },
    LatestFork::Initial,
) {
    Ok(token) => token,
    Err(_) => panic!("eukhe.rlm.items has a valid version"),
};

/// The account `conversation_id` keeps of its items; `None` when it gave
/// none.
///
/// # Errors
///
/// Read failures, or a document that does not decode.
pub async fn items_account(
    reader: &(impl DocumentReader + ?Sized),
    conversation_id: ConversationId,
    cx: &Context,
) -> SessionResult<Option<ItemAccount>> {
    read_doc(reader, &ITEMS_DOC, conversation_id, cx).await
}

/// Merge `marks` into the account of `conversation_id` inside a commit;
/// answers how many items the account holds after it.
pub(crate) async fn tx_account(
    tx: &Tx,
    conversation_id: ConversationId,
    marks: Vec<(String, ItemMark)>,
) -> SessionResult<usize> {
    let draft = tx.doc(&ITEMS_DOC, conversation_id).await?;
    let mut account: ItemAccount = from_json(&draft.value()?)?;
    account.items.extend(marks);
    draft.set("items", to_json(&account.items)?)?;
    Ok(account.items.len())
}

/// The marks of an `rlm.items` request: `done`, a list of item ids, and
/// `left`, each id with why; either may be absent. An empty id or reason,
/// or an id both done and left, is refused.
///
/// # Errors
///
/// A malformed `done` or `left`, an empty id or reason, an id in both.
pub(crate) fn marks(data: &Value) -> anyhow::Result<Vec<(String, ItemMark)>> {
    let id = |id: &str| {
        Some(id.trim())
            .filter(|id| !id.is_empty())
            .map(str::to_owned)
            .ok_or_else(|| anyhow!("rlm.items ids must be non-empty strings"))
    };
    let done = match data.get("done") {
        None | Some(Value::Null) => Vec::new(),
        Some(Value::Array(ids)) => ids
            .iter()
            .map(|item| {
                item.as_str()
                    .ok_or_else(|| anyhow!("rlm.items done must be a list of item ids"))
                    .and_then(id)
                    .map(|id| (id, ItemMark::Done))
            })
            .collect::<anyhow::Result<Vec<_>>>()?,
        Some(_) => bail!("rlm.items done must be a list of item ids"),
    };
    let left = match data.get("left") {
        None | Some(Value::Null) => Vec::new(),
        Some(Value::Object(reasons)) => reasons
            .iter()
            .map(|(item, reason)| {
                let reason = reason
                    .as_str()
                    .map(str::trim)
                    .filter(|reason| !reason.is_empty())
                    .ok_or_else(|| anyhow!("rlm.items left needs a reason for {item}"))?;
                Ok((
                    id(item)?,
                    ItemMark::Left {
                        reason: reason.to_owned(),
                    },
                ))
            })
            .collect::<anyhow::Result<Vec<_>>>()?,
        Some(_) => bail!("rlm.items left must map item ids to reasons"),
    };
    if let Some((both, _)) = left
        .iter()
        .find(|(item, _)| done.iter().any(|(id, _)| id == item))
    {
        bail!("rlm.items names {both} both done and left");
    }
    Ok(done.into_iter().chain(left).collect())
}

/// Why an item is left.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(
    tag = "kind",
    rename_all = "camelCase",
    rename_all_fields = "camelCase"
)]
pub(crate) enum LeftWhy {
    /// The child left it, with this reason.
    Left { reason: String },
    /// The child never accounted for it.
    Unaccounted,
}

/// One item a child handed back not done.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub(crate) struct LeftItem {
    pub(crate) id: String,
    pub(crate) why: LeftWhy,
}

/// A child that handed back with items left: how many its parent named,
/// and each one left, in its parent's order.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub(crate) struct Stopped {
    pub(crate) items: usize,
    pub(crate) left: Vec<LeftItem>,
}

/// The hand-back of a child's work list.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum HandBack {
    /// Every item is done (also: no items).
    Finished,
    Stopped(Stopped),
}

impl HandBack {
    /// The hand-back of the `items` its parent named, by the child's
    /// `account` (`None`: it gave none, so no item is done).
    pub(crate) fn of(items: &[String], account: Option<&ItemAccount>) -> Self {
        let mark = |id: &String| account.and_then(|account| account.items.get(id));
        let done: Vec<bool> = items
            .iter()
            .map(|id| matches!(mark(id), Some(ItemMark::Done)))
            .collect();
        match outcome(&done) {
            Outcome::Finished => Self::Finished,
            Outcome::Stopped { left } => Self::Stopped(Stopped {
                items: items.len(),
                left: left
                    .into_iter()
                    .filter_map(|at| items.get(at))
                    .map(|id| LeftItem {
                        id: id.clone(),
                        why: match mark(id) {
                            Some(ItemMark::Left { reason }) => LeftWhy::Left {
                                reason: reason.clone(),
                            },
                            Some(ItemMark::Done) | None => LeftWhy::Unaccounted,
                        },
                    })
                    .collect(),
            }),
        }
    }
}

impl Stopped {
    /// `stopped: <left> of <items> items left: <id> (<why>), ...`: the
    /// one-line form of the roster and `rlm.collect`.
    pub(crate) fn summary(&self) -> String {
        let left: Vec<String> = self.left.iter().map(LeftItem::line).collect();
        format!(
            "stopped: {} of {} items left: {}",
            self.left.len(),
            self.items,
            left.join(", ")
        )
    }

    /// The notice's body: the summary's count, then one item per line.
    pub(crate) fn text(&self) -> String {
        let lines: Vec<String> = self
            .left
            .iter()
            .map(|item| format!("- {}", item.line()))
            .collect();
        format!(
            "Stopped: {} of {} items left:\n{}",
            self.left.len(),
            self.items,
            lines.join("\n")
        )
    }
}

impl LeftItem {
    fn line(&self) -> String {
        match &self.why {
            LeftWhy::Left { reason } => format!("{} (left: {reason})", self.id),
            LeftWhy::Unaccounted => format!("{} (no account)", self.id),
        }
    }
}

/// The task text a child given `items` receives: `prompt`, then its items
/// and how it accounts for them.
pub(crate) fn task_text(prompt: &str, items: &[String]) -> String {
    if items.is_empty() {
        return prompt.to_owned();
    }
    format!(
        "{prompt}\n\nItems: {}.\nAccount for each before your hand-back: `await rlm.items(done=[...], left={{\"<id>\": \"<why>\"}})`; call it again as items change (the latest account of an item counts). An item not accounted done reaches your parent as left, and your hand-back as stopped.",
        items.join(", ")
    )
}

#[cfg(test)]
mod tests {
    use super::*;

    fn ids(items: &[&str]) -> Vec<String> {
        items.iter().map(|id| (*id).to_owned()).collect()
    }

    /// A child that did 4 of 11 items, left 2 with a reason and never
    /// accounted for 5, hands back stopped with all 7, in its parent's
    /// order; its account of an item it was not given changes nothing.
    #[test]
    fn open_items_hand_back_stopped_in_order() {
        let items = ids(&[
            "S2", "M1", "M2", "U1", "U3", "U4", "U6", "A3", "A4", "A5", "A10",
        ]);
        let mut account = ItemAccount::default();
        for id in ["U3", "U6", "M1", "A10", "Z9"] {
            account.items.insert(id.to_owned(), ItemMark::Done);
        }
        for id in ["S2", "U1"] {
            account.items.insert(
                id.to_owned(),
                ItemMark::Left {
                    reason: "too risky".to_owned(),
                },
            );
        }
        let left = |id: &str, why: LeftWhy| LeftItem {
            id: id.to_owned(),
            why,
        };
        let risky = || LeftWhy::Left {
            reason: "too risky".to_owned(),
        };
        let stopped = Stopped {
            items: 11,
            left: vec![
                left("S2", risky()),
                left("M2", LeftWhy::Unaccounted),
                left("U1", risky()),
                left("U4", LeftWhy::Unaccounted),
                left("A3", LeftWhy::Unaccounted),
                left("A4", LeftWhy::Unaccounted),
                left("A5", LeftWhy::Unaccounted),
            ],
        };
        assert_eq!(
            HandBack::of(&items, Some(&account)),
            HandBack::Stopped(stopped.clone())
        );
        assert_eq!(
            stopped.summary(),
            "stopped: 7 of 11 items left: S2 (left: too risky), M2 (no account), U1 (left: too risky), U4 (no account), A3 (no account), A4 (no account), A5 (no account)"
        );
    }

    /// No account leaves every item; a full account of done items, and no
    /// items at all, finish.
    #[test]
    fn only_a_full_account_finishes() {
        let items = ids(&["a", "b"]);
        let done = ItemAccount {
            items: items
                .iter()
                .map(|id| (id.clone(), ItemMark::Done))
                .collect(),
        };
        assert_eq!(
            [
                HandBack::of(&items, None),
                HandBack::of(&items, Some(&done)),
                HandBack::of(&[], None),
            ],
            [
                HandBack::Stopped(Stopped {
                    items: 2,
                    left: vec![
                        LeftItem {
                            id: "a".to_owned(),
                            why: LeftWhy::Unaccounted,
                        },
                        LeftItem {
                            id: "b".to_owned(),
                            why: LeftWhy::Unaccounted,
                        },
                    ],
                }),
                HandBack::Finished,
                HandBack::Finished,
            ]
        );
    }
}
