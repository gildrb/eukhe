//! The wire between a workflow and the session's agent tree: the
//! session's tree facts (`rlm.tree_facts`) as a batch's room, the key a
//! batch's nodes are lent under (`rlm.tree_lend`, `rlm.tree_return`), a
//! writing leaf's spawn kwargs (`node`, `budget`), and what a settled
//! writer wrote (`scopedHandback`, `patch` of `rlm.answer`).

use eukhe_bend::rules::agent_tree::{Lim, Patch};
use serde_json::{json, Map, Value};

use super::batch::{Batch, LeafPlace, Limit, Room};

/// The session's write scope and the room a new batch gets in it.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct Facts {
    pub(crate) write_scope: Vec<String>,
    pub(crate) room: Room,
}

/// Why a facts reply does not read.
#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
#[error("rlm.tree_facts: {0}")]
pub(crate) struct FactsError(&'static str);

/// The facts of an `rlm.tree_facts` reply. The batch's root sits one
/// level below the session; its limit is the session's free less the
/// tenth the session keeps for itself.
///
/// # Errors
///
/// A missing or mistyped field.
pub(crate) fn facts(reply: &Value) -> Result<Facts, FactsError> {
    let write_scope = reply
        .get("writeScope")
        .and_then(Value::as_array)
        .ok_or(FactsError("writeScope must be a list"))?
        .iter()
        .map(|path| path.as_str().map(str::to_owned))
        .collect::<Option<Vec<_>>>()
        .ok_or(FactsError("writeScope must hold paths"))?;
    let number = |key: &str| reply.get(key).and_then(Value::as_u64);
    let depth = number("depth").ok_or(FactsError("depth must be a whole number"))?;
    let allowance = number("remaining").ok_or(FactsError("remaining must be a whole number"))?;
    let limit = match reply.get("free") {
        None | Some(Value::Null) => None,
        Some(free) => {
            let (key, amount) = free
                .get("budget")
                .and_then(Value::as_object)
                .and_then(|budget| budget.iter().next())
                .and_then(|(key, amount)| Some((key.clone(), amount.as_u64()?)))
                .ok_or(FactsError("free must name one budget amount"))?;
            Some(Limit {
                key,
                amount: amount - amount / 10,
            })
        }
    };
    let deadline = match reply.get("deadlineMs") {
        None | Some(Value::Null) => None,
        Some(deadline) => Some(
            deadline
                .as_u64()
                .ok_or(FactsError("deadlineMs must be a whole number"))?,
        ),
    };
    Ok(Facts {
        write_scope,
        room: Room {
            depth: depth + 1,
            allowance,
            limit,
            deadline,
        },
    })
}

/// The key a batch's nodes are lent under.
pub(crate) fn lend_key(run_id: &str, batch: u32) -> String {
    format!("{run_id}:{batch}")
}

/// The nodes a batch of `agents` writing agents holds: its leaves and
/// its integrators.
pub(crate) fn nodes(agents: usize) -> u64 {
    u64::try_from(agents.saturating_mul(2).saturating_sub(1)).unwrap_or(u64::MAX)
}

/// The `node` and `budget` kwargs of a writing leaf's spawn. A leaf holds
/// one node: it works alone.
pub(crate) fn leaf_kwargs(batch: &Batch, place: &LeafPlace) -> Map<String, Value> {
    let role = match place.path.chars().last() {
        None => "root",
        Some('L') => "left",
        Some(_) => "right",
    };
    let mut node = json!({
        "role": role,
        "path": place.path,
        "units": batch.units,
        "scope": place.mask,
        "allowance": 1,
    });
    if let Lim::Value(deadline) = place.deadline {
        node["deadline_ms"] = json!(deadline);
    }
    let mut kwargs = Map::new();
    kwargs.insert("node".to_owned(), node);
    if let (Some(limit), Lim::Value(amount)) = (&batch.room.limit, place.limit) {
        kwargs.insert("budget".to_owned(), json!({ limit.key.as_str(): amount }));
    }
    kwargs
}

/// What a writing agent's children wrote: the patch over the batch's
/// units, and the paths that came back as conflicts (written outside the
/// agent's scope, or changed by both sides).
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub(crate) struct Written {
    pub(crate) patch: Patch,
    pub(crate) conflicts: Vec<String>,
}

fn paths(value: Option<&Value>) -> Vec<String> {
    value
        .and_then(Value::as_array)
        .map(|paths| {
            paths
                .iter()
                .filter_map(Value::as_str)
                .map(str::to_owned)
                .collect()
        })
        .unwrap_or_default()
}

fn patch(value: Option<&Value>) -> Patch {
    value
        .and_then(|patch| serde_json::from_value(patch.clone()).ok())
        .unwrap_or_default()
}

/// What the settled child of an `rlm.answer` state wrote: its scoped
/// hand-back when it finished, its unapplied patch when it failed.
pub(crate) fn written(state: &Value) -> Written {
    match state
        .get("scopedHandback")
        .filter(|handback| !handback.is_null())
    {
        Some(handback) => Written {
            patch: patch(handback.get("patch")),
            conflicts: paths(handback.get("outside"))
                .into_iter()
                .chain(paths(handback.get("conflicts")))
                .collect(),
        },
        None => Written {
            patch: patch(state.get("patch")),
            conflicts: Vec::new(),
        },
    }
}

impl Written {
    /// This and a later child's writes of the same agent: per unit the
    /// later version where it wrote one; the conflicts of both.
    pub(crate) fn then(self, later: Written) -> Written {
        let units = self.patch.len().max(later.patch.len());
        let patch = (0..units)
            .map(|unit| {
                later
                    .patch
                    .get(unit)
                    .copied()
                    .flatten()
                    .or(self.patch.get(unit).copied().flatten())
            })
            .collect();
        let mut conflicts = self.conflicts;
        for path in later.conflicts {
            if !conflicts.contains(&path) {
                conflicts.push(path);
            }
        }
        Written { patch, conflicts }
    }

    /// The batch end of this agent: its patch over `units` units.
    pub(crate) fn patch_over(&self, units: usize) -> Patch {
        match self.patch.len() {
            0 => vec![None; units],
            _ => self.patch.clone(),
        }
    }
}
