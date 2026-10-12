//! The family mesh: every agent under one root session. A row's parent is
//! found through its durable parent edge ([`row_is_parent`]), the family
//! root by walking those edges up, and the caller's family is every row
//! that reaches the same root. Relationships keep the nuclear labels
//! (parent, sibling, child) and call everyone else in the tree a relative.
//! A root session additionally keeps the other root sessions as siblings
//! (roots are each other's family), never their subtrees.

use std::collections::HashSet;

use serde_json::json;

use super::{
    row_depth, row_is_parent, row_is_sibling, row_str, AgentFamilyRelationship, FamilyIdentity,
    Value,
};

/// One member of the caller's family: its index in the roster slice, its
/// relationship to the caller, and the `parent/child` path that names it
/// when its parent has a name.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct FamilyRow {
    pub index: usize,
    pub relationship: AgentFamilyRelationship,
    pub path: Option<String>,
}

/// The caller's family over `rows`: the family rows (never the caller's
/// own row), the index of the caller's own row when the roster carries it,
/// and the family root's live session id when the root is resident.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct Family {
    pub members: Vec<FamilyRow>,
    pub own_index: Option<usize>,
    pub root_active_session_id: Option<String>,
}

/// The live session id of one roster row (`activeSessionId`, the
/// supervisor rows' `id` fallback).
pub(crate) fn row_active_id(row: &Value) -> Option<&str> {
    row_str(row, "activeSessionId")
}

/// The address a send uses for one row: its live session id, else its
/// durable session id (the supervisor wakes a passivated agent by it).
pub(crate) fn row_target(row: &Value) -> Option<String> {
    row_active_id(row)
        .or_else(|| row_str(row, "sessionId"))
        .or_else(|| row_str(row, "id"))
        .map(str::to_string)
}

/// The display name of one row: its session name, else its address.
pub(crate) fn row_display_name(row: &Value) -> Option<String> {
    row_str(row, "sessionName")
        .map(str::to_string)
        .or_else(|| row_target(row))
}

/// The durable family identity a roster row describes (its own ids and
/// recorded parent edge).
fn row_identity(row: &Value) -> FamilyIdentity {
    FamilyIdentity::from_summary(Some(row), row_active_id(row).unwrap_or_default())
}

/// Whether `row` is the caller's own row.
fn is_own_row(row: &Value, identity: &FamilyIdentity) -> bool {
    row_active_id(row) == Some(identity.active_session_id.as_str())
        || identity
            .session_id
            .as_deref()
            .is_some_and(|id| row_str(row, "sessionId") == Some(id))
}

/// The caller's own row as the edge rules read it: its roster row (when
/// listed) with the caller's authoritative ids, session file, name, and
/// depth laid over — a roster row may lag a rename or omit the file.
fn own_view(row: Option<&Value>, identity: &FamilyIdentity) -> Value {
    let mut view = row
        .filter(|row| row.is_object())
        .cloned()
        .unwrap_or_else(|| json!({}));
    view["activeSessionId"] = json!(identity.active_session_id);
    view["rlmDepth"] = json!(identity.rlm_depth);
    for (key, value) in [
        ("sessionId", &identity.session_id),
        ("sessionFile", &identity.session_file),
        ("sessionName", &identity.session_name),
    ] {
        if let Some(value) = value {
            view[key] = json!(value);
        }
    }
    view
}

/// Classify `rows` into the caller's family. `forced_child` marks rows the
/// caller's children registry owns: they are children even before their
/// durable edges reach the roster.
pub(crate) fn family_of(
    rows: &[Value],
    identity: &FamilyIdentity,
    forced_child: impl Fn(&Value) -> bool,
) -> Family {
    let own_index = rows.iter().position(|row| is_own_row(row, identity));
    let own = own_view(own_index.map(|index| &rows[index]), identity);
    let row_at = |index: usize| {
        if Some(index) == own_index {
            &own
        } else {
            &rows[index]
        }
    };
    // Each row's parent row; the caller's parent comes from its own
    // (authoritative) identity, not its roster row.
    let parent_of: Vec<Option<usize>> = (0..rows.len())
        .map(|index| {
            if Some(index) == own_index {
                return find_parent(rows.len(), row_at, identity, index);
            }
            find_parent(rows.len(), row_at, &row_identity(&rows[index]), index)
        })
        .collect();
    let own_parent = match own_index {
        Some(index) => parent_of[index],
        None => find_parent(rows.len(), row_at, identity, usize::MAX),
    };
    // A row whose parent edge names the caller is a child even when the
    // caller's own row is missing from the roster.
    let is_child_of_caller = |index: usize| match own_index {
        Some(own_index) => parent_of[index] == Some(own_index),
        None => row_points_at(&rows[index], &own),
    };
    let own_root = match own_index {
        Some(index) => root_of(&parent_of, index),
        None => own_parent.map_or(Root::Caller, |parent| root_of(&parent_of, parent)),
    };
    let root_active_session_id = match own_root {
        Root::Row(index) => row_active_id(row_at(index)).map(str::to_string),
        Root::Caller => Some(identity.active_session_id.clone()),
    };
    let mut members = Vec::new();
    for (index, row) in rows.iter().enumerate() {
        if Some(index) == own_index {
            continue;
        }
        let forced = forced_child(row);
        let in_tree = is_child_of_caller(index)
            || match own_root {
                Root::Row(root) => root_of(&parent_of, index) == Root::Row(root),
                Root::Caller => reaches_caller(&parent_of, index, rows, &own),
            };
        let relationship = if forced || is_child_of_caller(index) {
            AgentFamilyRelationship::Child
        } else if !in_tree {
            // Outside the tree: a root's fellow roots, and a subagent's
            // siblings under a parent the roster does not list, share
            // the caller's (absent) parent edge; nothing else enters.
            if (identity.is_top_level() || own_parent.is_none()) && row_is_sibling(row, identity) {
                AgentFamilyRelationship::Sibling
            } else {
                continue;
            }
        } else if own_parent == Some(index) {
            AgentFamilyRelationship::Parent
        } else if own_parent.is_some() && parent_of[index] == own_parent {
            AgentFamilyRelationship::Sibling
        } else {
            AgentFamilyRelationship::Relative
        };
        let path = match parent_of[index] {
            Some(parent) => parent_path(row_at(parent), row),
            None if forced || is_child_of_caller(index) => parent_path(&own, row),
            None => None,
        };
        members.push(FamilyRow {
            index,
            relationship,
            path,
        });
    }
    Family {
        members,
        own_index,
        root_active_session_id,
    }
}

/// The `parent/child` path of `row` under `parent`, when both are named.
fn parent_path(parent: &Value, row: &Value) -> Option<String> {
    Some(format!(
        "{}/{}",
        row_str(parent, "sessionName")?,
        row_str(row, "sessionName")?
    ))
}

/// The first of `len` rows (other than `skip`) that is the parent
/// `identity` records.
fn find_parent<'a>(
    len: usize,
    row_at: impl Fn(usize) -> &'a Value,
    identity: &FamilyIdentity,
    skip: usize,
) -> Option<usize> {
    if identity.is_top_level() {
        return None;
    }
    (0..len).find(|index| *index != skip && row_is_parent(row_at(*index), identity))
}

/// Whether `row`'s parent edge names the caller (`own`, its own view).
fn row_points_at(row: &Value, own: &Value) -> bool {
    let row_identity = row_identity(row);
    !row_identity.is_top_level() && row_is_parent(own, &row_identity)
}

/// A family root: a roster row, or the caller itself when its own row is
/// missing and it has no parent row.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Root {
    Row(usize),
    Caller,
}

/// The topmost row reached from `index` through parent links (a cycle in
/// corrupt edges stops at the first repeated row).
fn root_of(parent_of: &[Option<usize>], index: usize) -> Root {
    let mut seen = HashSet::new();
    let mut current = index;
    while let Some(parent) = parent_of[current] {
        if !seen.insert(current) {
            break;
        }
        current = parent;
    }
    Root::Row(current)
}

/// Whether the parent chain from `index` reaches a row whose parent edge
/// names the caller (the caller's own row missing from the roster).
fn reaches_caller(parent_of: &[Option<usize>], index: usize, rows: &[Value], own: &Value) -> bool {
    let mut seen = HashSet::new();
    let mut current = index;
    loop {
        if row_points_at(&rows[current], own) {
            return true;
        }
        if !seen.insert(current) {
            return false;
        }
        match parent_of[current] {
            Some(parent) => current = parent,
            None => return false,
        }
    }
}

/// Whether `row` is a subagent (a subagent runtime, or below the root).
pub(crate) fn row_is_subagent(row: &Value) -> bool {
    row_str(row, "runtimeKind") == Some("subagent") || row_depth(row) > 0
}

/// The durable session ids of the running subagents in the family of the
/// session live as `active_session_id` (its own row included): the spawn
/// cap's family-wide view over the supervisor's `roster`-scope peers. The
/// session's identity is its own roster row.
pub(crate) fn running_family_subagents(rows: &[Value], active_session_id: &str) -> Vec<String> {
    let own = rows
        .iter()
        .find(|row| row_active_id(row) == Some(active_session_id));
    let identity = FamilyIdentity::from_summary(own, active_session_id);
    let family = family_of(rows, &identity, |_| false);
    family
        .members
        .iter()
        .map(|member| member.index)
        .chain(family.own_index)
        .filter_map(|index| {
            let row = &rows[index];
            (row_is_subagent(row) && row_str(row, "status") == Some("running"))
                .then(|| row_str(row, "sessionId").or_else(|| row_str(row, "id")))
                .flatten()
                .map(str::to_string)
        })
        .collect()
}
