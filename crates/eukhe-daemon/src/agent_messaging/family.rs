//! The caller's place in its tree. A row's parent is found through its
//! durable parent edge ([`row_is_parent`]); the caller's members are its
//! parent and its own children, the only agents it messages or observes.

use serde_json::json;

use super::{row_is_parent, row_str, AgentFamilyRelationship, FamilyIdentity, Value};

/// One member of the caller's family: its index in the roster slice, its
/// relationship to the caller, and the `parent/child` path that names it
/// when its parent has a name.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct FamilyRow {
    pub index: usize,
    pub relationship: AgentFamilyRelationship,
    pub path: Option<String>,
}

/// The caller's family over `rows`: its parent and children (never the
/// caller's own row), and the index of the caller's own row when the
/// roster carries it.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct Family {
    pub members: Vec<FamilyRow>,
    pub own_index: Option<usize>,
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
    let mut members = Vec::new();
    for (index, row) in rows.iter().enumerate() {
        if Some(index) == own_index {
            continue;
        }
        let child = forced_child(row) || is_child_of_caller(index);
        let relationship = if child {
            AgentFamilyRelationship::Child
        } else if own_parent == Some(index) {
            AgentFamilyRelationship::Parent
        } else {
            continue;
        };
        let path = match parent_of[index] {
            Some(parent) => parent_path(row_at(parent), row),
            None if child => parent_path(&own, row),
            None => None,
        };
        members.push(FamilyRow {
            index,
            relationship,
            path,
        });
    }
    Family { members, own_index }
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
