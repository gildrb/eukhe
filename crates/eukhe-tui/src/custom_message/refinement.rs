//! The refinement-outcome row: decode (TS `isRefinementOutcomeMessage`,
//! `refinementHeader`, `editLabel`, `editFieldRows`) and rendering (TS
//! `RefinementOutcomeMessageComponent` over `ExpandableEventMessage`, with
//! the `buildRichDiffLine` -/+ change rows).
//!
//! Split from the module root so the dispatch stays small; the shared row
//! types live in `super`.

use super::render::{pad_with, spacer, text_rows};
use super::{EditField, LabelPart, RefinementEditRow, RefinementOutcomeRow};
use crate::chat::{ChatEntry, Detail, StatusKind};
use crate::theme::{ColorMode, Theme, ThemeBg, ThemeColor};
use crate::width::wrap_line;
use crate::width::{str_width, truncate_line, wrap_text};
use crate::{Line, Span};
use serde::Deserialize;
use serde_json::Value;

/// One refinement's message scope (`details.scope`).
#[derive(Debug, Clone, Copy, Deserialize)]
#[serde(rename_all = "lowercase")]
enum Scope {
    Local,
    Global,
}

impl Scope {
    fn as_str(self) -> &'static str {
        match self {
            Self::Local => "local",
            Self::Global => "global",
        }
    }
}

/// One edit's action (`edits[].action`).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Deserialize)]
#[serde(rename_all = "lowercase")]
enum EditAction {
    Create,
    Update,
    Delete,
}

impl EditAction {
    fn as_str(self) -> &'static str {
        match self {
            Self::Create => "create",
            Self::Update => "update",
            Self::Delete => "delete",
        }
    }
}

/// The edited harness component (`edits[].kind`): free text, with
/// `memory` the one kind that pluralizes irregularly.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum EditKind<'a> {
    Memory,
    Other(&'a str),
}

impl<'a> EditKind<'a> {
    fn parse(kind: &'a str) -> Self {
        match kind {
            "memory" => Self::Memory,
            other => Self::Other(other),
        }
    }

    fn as_str(self) -> &'a str {
        match self {
            Self::Memory => "memory",
            Self::Other(kind) => kind,
        }
    }
}

/// The required envelope of a refinement outcome's details.
#[derive(Deserialize)]
struct OutcomeHead<'a> {
    #[serde(borrow)]
    summary: &'a str,
    scope: Scope,
}

/// The required fields of one edit.
#[derive(Deserialize)]
struct EditHead<'a> {
    action: EditAction,
    #[serde(borrow)]
    kind: &'a str,
    #[serde(borrow)]
    id: &'a str,
    applied: bool,
}

/// One decoded edit: its typed head over the raw entry, whose
/// `before`/`after`/field values stay opaque display data.
struct Edit<'a> {
    action: EditAction,
    kind: EditKind<'a>,
    id: &'a str,
    applied: bool,
    raw: &'a Value,
}

impl<'a> Edit<'a> {
    fn parse(raw: &'a Value) -> Option<Self> {
        if !raw.is_object() {
            return None;
        }
        let head = EditHead::deserialize(raw).ok()?;
        Some(Self {
            action: head.action,
            kind: EditKind::parse(head.kind),
            id: head.id,
            applied: head.applied,
            raw,
        })
    }
}

/// TS `isRefinementOutcomeMessage` (summary + scope + applied-edit list)
/// with the full outcome shape; malformed payloads render the notice.
pub(crate) fn refinement_outcome_entries(
    content: &eukhe_types::ai::UserContent,
    details: &Value,
) -> Vec<ChatEntry> {
    let head = details
        .is_object()
        .then(|| OutcomeHead::deserialize(details).ok())
        .flatten();
    let edits = details
        .get("edits")
        .and_then(Value::as_array)
        .and_then(|edits| {
            edits
                .iter()
                .map(Edit::parse)
                .collect::<Option<Vec<Edit<'_>>>>()
        });
    let (Some(head), Some(edits), eukhe_types::ai::UserContent::Text(_)) = (head, edits, content)
    else {
        return vec![ChatEntry::Status {
            text: "[Malformed refinement outcome message]".to_string(),
            kind: StatusKind::Error,
        }];
    };
    let applied: Vec<&Edit<'_>> = edits.iter().filter(|edit| edit.applied).collect();
    let rollback_of = details.get("rollbackOf").and_then(Value::as_str);
    let outcome = refinement_outcome_line(edits.len(), &applied, rollback_of);
    let scope = head.scope.as_str();
    let meta = format!(
        "{outcome} - Refinement {} - {scope}{}",
        details
            .get("refinementId")
            .and_then(Value::as_str)
            .unwrap_or(""),
        rollback_of
            .map(|id| format!(" - rollback of {id}"))
            .unwrap_or_default()
    );
    let header = if outcome.starts_with("Harness refined -") {
        "Harness refined".to_string()
    } else {
        outcome
    };
    vec![ChatEntry::RefinementOutcome(Box::new(
        RefinementOutcomeRow {
            header,
            summary: head.summary.to_string(),
            meta,
            edits: edits
                .iter()
                .map(|edit| refinement_edit_row(edit, scope))
                .collect(),
        },
    ))]
}

/// TS `refinementHeader`: the outcome line over the applied edit list.
fn refinement_outcome_line(
    edit_count: usize,
    applied: &[&Edit<'_>],
    rollback_of: Option<&str>,
) -> String {
    let operation = if rollback_of.is_some() {
        "Harness rollback"
    } else {
        "Harness refinement"
    };
    if edit_count == 0 {
        return if rollback_of.is_some() {
            "Harness rollback unchanged - no edits applied".to_string()
        } else {
            "Harness unchanged - no edits applied".to_string()
        };
    }
    let [first, ..] = applied else {
        return format!("{operation} failed - 0/{edit_count} edits applied");
    };
    let count = applied.len();
    if count < edit_count {
        return if rollback_of.is_some() {
            format!("Harness partially rolled back - {count}/{edit_count} edits applied")
        } else {
            format!("Harness partially refined - {count}/{edit_count} edits applied")
        };
    }
    if rollback_of.is_some() {
        return format!(
            "Harness rollback completed - {count} edit{} applied",
            if count == 1 { "" } else { "s" }
        );
    }
    if !applied.iter().all(|edit| edit.kind == first.kind) {
        return format!("Harness refined - {count} edits applied");
    }
    // TS: `memory` pluralizes to `memories`, every other kind just
    // appends `s`; mixed actions collapse to `changed`.
    let action = if applied.iter().all(|edit| edit.action == first.action) {
        match first.action {
            EditAction::Create => "created",
            EditAction::Update => "updated",
            EditAction::Delete => "deleted",
        }
    } else {
        "changed"
    };
    match (first.kind, count) {
        (EditKind::Memory, 1) => format!("Harness refined - 1 memory {action}"),
        (EditKind::Memory, _) => format!("Harness refined - {count} memories {action}"),
        (EditKind::Other(kind), 1) => format!("Harness refined - 1 {kind} {action}"),
        (EditKind::Other(kind), _) => format!("Harness refined - {count} {kind}s {action}"),
    }
}

/// TS `editLabel`/`editFieldRows` for one edit; `editScope(edit, fallback)`
/// takes the edit's own scope, else the message scope.
fn refinement_edit_row(edit: &Edit<'_>, fallback_scope: &str) -> RefinementEditRow {
    let raw = edit.raw;
    let scope = raw
        .get("after")
        .and_then(|after| after.get("scope"))
        .and_then(Value::as_str)
        .or_else(|| {
            raw.get("before")
                .and_then(|before| before.get("scope"))
                .and_then(Value::as_str)
        })
        .unwrap_or(fallback_scope);
    let kind = edit.kind.as_str();
    let id = edit.id;
    let label = if edit.applied {
        let verb = match edit.action {
            EditAction::Create => "Created",
            EditAction::Update => "Updated",
            EditAction::Delete => "Deleted",
        };
        vec![
            LabelPart {
                text: verb.to_string(),
                color: Some(ThemeColor::Success),
            },
            LabelPart {
                text: format!(" {scope} {kind} `{id}`"),
                color: None,
            },
        ]
    } else {
        let action = edit.action.as_str();
        let error = raw
            .get("error")
            .and_then(Value::as_str)
            .map(|error| format!(": {error}"))
            .unwrap_or_default();
        vec![LabelPart {
            text: format!("Failed to {action} {scope} {kind} `{id}`{error}"),
            color: Some(ThemeColor::Error),
        }]
    };
    RefinementEditRow {
        label,
        reason: raw
            .get("reason")
            .and_then(Value::as_str)
            .map(str::to_string),
        fields: edit_field_rows(edit),
    }
}

/// The editable harness fields shown per edit, in display order (TS
/// `EDIT_FIELDS`), with their display labels.
const EDIT_FIELDS: [(&str, &str); 6] = [
    ("title", "Title"),
    ("content", "Description"),
    ("path", "Path"),
    ("reference", "Reference"),
    ("arguments", "Arguments"),
    ("metadata", "Metadata"),
];

/// TS `fieldValueLines`: strings split on newlines, objects one JSON row,
/// everything else (and empty values) no rows.
fn field_value_lines(value: Option<&Value>) -> Vec<String> {
    match value {
        Some(Value::String(text)) if !text.is_empty() => {
            text.split('\n').map(str::to_string).collect()
        }
        Some(value @ Value::Object(map)) if !map.is_empty() => {
            vec![serde_json::to_string(value).unwrap_or_default()]
        }
        Some(_) | None => Vec::new(),
    }
}

/// One entry's field rows (TS `entryFieldRows`).
fn entry_field_rows(entry: &Value) -> Vec<EditField> {
    EDIT_FIELDS
        .iter()
        .filter_map(|(key, label)| {
            let value = field_value_lines(entry.get(*key));
            (!value.is_empty()).then(|| EditField {
                label: (*label).to_string(),
                value,
                change: None,
            })
        })
        .collect()
}

/// The edit fields for one edit (TS `editFieldRows`): failed edits show
/// before/proposed, updates show -/+ changes for changed fields, create and
/// delete show their value as added/removed rows.
fn edit_field_rows(edit: &Edit<'_>) -> Vec<EditField> {
    let raw = edit.raw;
    let before = raw.get("before").filter(|v| v.is_object());
    let after = raw.get("after").filter(|v| v.is_object());
    if !edit.applied {
        let proposed = entry_field_rows(after.unwrap_or(raw));
        return match before {
            None => proposed,
            Some(before) => {
                let mut rows: Vec<EditField> = entry_field_rows(before)
                    .into_iter()
                    .map(|field| EditField {
                        label: format!("Before {}", field.label),
                        ..field
                    })
                    .collect();
                rows.extend(proposed.into_iter().map(|field| EditField {
                    label: format!("Proposed {}", field.label),
                    ..field
                }));
                rows
            }
        };
    }
    if let (Some(before), Some(after)) = (before, after) {
        // TS `updateFieldRows`: one plain row per unchanged field, -/+ for
        // changed ones. Rows hold no newline, so row equality is the
        // joined-text equality.
        return EDIT_FIELDS
            .iter()
            .filter_map(|(key, label)| {
                let removed = field_value_lines(before.get(*key));
                let added = field_value_lines(after.get(*key));
                if removed.is_empty() && added.is_empty() {
                    return None;
                }
                let label = (*label).to_string();
                if removed == added {
                    return Some(EditField {
                        label,
                        value: added,
                        change: None,
                    });
                }
                Some(EditField {
                    label,
                    value: Vec::new(),
                    change: Some((removed, added)),
                })
            })
            .collect();
    }
    let fields = entry_field_rows(after.or(before).unwrap_or(raw));
    // TS: delete moves the value to the removed rows, create to the added
    // rows (one branch or the other, never both).
    if edit.action == EditAction::Update {
        return fields;
    }
    fields
        .into_iter()
        .map(|field| EditField {
            label: field.label,
            value: Vec::new(),
            change: Some(match edit.action {
                EditAction::Delete => (field.value, Vec::new()),
                EditAction::Create => (Vec::new(), field.value),
                EditAction::Update => (Vec::new(), Vec::new()),
            }),
        })
        .collect()
}

mod layout;
pub(crate) use layout::render_refinement_outcome;

/// One line-diff op over the field's removed/added values.
enum DiffOp<'a> {
    Context(&'a str),
    Removed(&'a str),
    Added(&'a str),
}

/// Longest-common-subsequence line diff (the full-context form of the TS
/// `diff` package's `diffLines`): equal runs stay in order, removals come
/// before the additions that replace them.
fn line_diff<'a>(removed: &'a [String], added: &'a [String]) -> Vec<DiffOp<'a>> {
    let mut table = vec![vec![0usize; added.len() + 1]; removed.len() + 1];
    for (i, r) in removed.iter().enumerate().rev() {
        for (j, a) in added.iter().enumerate().rev() {
            table[i][j] = if r == a {
                table[i + 1][j + 1] + 1
            } else {
                table[i + 1][j].max(table[i][j + 1])
            };
        }
    }
    let mut ops = Vec::new();
    let (mut i, mut j) = (0usize, 0usize);
    while i < removed.len() && j < added.len() {
        if removed[i] == added[j] {
            ops.push(DiffOp::Context(&removed[i]));
            i += 1;
            j += 1;
        } else if table[i + 1][j] >= table[i][j + 1] {
            ops.push(DiffOp::Removed(&removed[i]));
            i += 1;
        } else {
            ops.push(DiffOp::Added(&added[j]));
            j += 1;
        }
    }
    while i < removed.len() {
        ops.push(DiffOp::Removed(&removed[i]));
        i += 1;
    }
    while j < added.len() {
        ops.push(DiffOp::Added(&added[j]));
        j += 1;
    }
    ops
}

#[cfg(test)]
mod tests {
    use super::*;
    use serde_json::json;

    fn theme() -> Theme {
        Theme::builtin("forge", ColorMode::TrueColor)
    }

    fn flat(row: &Line) -> String {
        row.iter().map(|s| s.content.as_str()).collect()
    }

    fn decoded(message: &serde_json::Value) -> Vec<ChatEntry> {
        crate::custom_message::tests::decoded(message)
    }

    #[test]
    fn refinement_outcome_decodes_header_and_edits() {
        let entries = decoded(&json!({
            "role": "custom",
            "customType": "refinement_outcome",
            "content": "Refinement complete: add a memory",
            "display": true,
            "details": {
                "refinementId": "refine_1",
                "summary": "add a memory",
                "scope": "local",
                "edits": [
                    {
                        "action": "create",
                        "kind": "memory",
                        "id": "mission",
                        "applied": true,
                        "reason": "durable",
                        "title": "Mission",
                        "content": "Keep going",
                        "after": { "id": "mission", "kind": "memory", "title": "Mission", "content": "Keep going", "scope": "local" },
                    }
                ],
            },
        }));
        let [ChatEntry::RefinementOutcome(row)] = entries.as_slice() else {
            panic!("refinement row: {entries:?}");
        };
        assert_eq!(row.header, "Harness refined");
        assert_eq!(row.summary, "add a memory");
        assert_eq!(
            row.meta,
            "Harness refined - 1 memory created - Refinement refine_1 - local"
        );
        assert_eq!(row.edits.len(), 1);
        assert_eq!(row.edits[0].label[0].text, "Created");
        assert_eq!(row.edits[0].label[1].text, " local memory `mission`");
        assert_eq!(row.edits[0].reason.as_deref(), Some("durable"));
        // Create edits show their value as added change rows.
        let field = &row.edits[0].fields[0];
        assert_eq!(field.label, "Title");
        assert_eq!(
            field.change.as_ref().unwrap().1,
            vec!["Mission".to_string()]
        );

        // TS `isRefinementOutcomeMessage` runs `edits.every(isAppliedRefinementEdit)`,
        // which passes on an empty list: an outcome with no edits is valid
        // and renders the `Harness unchanged` row.
        let empty = decoded(&json!({
            "role": "custom",
            "customType": "refinement_outcome",
            "content": "Refinement complete: ?",
            "display": true,
            "details": { "refinementId": "x", "summary": "?", "scope": "local", "edits": [] },
        }));
        let [ChatEntry::RefinementOutcome(row)] = empty.as_slice() else {
            panic!("empty-edits refinement row: {empty:?}");
        };
        assert_eq!(row.header, "Harness unchanged - no edits applied");

        // An unknown scope fails the TS envelope check and renders the notice.
        let malformed = decoded(&json!({
            "role": "custom",
            "customType": "refinement_outcome",
            "content": "Refinement complete: ?",
            "display": true,
            "details": { "refinementId": "x", "summary": "?", "scope": "team", "edits": [] },
        }));
        assert_eq!(
            malformed,
            vec![ChatEntry::Status {
                text: "[Malformed refinement outcome message]".to_string(),
                kind: StatusKind::Error,
            }]
        );
    }

    #[test]
    fn refinement_outcome_lines_match_ts() {
        // TS `refinementHeader` across the applied/total matrix.
        let edit = |applied: bool, kind: &str, action: &str| json!({ "action": action, "kind": kind, "id": "e", "applied": applied });
        // TS `refinementHeader` filters `edits.filter((edit) => edit.applied)`
        // before comparing to the total, so the helper passes only the
        // applied edits as the applied list.
        let line = |edits: Vec<serde_json::Value>, rollback: bool| {
            let edits: Vec<Edit<'_>> = edits.iter().filter_map(Edit::parse).collect();
            let applied: Vec<&Edit<'_>> = edits.iter().filter(|edit| edit.applied).collect();
            refinement_outcome_line(edits.len(), &applied, rollback.then_some("r"))
        };
        assert_eq!(
            line(
                vec![
                    edit(true, "memory", "create"),
                    edit(false, "memory", "create")
                ],
                false
            ),
            "Harness partially refined - 1/2 edits applied"
        );
        assert_eq!(line(vec![], false), "Harness unchanged - no edits applied");
        assert_eq!(
            line(
                vec![
                    edit(true, "memory", "create"),
                    edit(true, "skill", "update")
                ],
                false
            ),
            "Harness refined - 2 edits applied"
        );
        assert_eq!(
            line(vec![edit(true, "skill", "delete")], true),
            "Harness rollback completed - 1 edit applied"
        );
        assert_eq!(
            line(
                vec![edit(true, "skill", "delete"), edit(true, "skill", "delete")],
                true
            ),
            "Harness rollback completed - 2 edits applied"
        );
        // Edits present but none applied: the operation-failed line (TS
        // distinguishes this from the empty-edit "unchanged" line).
        assert_eq!(
            line(vec![edit(false, "memory", "create")], false),
            "Harness refinement failed - 0/1 edits applied"
        );
        assert_eq!(
            line(
                vec![
                    edit(false, "memory", "create"),
                    edit(false, "memory", "update")
                ],
                true
            ),
            "Harness rollback failed - 0/2 edits applied"
        );
    }

    #[test]
    fn refinement_outcome_collapsed_shape() {
        let row = RefinementOutcomeRow {
            header: "Harness refined".to_string(),
            summary: "add a memory for the mission".to_string(),
            meta: "Harness refined - 1 memory created - Refinement r1 - local".to_string(),
            edits: Vec::new(),
        };
        let rows = render_refinement_outcome(&row, Detail::Overview, &theme(), 60);
        // Blank, diamond header, summary row.
        assert!(rows[0].is_empty());
        assert_eq!(flat(&rows[1]).trim_end(), " * Harness refined");
        assert_eq!(
            rows[1][1],
            Span::styled(
                "* Harness refined".to_string(),
                theme().fg_style(ThemeColor::RefinementHeader)
            )
        );
        assert_eq!(flat(&rows[2]), " add a memory for the mission");
        // TS `EventSummary` colors the inset space inside the summary
        // span (the space is part of the styled text): one styled span.
        assert_eq!(
            rows[2],
            vec![Span::styled(
                " add a memory for the mission".to_string(),
                theme().fg_style(ThemeColor::RefinementSummary)
            )]
        );
    }

    #[test]
    fn refinement_summary_collapses_whitespace_and_clamps() {
        let row = RefinementOutcomeRow {
            header: "Harness refined".to_string(),
            summary: "one   two\n\nthree four five six seven".to_string(),
            meta: String::new(),
            edits: Vec::new(),
        };
        // Collapsed (TS `EventSummary` under `setExpanded(false)`, i.e.
        // tool output not expanded): whitespace-collapsed and clamped to
        // two lines at width 14 (content width 13), the second line keeps
        // its ellipsis. `Detail::Details` expands edit diffs but not tool
        // output, so the summary stays collapsed there too.
        let rows = render_refinement_outcome(&row, Detail::Overview, &theme(), 14);
        // TS `Text(..., 1, 0)` wraps the header at content width 12, so the
        // `* Harness refined` header spans rows[1..3] before the summary.
        assert_eq!(flat(&rows[1]).trim_end(), " * Harness");
        assert_eq!(flat(&rows[2]).trim_end(), " refined");
        assert_eq!(flat(&rows[3]), " one two three");
        assert_eq!(flat(&rows[4]), " four five ...");
        let rows = render_refinement_outcome(&row, Detail::Details, &theme(), 60);
        assert!(rows
            .iter()
            .any(|r| flat(r) == " one two three four five six seven"));
        // Expanded (`Detail::All`): the raw summary hangs on the branch
        // grammar -- the first row carries the dim ``- ` gutter,
        // the newline-joined source rows the matching continuation indent.
        let rows = render_refinement_outcome(&row, Detail::All, &theme(), 60);
        assert_eq!(
            flat(&rows[2]),
            format!(" {}one   two", crate::branch::BRANCH_GUTTER)
        );
        // The empty source-line segment renders as an indented blank row,
        // the wrapped content after it.
        assert_eq!(flat(&rows[3]), crate::branch::BRANCH_INDENT.to_string());
        assert_eq!(
            flat(&rows[4]),
            format!("{}three four five six seven", crate::branch::BRANCH_INDENT)
        );
    }

    #[test]
    fn refinement_expanded_shows_meta_and_edits() {
        let row = RefinementOutcomeRow {
            header: "Harness refined".to_string(),
            summary: "add a memory".to_string(),
            meta: "Harness refined - 1 memory created - Refinement r1 - local".to_string(),
            edits: vec![RefinementEditRow {
                label: vec![
                    LabelPart {
                        text: "Created".to_string(),
                        color: Some(ThemeColor::Success),
                    },
                    LabelPart {
                        text: " local memory `mission`".to_string(),
                        color: None,
                    },
                ],
                reason: Some("durable".to_string()),
                fields: vec![
                    EditField {
                        label: "Title".to_string(),
                        value: Vec::new(),
                        change: Some((vec![], vec!["Mission".to_string()])),
                    },
                    EditField {
                        label: "Description".to_string(),
                        value: vec!["Keep going".to_string()],
                        change: None,
                    },
                ],
            }],
        };
        let rows = render_refinement_outcome(&row, Detail::All, &theme(), 80);
        let text: Vec<String> = rows
            .iter()
            .map(|r| flat(r).trim_end().to_string())
            .collect();
        // The expanded block hangs on the branch grammar: the meta row
        // and every edit-section row sit on the continuation indent, each
        // edit section's label row re-branches with the ``- `
        // gutter.
        let meta = text
            .iter()
            .position(|r| {
                r.trim() == "Harness refined - 1 memory created - Refinement r1 - local"
                    && r.starts_with(crate::branch::BRANCH_INDENT)
            })
            .expect("meta row");
        let label = text
            .iter()
            .position(|r| {
                r.strip_prefix(&format!(" {}", crate::branch::BRANCH_GUTTER))
                    .is_some_and(|rest| rest == "Created local memory `mission`")
            })
            .expect("edit label");
        let field_label = text
            .iter()
            .position(|r| r.trim() == "Title" && r.starts_with(crate::branch::BRANCH_INDENT))
            .expect("field label");
        let added = text
            .iter()
            .position(|r| r.contains(" + Mission"))
            .expect("+ added row");
        assert!(
            text[added].starts_with(crate::branch::BRANCH_INDENT),
            "the diff block sits on the continuation indent: {:?}",
            text[added]
        );
        let value = text
            .iter()
            .position(|r| r.trim() == "Keep going" && r.starts_with(crate::branch::BRANCH_INDENT))
            .expect("value row");
        let reason = text
            .iter()
            .position(|r| {
                r.trim() == "Reason: durable" && r.starts_with(crate::branch::BRANCH_INDENT)
            })
            .expect("reason row");
        assert!(meta < label && label < field_label && field_label < added);
        assert!(added < value && value < reason);
    }
}
