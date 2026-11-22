//! `/undo` and `/diff`: the per-prompt workspace snapshots of a top-level
//! session. The `undo_turn` command answers an [`UndoReply`], the
//! `get_turn_diff` command a [`TurnDiffReply`]; [`undo_text`] and
//! [`diff_text`] are what every surface prints of them.

use serde::{Deserialize, Serialize};

use crate::effects::RanEffect;

/// What `/diff` compares the workspace with.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub enum DiffScope {
    /// The start of the newest turn not undone.
    #[default]
    Turn,
    /// The start of the session's first turn (`/diff all`).
    All,
}

/// The `undo_turn` response data.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct UndoReply {
    /// The workspace paths written back or removed, sorted.
    pub restored: Vec<String>,
    /// The turn whose start the workspace is back at.
    pub turn: u64,
    /// How many more turns `/undo` can take back.
    pub left: u64,
    /// The irreversible effects of the undone prompt's run, in ledger
    /// order: they ran, and `/undo` does not take them back.
    pub not_undone: Vec<RanEffect>,
}

/// The `get_turn_diff` response data.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct TurnDiffReply {
    /// The unified diff from the snapshot to the workspace.
    pub diff: String,
    /// The paths that differ, sorted.
    pub paths: Vec<String>,
    /// Paths held back (ignored, over the size cap, nested repositories as
    /// `dir/`): not compared.
    pub skipped: Vec<String>,
}

/// What an undo prints: the prompt the workspace is back at, each path
/// restored, how many prompts are left, then each irreversible effect of
/// the undone prompt's run under `Not undone (irreversible):` (none when
/// it had none).
#[must_use]
pub fn undo_text(reply: &UndoReply) -> String {
    let count = match reply.restored.len() {
        1 => "1 path".to_owned(),
        n => format!("{n} paths"),
    };
    let mut lines = vec![format!(
        "Restored the workspace to the start of prompt {} ({count}).",
        reply.turn
    )];
    lines.extend(reply.restored.iter().map(|path| format!("  {path}")));
    lines.push(match reply.left {
        0 => "Nothing more to undo.".to_owned(),
        1 => "1 more prompt to undo.".to_owned(),
        n => format!("{n} more prompts to undo."),
    });
    if !reply.not_undone.is_empty() {
        lines.push("Not undone (irreversible):".to_owned());
        lines.extend(reply.not_undone.iter().map(RanEffect::report_line));
    }
    format!("{}\n", lines.join("\n"))
}

/// What a diff prints: the unified diff (`No changes.` when no path
/// differs), then each path not compared.
#[must_use]
pub fn diff_text(reply: &TurnDiffReply) -> String {
    let mut text = match reply.paths.as_slice() {
        [] => "No changes.\n".to_owned(),
        _ => reply.diff.clone(),
    };
    text.extend(
        reply.skipped.iter().map(|path| {
            format!("Not compared (ignored, too large or a nested repository): {path}\n")
        }),
    );
    text
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::effects::{EffectClass, RanKind};
    use serde_json::json;

    fn pushed() -> RanEffect {
        RanEffect {
            id: "e3".to_owned(),
            key: "s1:call1:0".to_owned(),
            run: 2,
            kind: RanKind::ShellStep,
            command: "git push origin main".to_owned(),
            classes: vec![EffectClass::Net],
            agent: None,
            session_id: "s1".to_owned(),
            at_ms: 7,
        }
    }

    #[test]
    fn replies_and_scope_use_the_wire_names() {
        assert_eq!(
            (
                serde_json::to_value(DiffScope::All).unwrap(),
                serde_json::to_value(UndoReply {
                    restored: vec!["a.txt".to_owned()],
                    turn: 2,
                    left: 1,
                    not_undone: vec![pushed()],
                })
                .unwrap(),
                serde_json::to_value(TurnDiffReply {
                    diff: String::new(),
                    paths: Vec::new(),
                    skipped: vec!["big.bin".to_owned()],
                })
                .unwrap(),
            ),
            (
                json!("all"),
                json!({ "restored": ["a.txt"], "turn": 2, "left": 1,
                    "notUndone": [serde_json::to_value(pushed()).unwrap()] }),
                json!({ "diff": "", "paths": [], "skipped": ["big.bin"] }),
            )
        );
    }

    #[test]
    fn an_undo_names_the_effects_of_its_run_it_does_not_take_back() {
        let reply = |not_undone| UndoReply {
            restored: vec!["a.txt".to_owned(), "b.txt".to_owned()],
            turn: 2,
            left: 1,
            not_undone,
        };
        assert_eq!(
            (
                undo_text(&reply(vec![pushed()])),
                undo_text(&reply(Vec::new()))
            ),
            (
                "Restored the workspace to the start of prompt 2 (2 paths).\n  a.txt\n  b.txt\n\
1 more prompt to undo.\nNot undone (irreversible):\n- e3 git push origin main (net)\n"
                    .to_owned(),
                "Restored the workspace to the start of prompt 2 (2 paths).\n  a.txt\n  b.txt\n\
1 more prompt to undo.\n"
                    .to_owned(),
            )
        );
    }
}
