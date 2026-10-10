//! The `edit` tool. Port of `tools/edit.ts`.

use std::sync::Arc;

use eukhe_chord::json::to_json;
use eukhe_pi_ai::typebox::{Options, TSchema, Type};
use eukhe_types::pi_ai::{JsonObject, JsonValue as PiJsonValue, TextContent, UserContentBlock};
use serde::{Deserialize, Serialize};

use super::edit_diff::{
    apply_edits_to_normalized_content, detect_line_ending, generate_diff_string,
    generate_unified_patch, normalize_to_lf, restore_line_endings, strip_bom, Edit,
    DEFAULT_CONTEXT_LINES,
};
use super::env::{operation_aborted, require_env};
use super::file_mutation_queue::with_file_mutation_queue;
use super::path_utils::resolve_tool_path;
use crate::env::{FileError, FileKind};
use crate::harness::define::define_tool;
use crate::harness::types::{ToolExecutionResult, ToolRegistration};
use crate::session::{SessionError, SessionResult};

fn edit_schema() -> TSchema {
    let replace_edit_schema = Type::object([
        (
            "oldText",
            Type::string_with(Options::new().set(
                "description",
                "Exact text for one targeted replacement. It must be unique in the original file and must not overlap with any other edits[].oldText in the same call.",
            )),
        ),
        (
            "newText",
            Type::string_with(
                Options::new().set("description", "Replacement text for this targeted edit."),
            ),
        ),
    ]);
    Type::object([
        (
            "path",
            Type::string_with(Options::new().set(
                "description",
                "Path to the file to edit (relative or absolute)",
            )),
        ),
        (
            "edits",
            Type::array_with(
                replace_edit_schema,
                Options::new().set(
                    "description",
                    "One or more targeted replacements. Each edit is matched against the original file, not incrementally. Do not include overlapping or nested edits. If two changes touch the same block or nearby lines, merge them into one edit instead.",
                ),
            ),
        ),
    ])
}

/// One replacement of `edit` (TS `EditToolInput["edits"][number]`).
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ReplaceEdit {
    pub old_text: String,
    pub new_text: String,
}

/// Arguments of `edit` (TS `EditToolInput`).
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct EditToolInput {
    pub path: String,
    pub edits: Vec<ReplaceEdit>,
}

/// Details of a successful edit (TS `EditToolDetails`).
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct EditToolDetails {
    pub diff: String,
    pub patch: String,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub first_changed_line: Option<usize>,
}

/// TS `isSingleEditInput`: an object whose `oldText` and `newText` are
/// strings.
fn is_single_edit_input(value: &PiJsonValue) -> bool {
    value.as_object().is_some_and(|edit| {
        edit.get("oldText").is_some_and(PiJsonValue::is_string)
            && edit.get("newText").is_some_and(PiJsonValue::is_string)
    })
}

/// Repair shapes models commonly send: `edits` as a JSON string or as a
/// single edit object, and a top-level `oldText`/`newText` pair. Works on a
/// copy; the call's arguments stay unchanged.
fn prepare_edit_arguments(input: PiJsonValue) -> PiJsonValue {
    let PiJsonValue::Object(mut args) = input else {
        return input;
    };
    match args.get("edits") {
        Some(PiJsonValue::String(text)) => {
            // `JSON.parse` failures leave the arguments as they were.
            if let Ok(parsed) = serde_json::from_str::<PiJsonValue>(text) {
                if parsed.is_array() {
                    args.insert("edits".to_owned(), parsed);
                } else if is_single_edit_input(&parsed) {
                    args.insert("edits".to_owned(), PiJsonValue::Array(vec![parsed]));
                }
            }
        }
        Some(edits) if is_single_edit_input(edits) => {
            let edit = edits.clone();
            args.insert("edits".to_owned(), PiJsonValue::Array(vec![edit]));
        }
        Some(_) | None => {}
    }

    let (Some(PiJsonValue::String(old_text)), Some(PiJsonValue::String(new_text))) =
        (args.get("oldText"), args.get("newText"))
    else {
        return PiJsonValue::Object(args);
    };
    let mut legacy = JsonObject::new();
    legacy.insert("oldText".to_owned(), PiJsonValue::String(old_text.clone()));
    legacy.insert("newText".to_owned(), PiJsonValue::String(new_text.clone()));
    let mut edits = match args.get("edits") {
        Some(PiJsonValue::Array(edits)) => edits.clone(),
        Some(_) | None => Vec::new(),
    };
    edits.push(PiJsonValue::Object(legacy));
    // `{ ...rest, edits }`: an existing `edits` keeps its position.
    args.shift_remove("oldText");
    args.shift_remove("newText");
    args.insert("edits".to_owned(), PiJsonValue::Array(edits));
    PiJsonValue::Object(args)
}

/// TS `validateEditInput`: the path and at least one replacement.
fn validate_edit_input(input: PiJsonValue) -> SessionResult<(String, Vec<Edit>)> {
    let has_edits = input
        .get("edits")
        .and_then(PiJsonValue::as_array)
        .is_some_and(|edits| !edits.is_empty());
    if !has_edits {
        return Err(SessionError::error(
            "Edit tool input is invalid. edits must contain at least one replacement.",
        ));
    }
    let EditToolInput { path, edits } =
        serde_json::from_value(input).map_err(SessionError::other)?;
    let edits = edits
        .into_iter()
        .map(|edit| Edit {
            old_text: edit.old_text,
            new_text: edit.new_text,
        })
        .collect();
    Ok((path, edits))
}

/// TS `editAccessError`: the message names the path and the error code; the
/// cause is the [`FileError`].
#[derive(Debug, thiserror::Error)]
#[error("Could not edit file: {path}. Error code: {}.", cause.code)]
struct EditAccessError {
    path: String,
    #[source]
    cause: FileError,
}

fn edit_access_error(path: &str, error: FileError) -> SessionError {
    SessionError::other(EditAccessError {
        path: path.to_owned(),
        cause: error,
    })
}

/// Edits one file by exact text replacement.
#[must_use]
pub fn create_edit_tool() -> Arc<ToolRegistration> {
    let mut tool = ToolRegistration::new(
        "edit",
        "Edit a single file using exact text replacement. Every edits[].oldText must match a unique, non-overlapping region of the original file. If two changes affect the same block or nearby lines, merge them into one edit instead of emitting overlapping edits. Do not include large unchanged regions just to connect distant changes.",
        edit_schema(),
        |args, api, cx| async move {
            let (path, edits) = validate_edit_input(args)?;
            let env = require_env(api.as_ref())?;
            let absolute_path = resolve_tool_path(env.as_ref(), &path, &cx).await?;
            with_file_mutation_queue(
                env.as_ref(),
                &absolute_path,
                || async {
                    if cx.aborted() {
                        return Err(operation_aborted());
                    }
                    let info = env
                        .file_info(&absolute_path, &cx)
                        .await
                        .map_err(|error| edit_access_error(&path, error))?;
                    if info.kind != FileKind::File && info.kind != FileKind::Symlink {
                        return Err(SessionError::error(format!(
                            "Could not edit file: {path}. Path is not a file."
                        )));
                    }

                    let read = env
                        .read_text_file(&absolute_path, &cx)
                        .await
                        .map_err(|error| edit_access_error(&path, error))?;
                    if cx.aborted() {
                        return Err(operation_aborted());
                    }

                    let split = strip_bom(&read);
                    let original_ending = detect_line_ending(split.text);
                    let normalized_content = normalize_to_lf(split.text);
                    let applied =
                        apply_edits_to_normalized_content(&normalized_content, &edits, &path)
                            .map_err(SessionError::other)?;
                    if cx.aborted() {
                        return Err(operation_aborted());
                    }

                    let final_content = format!(
                        "{}{}",
                        split.bom,
                        restore_line_endings(&applied.new_content, original_ending)
                    );
                    env.write_file(&absolute_path, final_content.as_bytes(), &cx)
                        .await
                        .map_err(|error| edit_access_error(&path, error))?;
                    if cx.aborted() {
                        return Err(operation_aborted());
                    }

                    let diff = generate_diff_string(
                        &applied.base_content,
                        &applied.new_content,
                        DEFAULT_CONTEXT_LINES,
                    );
                    let details = EditToolDetails {
                        diff: diff.diff,
                        patch: generate_unified_patch(
                            &path,
                            &applied.base_content,
                            &applied.new_content,
                            DEFAULT_CONTEXT_LINES,
                        ),
                        first_changed_line: diff.first_changed_line,
                    };
                    Ok(ToolExecutionResult {
                        output: Some(vec![UserContentBlock::Text(TextContent::new(format!(
                            "Successfully replaced {} block(s) in {path}.",
                            edits.len()
                        )))]),
                        details: Some(to_json(&details)?),
                        ..ToolExecutionResult::default()
                    })
                },
                &cx,
            )
            .await
        },
    );
    tool.prepare_arguments = Some(Arc::new(|args| Ok(prepare_edit_arguments(args))));
    define_tool(tool)
}
