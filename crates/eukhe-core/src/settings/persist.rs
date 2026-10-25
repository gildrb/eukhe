//! The read/modify/write of one config document (`settings.json`,
//! `mcp-connections.json`, `auth.json`): a writer reads the document on
//! disk under its lock, classifies the read (missing, parsed or broken)
//! and lets the compiled core decide what to write (`laws/config.bend`
//! `rmw_refuses_broken`, `rmw_keeps_others`, `rmw_applies_change`,
//! `rmw_keeps_place`, `settings_save_preserves`): a document that cannot
//! be read or parsed is never written; every other key keeps its value and
//! its place.

use std::fmt;

use eukhe_bend::rules::config;
use serde_json::{Map, Value};

/// What the value a setter wrote does: it applies, or a higher layer
/// sets the same setting.
#[derive(Debug, Clone, PartialEq, Eq)]
#[must_use]
pub enum Persisted {
    /// The written value is the value that applies.
    Applies,
    /// A higher layer sets these settings, so the written values do not
    /// apply.
    Shadowed(Vec<Shadow>),
}

/// A written setting that a higher layer sets.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Shadow {
    /// The setting (its cvar id).
    pub id: String,
    /// The file that sets it (a path, or a name when the storage has no
    /// files).
    pub file: String,
}

impl Persisted {
    /// `Ok` when the written value applies; else an error that names each
    /// file that shadows it (for a caller that shows a failure).
    ///
    /// # Errors
    ///
    /// A higher layer sets a written setting.
    pub fn applied(self) -> anyhow::Result<()> {
        match self {
            Persisted::Applies => Ok(()),
            shadowed @ Persisted::Shadowed(_) => Err(anyhow::anyhow!("{shadowed}")),
        }
    }
}

impl fmt::Display for Shadow {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "`{}` is saved, but {} also sets it, so that value applies",
            self.id, self.file
        )
    }
}

impl fmt::Display for Persisted {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Persisted::Applies => write!(f, "saved"),
            Persisted::Shadowed(shadows) => {
                let texts: Vec<String> = shadows.iter().map(Shadow::to_string).collect();
                write!(f, "{}", texts.join("; "))
            }
        }
    }
}

/// How a read of a settings document ended.
#[derive(Debug, Clone, PartialEq)]
pub(crate) enum DocRead {
    /// No file: a write starts from the empty document.
    Missing,
    /// The document, a JSON object.
    Parsed(Map<String, Value>),
    /// The file is there but it is not a JSON object: the reason.
    Broken(String),
}

/// Classify the content of a settings file (`None`: no file).
pub(crate) fn read_document(content: Option<&str>) -> DocRead {
    let Some(content) = content else {
        return DocRead::Missing;
    };
    match serde_json::from_str::<Value>(content) {
        Ok(Value::Object(document)) => DocRead::Parsed(document),
        Ok(
            Value::Null | Value::Bool(_) | Value::Number(_) | Value::String(_) | Value::Array(_),
        ) => DocRead::Broken("the document is not a JSON object".to_string()),
        Err(error) => DocRead::Broken(error.to_string()),
    }
}

/// One change of a key path.
#[derive(Debug, Clone, PartialEq)]
pub(crate) enum KeyEdit {
    Set(Value),
    Remove,
}

/// The read of the value at a key of a parent: none (or `null`) is a
/// missing document, an object a parsed one, anything else a broken one
/// (an edit under it would drop that value).
fn child_read(document: &Map<String, Value>, at: &[&str], path: &[&str]) -> DocRead {
    match at.last().and_then(|key| document.get(*key)) {
        None | Some(Value::Null) => DocRead::Missing,
        Some(Value::Object(child)) => DocRead::Parsed(child.clone()),
        Some(Value::Bool(_) | Value::Number(_) | Value::String(_) | Value::Array(_)) => {
            DocRead::Broken(format!(
                "`{}` is not an object, so `{}` cannot be written",
                at.join("."),
                path.join(".")
            ))
        }
    }
}

/// Apply `edit` at `path` of the document `read` (the read of a writer
/// under its lock): the compiled core decides each level of the path
/// (`Cf.rmw`), the innermost first; the level above sets its key to the
/// object below. Returns the document to write and the value the edit
/// replaced. A removal under a parent that is not there removes nothing
/// (the path is absent).
///
/// # Errors
///
/// The core refuses a broken read: the reason of the read (the document,
/// or a parent on `path` that is not an object).
pub(crate) fn edit_read(
    read: DocRead,
    path: &[&str],
    edit: &KeyEdit,
) -> Result<(Map<String, Value>, Option<Value>), String> {
    edit_level(read, path, 1, edit)
}

/// Apply `edits` in order to the document `read`, each with [`edit_read`]
/// over what the one before wrote: the document to write, or `None` when
/// no edit changed it (a set always does; a removal does when its key was
/// there).
///
/// # Errors
///
/// As [`edit_read`], for the first edit the core refuses.
pub(crate) fn edit_document(
    read: DocRead,
    edits: Vec<(Vec<&str>, KeyEdit)>,
) -> Result<Option<Map<String, Value>>, String> {
    let mut read = read;
    let mut changed = false;
    for (path, edit) in edits {
        let (document, replaced) = edit_read(read, &path, &edit)?;
        changed |= matches!(edit, KeyEdit::Set(_)) || replaced.is_some();
        read = DocRead::Parsed(document);
    }
    Ok(match read {
        DocRead::Parsed(document) if changed => Some(document),
        DocRead::Missing | DocRead::Parsed(_) | DocRead::Broken(_) => None,
    })
}

/// [`edit_read`] at the level of `path[depth - 1]`.
fn edit_level(
    read: DocRead,
    path: &[&str],
    depth: usize,
    edit: &KeyEdit,
) -> Result<(Map<String, Value>, Option<Value>), String> {
    let Some(key) = depth.checked_sub(1).and_then(|at| path.get(at)) else {
        return Err("an empty key path".to_string());
    };
    let (document, missing, refused) = match read {
        DocRead::Missing => (Map::new(), true, None),
        DocRead::Parsed(document) => (document, false, None),
        DocRead::Broken(reason) => (Map::new(), false, Some(reason)),
    };
    let (level_edit, replaced) = if depth == path.len() {
        (edit.clone(), document.get(*key).cloned())
    } else {
        let below = child_read(&document, &path[..depth], path);
        if refused.is_none() && matches!(edit, KeyEdit::Remove) && matches!(below, DocRead::Missing)
        {
            return Ok((document, None));
        }
        let (child, replaced) = edit_level(below, path, depth + 1, edit)?;
        (KeyEdit::Set(Value::Object(child)), replaced)
    };
    let read = match (missing, &refused) {
        (_, Some(_)) => config::Read::Broken,
        (true, None) => config::Read::Missing,
        (false, None) => config::Read::Parsed(document.into_iter().collect()),
    };
    let edit = match level_edit {
        KeyEdit::Set(value) => config::Edit::Set((*key).to_string(), value),
        KeyEdit::Remove => config::Edit::Delete((*key).to_string()),
    };
    match config::rmw(read, edit) {
        Some(written) => Ok((written.into_iter().collect(), replaced)),
        None => Err(refused.unwrap_or_else(|| "the document was refused".to_string())),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use serde_json::json;

    fn object(value: Value) -> Map<String, Value> {
        match value {
            Value::Object(object) => object,
            Value::Null
            | Value::Bool(_)
            | Value::Number(_)
            | Value::String(_)
            | Value::Array(_) => {
                panic!("not an object")
            }
        }
    }

    /// The glue around the compiled core: each level of a path is read as
    /// missing, parsed or broken, and the document comes back in order.
    #[test]
    fn an_edit_reaches_the_core_at_each_level_of_its_path() {
        let document = json!({ "a": 1, "b": { "c": "x", "d": [1] }, "e": null, "f": "oops" });
        let set = |path: &[&str]| {
            edit_read(
                DocRead::Parsed(object(document.clone())),
                path,
                &KeyEdit::Set(json!(true)),
            )
            .map(|(written, replaced)| (Value::Object(written), replaced))
        };
        assert_eq!(
            (
                set(&["b", "c"]),
                set(&["e", "g"]),
                set(&["f", "g"]),
                edit_read(DocRead::Missing, &["x", "y"], &KeyEdit::Remove),
                edit_read(
                    DocRead::Broken("unparsed".to_string()),
                    &["a"],
                    &KeyEdit::Remove
                ),
            ),
            (
                Ok((
                    json!({ "a": 1, "b": { "c": true, "d": [1] }, "e": null, "f": "oops" }),
                    Some(json!("x"))
                )),
                Ok((
                    json!({ "a": 1, "b": { "c": "x", "d": [1] }, "e": { "g": true }, "f": "oops" }),
                    None
                )),
                Err("`f` is not an object, so `f.g` cannot be written".to_string()),
                Ok((Map::new(), None)),
                Err("unparsed".to_string()),
            )
        );
    }

    #[test]
    fn a_read_is_missing_parsed_or_broken() {
        assert_eq!(read_document(None), DocRead::Missing);
        assert_eq!(
            read_document(Some("{\"a\": 1}")),
            DocRead::Parsed(object(json!({ "a": 1 })))
        );
        assert_eq!(
            read_document(Some("[]")),
            DocRead::Broken("the document is not a JSON object".to_string())
        );
        assert_eq!(
            read_document(Some("{\"a\": 1,}")),
            DocRead::Broken("trailing comma at line 1 column 9".to_string())
        );
    }
}
