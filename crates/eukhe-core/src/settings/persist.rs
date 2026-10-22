//! The read/modify/write of one settings document
//! (`LAWS.bend` section `config` `rmw_refuses_broken`, `rmw_keeps_others`,
//! `settings_save_preserves`): a write reads the document on disk under
//! its lock, changes only its own key paths, and writes the result. A
//! document that cannot be read or parsed is never written.

use std::fmt;

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

/// Apply `edit` at `path` of `document` and return the value it replaced.
/// A missing (or `null`) parent becomes an object; every other key keeps
/// its value and its place.
///
/// # Errors
///
/// A parent on `path` that holds a value which is not an object (the
/// edit cannot apply without dropping that value).
pub(crate) fn edit_path(
    document: &mut Map<String, Value>,
    path: &[&str],
    edit: KeyEdit,
) -> Result<Option<Value>, String> {
    let Some((last, parents)) = path.split_last() else {
        return Err("an empty key path".to_string());
    };
    let mut node = document;
    for (depth, key) in parents.iter().enumerate() {
        let slot = match edit {
            KeyEdit::Set(_) => node
                .entry((*key).to_string())
                .or_insert_with(|| Value::Object(Map::new())),
            KeyEdit::Remove => match node.get_mut(*key) {
                Some(slot) => slot,
                None => return Ok(None),
            },
        };
        if slot.is_null() {
            match edit {
                KeyEdit::Set(_) => *slot = Value::Object(Map::new()),
                KeyEdit::Remove => return Ok(None),
            }
        }
        node = match slot {
            Value::Object(object) => object,
            Value::Null
            | Value::Bool(_)
            | Value::Number(_)
            | Value::String(_)
            | Value::Array(_) => {
                return Err(format!(
                    "`{}` is not an object, so `{}` cannot be written",
                    parents[..=depth].join("."),
                    path.join(".")
                ));
            }
        };
    }
    Ok(match edit {
        KeyEdit::Set(value) => node.insert((*last).to_string(), value),
        KeyEdit::Remove => node.shift_remove(*last),
    })
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

    #[test]
    fn a_set_changes_only_its_path() {
        let mut document = object(json!({ "a": 1, "b": { "c": "x", "d": [1] }, "e": null }));
        let before = edit_path(&mut document, &["b", "c"], KeyEdit::Set(json!("y")));
        assert_eq!(before, Ok(Some(json!("x"))));
        let created = edit_path(&mut document, &["e", "f"], KeyEdit::Set(json!(true)));
        assert_eq!(created, Ok(None));
        assert_eq!(
            Value::Object(document),
            json!({ "a": 1, "b": { "c": "y", "d": [1] }, "e": { "f": true } })
        );
    }

    #[test]
    fn a_remove_keeps_the_order_of_the_rest() {
        let mut document = object(json!({ "a": 1, "b": 2, "c": 3 }));
        assert_eq!(
            edit_path(&mut document, &["a"], KeyEdit::Remove),
            Ok(Some(json!(1)))
        );
        assert_eq!(
            edit_path(&mut document, &["x", "y"], KeyEdit::Remove),
            Ok(None)
        );
        assert_eq!(
            document.keys().cloned().collect::<Vec<_>>(),
            vec!["b".to_string(), "c".to_string()]
        );
    }

    #[test]
    fn a_parent_that_is_not_an_object_refuses() {
        let mut document = object(json!({ "mcpServers": "oops" }));
        assert_eq!(
            edit_path(&mut document, &["mcpServers", "x"], KeyEdit::Set(json!({}))),
            Err("`mcpServers` is not an object, so `mcpServers.x` cannot be written".to_string())
        );
        assert_eq!(Value::Object(document), json!({ "mcpServers": "oops" }));
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
