//! Charitable argument repair (omp ADR 0020): strict on a tool's contract,
//! charitable on the model's dialect. Before validation, a call's arguments
//! pass through the tool's declared [`ArgDialect`]: an alias key becomes its
//! canonical name, a string spelling of a declared boolean or number becomes
//! the value, and each repair is kept as a [`Repair`] that rides with the
//! call as a warning. A key of another dialect, an unknown key of a closed
//! schema, or two keys for one argument is a typed [`ArgumentError`] that
//! names the valid arguments.

use std::fmt;

use eukhe_types::pi_ai::{JsonObject as PiJsonObject, JsonValue as PiJsonValue, ToolSchema};
use serde::{Deserialize, Serialize};

use crate::harness::types::{ToolDiagnostic, ToolDiagnosticSeverity};

/// The diagnostic code of a repair.
pub const ARGUMENT_REPAIRED: &str = "argument_repaired";

/// Another name models use for an argument.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ArgAlias {
    pub alias: &'static str,
    pub canonical: &'static str,
}

/// A key of another tool's dialect this tool refuses, with the hint that
/// teaches its own.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RefusedArg {
    pub key: &'static str,
    pub hint: &'static str,
}

/// The dialect a tool declares: aliases it accepts and keys it refuses.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct ArgDialect {
    pub aliases: Vec<ArgAlias>,
    pub refused: Vec<RefusedArg>,
}

impl ArgDialect {
    /// Each of `aliases` read as `canonical`.
    #[must_use]
    pub fn alias(mut self, canonical: &'static str, aliases: &[&'static str]) -> Self {
        self.aliases
            .extend(aliases.iter().map(|&alias| ArgAlias { alias, canonical }));
        self
    }

    /// Each of `keys` refused with `hint`.
    #[must_use]
    pub fn refuse(mut self, keys: &[&'static str], hint: &'static str) -> Self {
        self.refused
            .extend(keys.iter().map(|&key| RefusedArg { key, hint }));
        self
    }
}

/// One applied repair.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "camelCase")]
pub enum Repair {
    /// `{ kind: "alias", from, to }`: a key read as its canonical name.
    Alias { from: String, to: String },
    /// `{ kind: "coercion", key, from, to }`: a string read as the value
    /// the schema declares.
    Coercion {
        key: String,
        from: String,
        to: PiJsonValue,
    },
}

impl fmt::Display for Repair {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Alias { from, to } => write!(formatter, "Repaired argument: {from} read as {to}"),
            Self::Coercion { key, from, to } => {
                write!(formatter, "Repaired argument: {key}={from:?} read as {to}")
            }
        }
    }
}

impl Repair {
    /// The warning the call's result carries.
    #[must_use]
    pub fn diagnostic(&self) -> ToolDiagnostic {
        ToolDiagnostic {
            severity: ToolDiagnosticSeverity::Warn,
            code: Some(ARGUMENT_REPAIRED.to_owned()),
            message: self.to_string(),
            omitted: None,
            artifact: None,
            lines: None,
        }
    }
}

/// Arguments in the tool's own dialect and the repairs that made them.
#[derive(Debug, Clone, PartialEq)]
pub struct Repaired {
    pub arguments: PiJsonObject,
    pub repairs: Vec<Repair>,
}

/// Arguments no repair can make valid; the message names the fix. Each is
/// retryable: the call changed nothing.
#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
pub enum ArgumentError {
    #[error("{tool} does not take `{key}`: {hint}")]
    Refused {
        tool: String,
        key: String,
        hint: &'static str,
    },
    #[error("{tool} has no argument `{key}`. Valid arguments: {}.", valid.join(", "))]
    Unknown {
        tool: String,
        key: String,
        valid: Vec<String>,
    },
    #[error("{tool} got `{canonical}` twice (as {}); send it once as `{canonical}`.", keys.join(" and "))]
    Ambiguous {
        tool: String,
        canonical: String,
        keys: Vec<String>,
    },
}

const TRUE: [&str; 4] = ["true", "yes", "on", "1"];
const FALSE: [&str; 4] = ["false", "no", "off", "0"];

/// The JSON Schema `type` of a declared property, when it is one name.
fn declared_type<'a>(properties: Option<&'a PiJsonObject>, key: &str) -> Option<&'a str> {
    properties?.get(key)?.get("type")?.as_str()
}

/// `text` as the value of a declared `boolean`, `integer`, or `number`.
fn coerce(kind: &str, text: &str) -> Option<PiJsonValue> {
    let trimmed = text.trim();
    match kind {
        "boolean" => {
            let lower = trimmed.to_ascii_lowercase();
            if TRUE.contains(&lower.as_str()) {
                Some(PiJsonValue::Bool(true))
            } else if FALSE.contains(&lower.as_str()) {
                Some(PiJsonValue::Bool(false))
            } else {
                None
            }
        }
        "integer" => trimmed.parse::<i64>().ok().map(PiJsonValue::from),
        "number" => trimmed
            .parse::<f64>()
            .ok()
            .and_then(serde_json::Number::from_f64)
            .map(PiJsonValue::Number),
        _ => None,
    }
}

/// `raw` in `tool`'s dialect: aliases renamed, declared scalars coerced from
/// strings, each repair recorded. Keys outside a closed schema
/// (`additionalProperties: false`) are rejected.
///
/// # Errors
///
/// [`ArgumentError`] for a refused, unknown, or doubled argument.
pub fn repair_arguments(
    tool: &str,
    parameters: &ToolSchema,
    dialect: &ArgDialect,
    raw: PiJsonObject,
) -> Result<Repaired, ArgumentError> {
    let schema = parameters.json();
    let properties = schema.get("properties").and_then(PiJsonValue::as_object);
    let closed = schema.get("additionalProperties") == Some(&PiJsonValue::Bool(false));
    let mut repairs = Vec::new();
    let mut sent_as: Vec<(String, String)> = Vec::with_capacity(raw.len());
    let mut arguments = PiJsonObject::new();
    for (key, value) in raw {
        if let Some(refused) = dialect.refused.iter().find(|refused| refused.key == key) {
            return Err(ArgumentError::Refused {
                tool: tool.to_owned(),
                key,
                hint: refused.hint,
            });
        }
        let declared = properties.is_some_and(|properties| properties.contains_key(&key));
        let canonical = match dialect.aliases.iter().find(|alias| alias.alias == key) {
            Some(alias) if !declared => alias.canonical.to_owned(),
            Some(_) | None => {
                if closed && !declared {
                    return Err(ArgumentError::Unknown {
                        tool: tool.to_owned(),
                        key,
                        valid: properties
                            .map(|properties| properties.keys().cloned().collect())
                            .unwrap_or_default(),
                    });
                }
                key.clone()
            }
        };
        if let Some((_, first)) = sent_as.iter().find(|(name, _)| *name == canonical) {
            return Err(ArgumentError::Ambiguous {
                tool: tool.to_owned(),
                keys: vec![format!("`{first}`"), format!("`{key}`")],
                canonical,
            });
        }
        if canonical != key {
            repairs.push(Repair::Alias {
                from: key.clone(),
                to: canonical.clone(),
            });
        }
        let value = match (&value, declared_type(properties, &canonical)) {
            (PiJsonValue::String(text), Some(kind)) => match coerce(kind, text) {
                Some(coerced) => {
                    repairs.push(Repair::Coercion {
                        key: canonical.clone(),
                        from: text.clone(),
                        to: coerced.clone(),
                    });
                    coerced
                }
                None => value,
            },
            _ => value,
        };
        sent_as.push((canonical.clone(), key));
        arguments.insert(canonical, value);
    }
    Ok(Repaired { arguments, repairs })
}

#[cfg(test)]
mod tests {
    use serde_json::json;

    use super::*;

    fn schema() -> ToolSchema {
        ToolSchema::from(json!({
            "type": "object",
            "properties": {
                "path": { "type": "string" },
                "case": { "type": "boolean" },
                "skip": { "type": "integer" },
            },
            "additionalProperties": false,
        }))
    }

    fn dialect() -> ArgDialect {
        ArgDialect::default()
            .alias("path", &["file_path"])
            .refuse(&["old_string"], "send a hashline patch")
    }

    fn object(value: PiJsonValue) -> PiJsonObject {
        let PiJsonValue::Object(object) = value else {
            panic!("arguments are an object");
        };
        object
    }

    #[test]
    fn renames_aliases_and_coerces_declared_scalars_with_receipts() {
        let repaired = repair_arguments(
            "grep",
            &schema(),
            &dialect(),
            object(json!({ "file_path": "a.rs", "case": "False", "skip": " 3 " })),
        )
        .unwrap();
        assert_eq!(
            repaired.arguments,
            object(json!({ "path": "a.rs", "case": false, "skip": 3 }))
        );
        let warnings: Vec<String> = repaired.repairs.iter().map(ToString::to_string).collect();
        assert_eq!(
            warnings,
            [
                "Repaired argument: file_path read as path",
                "Repaired argument: case=\"False\" read as false",
                "Repaired argument: skip=\" 3 \" read as 3",
            ]
        );
    }

    #[test]
    fn leaves_strings_that_are_not_the_declared_scalar_for_validation() {
        let repaired = repair_arguments(
            "grep",
            &schema(),
            &dialect(),
            object(json!({ "path": "true", "case": "maybe" })),
        )
        .unwrap();
        assert_eq!(
            repaired.arguments,
            object(json!({ "path": "true", "case": "maybe" }))
        );
        assert!(repaired.repairs.is_empty());
    }

    #[test]
    fn rejects_unknown_doubled_and_refused_keys_naming_the_fix() {
        let error = |raw| {
            repair_arguments("grep", &schema(), &dialect(), object(raw))
                .unwrap_err()
                .to_string()
        };
        assert_eq!(
            error(json!({ "pattern": "x" })),
            "grep has no argument `pattern`. Valid arguments: path, case, skip."
        );
        assert_eq!(
            error(json!({ "path": "a", "file_path": "b" })),
            "grep got `path` twice (as `path` and `file_path`); send it once as `path`."
        );
        assert_eq!(
            error(json!({ "old_string": "a" })),
            "grep does not take `old_string`: send a hashline patch"
        );
    }

    #[test]
    fn an_open_schema_keeps_unknown_keys() {
        let open = ToolSchema::from(json!({ "type": "object", "properties": {} }));
        let repaired = repair_arguments(
            "echo",
            &open,
            &ArgDialect::default(),
            object(json!({ "text": "hi" })),
        )
        .unwrap();
        assert_eq!(repaired.arguments, object(json!({ "text": "hi" })));
    }
}
