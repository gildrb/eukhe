//! Charitable argument repair (omp ADR 0020): strict on a tool's contract,
//! charitable on the model's dialect. Before validation, a call's arguments
//! pass through the tool's declared [`ArgDialect`]: a JSON-encoded key
//! (`"\"path\""`) and an alias key become the canonical name, and a value in
//! another spelling of its declared type becomes that type (a string of a
//! boolean, number, object or array; a lone string for an array of strings;
//! a number or boolean for a string). Each repair is kept as a [`Repair`]
//! that rides with the call as a warning. Arguments that are not JSON, a key
//! of another dialect, an unknown key of a closed schema, or two keys for one
//! argument is a typed [`ArgumentError`] that names the fix.
//!
//! The decisions run as the compiled Bend core (`eukhe_bend::rules::
//! arg_repair`, `bend/arg_repair.bend`, laws `laws/arg_repair.bend`): this
//! module decodes the JSON (the key's JSON string layers, a string's f64
//! and container readings) and turns the core's answer into the repaired
//! arguments and their receipts.

use std::fmt;

use eukhe_ai::utils::json_parse::{
    json_parse, parse_json_with_repair, PARSE_ERROR_KEY, RAW_JSON_KEY,
};
use eukhe_bend::rules::arg_repair::{
    self, Arg, Container, Prop, Reading, Record, Refusal, Verdict,
};
use eukhe_bend::wire::WireError;
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
    /// `{ kind: "alias", from, to }`: a key read as its canonical name (an
    /// alias, or a key in a JSON string).
    Alias { from: String, to: String },
    /// `{ kind: "coercion", key, from, to }`: a value read as the value the
    /// schema declares.
    Coercion {
        key: String,
        from: PiJsonValue,
        to: PiJsonValue,
    },
}

impl fmt::Display for Repair {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Alias { from, to } => write!(formatter, "Repaired argument: {from} read as {to}"),
            Self::Coercion { key, from, to } => {
                write!(formatter, "Repaired argument: {key}={from} read as {to}")
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

impl From<Record> for Repair {
    fn from(record: Record) -> Self {
        match record {
            Record::Alias { from, to } => Self::Alias { from, to },
            Record::Coercion { key, from, to } => Self::Coercion { key, from, to },
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
    /// The provider's argument text did not parse (omp `validation.ts`
    /// `__parseError`): the error and the text, bounded, so the model sees
    /// what it sent.
    #[error("{tool} got arguments that are not valid JSON. Send one JSON object.\nParse error: {error}\nRaw JSON:\n{raw}")]
    NotJson {
        tool: String,
        error: String,
        raw: String,
    },
    /// A key, name or hint longer than the compiled core reads: nothing was
    /// decided.
    #[error("{tool} got arguments too large to read: {error}")]
    TooLarge { tool: String, error: WireError },
    #[error("{tool} does not take `{key}`: {hint}")]
    Refused {
        tool: String,
        key: String,
        hint: String,
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

/// Layers of JSON string encoding removed from one key (omp
/// `MAX_KEY_DECODE_DEPTH`).
const MAX_KEY_DECODE_DEPTH: usize = 3;

/// `key` with its JSON string encoding removed (`"\"path\""` is `path`),
/// at most [`MAX_KEY_DECODE_DEPTH`] layers; `None` when no layer decodes.
fn plain_key(key: &str) -> Option<String> {
    let mut plain: Option<String> = None;
    for _ in 0..MAX_KEY_DECODE_DEPTH {
        let current = plain.as_deref().unwrap_or(key);
        if current.len() < 2 || !current.starts_with('"') || !current.ends_with('"') {
            break;
        }
        let Ok(PiJsonValue::String(inner)) = json_parse(current) else {
            break;
        };
        plain = Some(inner);
    }
    plain
}

/// What a string value's trimmed text reads as (omp `validation.ts`
/// `tryCoerceForExpectedTypes`): its f64, and the container it spells when
/// it opens with a bracket. Any other value reads as nothing.
fn reading(value: &PiJsonValue) -> Reading {
    let PiJsonValue::String(text) = value else {
        return Reading::default();
    };
    let trimmed = text.trim();
    let container = if trimmed.starts_with('{') {
        Container::Brace(match parse_json_with_repair(trimmed) {
            Ok(PiJsonValue::Object(object)) => Some(object),
            Ok(_) | Err(_) => None,
        })
    } else if trimmed.starts_with('[') {
        Container::Bracket(match parse_json_with_repair(trimmed) {
            Ok(PiJsonValue::Array(array)) => Some(array),
            Ok(_) | Err(_) => None,
        })
    } else {
        Container::Plain
    };
    Reading {
        number: trimmed
            .parse::<f64>()
            .ok()
            .and_then(serde_json::Number::from_f64)
            .map(PiJsonValue::Number),
        container,
    }
}

/// `raw` in `tool`'s dialect: JSON-encoded keys decoded, aliases renamed,
/// values in another spelling of their declared type coerced, each repair
/// recorded. Keys outside a closed schema (`additionalProperties: false`)
/// are rejected.
///
/// # Errors
///
/// [`ArgumentError`] for arguments that are not JSON (the
/// `__parseError` object of `parse_tool_call_arguments`), for a refused,
/// unknown, or doubled argument, and for a key too long to read.
pub fn repair_arguments(
    tool: &str,
    parameters: &ToolSchema,
    dialect: &ArgDialect,
    raw: PiJsonObject,
) -> Result<Repaired, ArgumentError> {
    if let Some(PiJsonValue::String(error)) = raw.get(PARSE_ERROR_KEY) {
        let text = raw.get(RAW_JSON_KEY).and_then(PiJsonValue::as_str);
        return Err(ArgumentError::NotJson {
            tool: tool.to_owned(),
            error: error.clone(),
            raw: text.unwrap_or_default().to_owned(),
        });
    }
    let schema = parameters.json();
    let none = PiJsonObject::new();
    let properties = schema
        .get("properties")
        .and_then(PiJsonValue::as_object)
        .unwrap_or(&none);
    let args = raw
        .into_iter()
        .map(|(key, value)| Arg {
            plain: plain_key(&key),
            reading: reading(&value),
            key,
            value,
        })
        .collect();
    let verdict = arg_repair::repair(
        arg_repair::Schema {
            props: properties.iter().map(|(name, declared)| Prop {
                name,
                kind: declared.get("type").and_then(PiJsonValue::as_str),
                items: declared
                    .get("items")
                    .and_then(|items| items.get("type"))
                    .and_then(PiJsonValue::as_str),
            }),
            closed: schema.get("additionalProperties") == Some(&PiJsonValue::Bool(false)),
        },
        arg_repair::Dialect {
            aliases: dialect
                .aliases
                .iter()
                .map(|alias| (alias.alias, alias.canonical)),
            refused: dialect
                .refused
                .iter()
                .map(|refused| (refused.key, refused.hint)),
        },
        args,
    )
    .map_err(|error| ArgumentError::TooLarge {
        tool: tool.to_owned(),
        error,
    })?;
    let tool = tool.to_owned();
    match verdict {
        Verdict::Repaired { arguments, records } => Ok(Repaired {
            arguments,
            repairs: records.into_iter().map(Repair::from).collect(),
        }),
        Verdict::Rejected(Refusal::Refused { key, hint }) => {
            Err(ArgumentError::Refused { tool, key, hint })
        }
        Verdict::Rejected(Refusal::Unknown { key, valid }) => {
            Err(ArgumentError::Unknown { tool, key, valid })
        }
        Verdict::Rejected(Refusal::Ambiguous {
            canonical,
            first,
            key,
        }) => Err(ArgumentError::Ambiguous {
            tool,
            canonical,
            keys: vec![format!("`{first}`"), format!("`{key}`")],
        }),
    }
}

#[cfg(test)]
mod tests {
    use eukhe_ai::utils::json_parse::parse_tool_call_arguments;
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

    #[test]
    fn reads_containers_lone_strings_and_scalars_as_their_declared_type_with_receipts() {
        let schema = ToolSchema::from(json!({
            "type": "object",
            "properties": {
                "path": { "type": "string" },
                "paths": { "type": "array", "items": { "type": "string" } },
                "edits": { "type": "array", "items": { "type": "object" } },
                "options": { "type": "object" },
                "lines": { "type": "array", "items": { "type": "integer" } },
                "ranges": { "type": "array", "items": { "type": "integer" } },
                "title": { "type": "string" },
            },
            "additionalProperties": false,
        }));
        let repaired = repair_arguments(
            "edit",
            &schema,
            &ArgDialect::default(),
            object(json!({
                "path": 42,
                "paths": "src/a.rs",
                "edits": "[{\"line\": 1}]",
                "options": " {'dry': True} ",
                "lines": "[1,",
                "ranges": "7",
                "title": false,
            })),
        )
        .unwrap();
        let coercion = |key: &str, from: PiJsonValue, to: PiJsonValue| Repair::Coercion {
            key: key.to_owned(),
            from,
            to,
        };
        assert_eq!(
            repaired,
            Repaired {
                arguments: object(json!({
                    "path": "42",
                    "paths": ["src/a.rs"],
                    "edits": [{ "line": 1 }],
                    "options": { "dry": true },
                    "lines": "[1,",
                    "ranges": "7",
                    "title": "false",
                })),
                repairs: vec![
                    coercion("path", json!(42), json!("42")),
                    coercion("paths", json!("src/a.rs"), json!(["src/a.rs"])),
                    coercion("edits", json!("[{\"line\": 1}]"), json!([{ "line": 1 }])),
                    coercion("options", json!(" {'dry': True} "), json!({ "dry": true })),
                    coercion("title", json!(false), json!("false")),
                ],
            }
        );
        assert_eq!(
            repaired.repairs[0].to_string(),
            "Repaired argument: path=42 read as \"42\""
        );
    }

    #[test]
    fn decodes_json_encoded_keys_unless_the_plain_key_is_sent_too() {
        let repaired = repair_arguments(
            "grep",
            &schema(),
            &dialect(),
            object(json!({ "\"\\\"file_path\\\"\"": "a.rs", "\"case\"": "yes" })),
        )
        .unwrap();
        let alias = |from: &str, to: &str| Repair::Alias {
            from: from.to_owned(),
            to: to.to_owned(),
        };
        assert_eq!(
            repaired,
            Repaired {
                arguments: object(json!({ "path": "a.rs", "case": true })),
                repairs: vec![
                    alias("\"\\\"file_path\\\"\"", "file_path"),
                    alias("file_path", "path"),
                    alias("\"case\"", "case"),
                    Repair::Coercion {
                        key: "case".to_owned(),
                        from: json!("yes"),
                        to: json!(true),
                    },
                ],
            }
        );
        assert_eq!(
            repair_arguments(
                "grep",
                &schema(),
                &dialect(),
                object(json!({ "\"path\"": "a", "path": "b" })),
            ),
            Err(ArgumentError::Unknown {
                tool: "grep".to_owned(),
                key: "\"path\"".to_owned(),
                valid: vec!["path".to_owned(), "case".to_owned(), "skip".to_owned()],
            })
        );
    }

    #[test]
    fn arguments_that_are_not_json_name_the_parse_error_and_the_raw_text() {
        let raw = parse_tool_call_arguments(Some(r#"{"path": "a.rs""#));
        let error = repair_arguments("grep", &schema(), &dialect(), raw).unwrap_err();
        assert_eq!(
            error,
            ArgumentError::NotJson {
                tool: "grep".to_owned(),
                error: "Expected ',' or '}' after property value in JSON at position 15 (line 1 column 16)"
                    .to_owned(),
                raw: r#"{"path": "a.rs""#.to_owned(),
            }
        );
        assert_eq!(
            error.to_string(),
            "grep got arguments that are not valid JSON. Send one JSON object.\n\
             Parse error: Expected ',' or '}' after property value in JSON at position 15 (line 1 column 16)\n\
             Raw JSON:\n\
             {\"path\": \"a.rs\""
        );
    }
}
