//! Stored tool calls replayed in the current dialect (omp² "version
//! everything the model sees"). Each tool result's details carry its
//! call's stamp, `version: "family@rev"`. When the context orders a
//! transcript's tool results ([`super::context::order_tool_results`]), every
//! stamped call goes through the lift table of the compiled core
//! (`eukhe_bend::rules::call_lift`, laws `laws/call_lift.bend`), so a model
//! request, and every resume, fork or model switch that builds one, sends
//! each call in its family's current dialect.
//!
//! A lifted call takes the arguments the core places (each stored value
//! moved to its name, added ones parsed from the table's JSON); its
//! result's `version` becomes the current stamp, and the result's details
//! record `lift`: the stamp it was lifted from, `outcome: "lifted"` and the
//! receipts. A call no step lifts (`stranded`), or one whose placed
//! arguments cannot be built (`refused`, with the reason), is replayed as
//! stored with that `lift` receipt. Unstamped calls, unknown families and
//! current calls are untouched. Only the derived view changes: the stored
//! entries keep what was stored.

use eukhe_bend::rules::call_lift::{self, Arg, Lift, Receipt, StoredCall};
use eukhe_types::pi_ai::{AssistantContentBlock, JsonObject, JsonValue, Message};
use serde_json::json;

/// Where one stamped call and its result sit in the ordered messages.
struct Site {
    assistant: usize,
    block: usize,
    result: usize,
}

/// Why the arguments a lift placed could not be built.
#[derive(Debug, thiserror::Error)]
enum PlaceError {
    /// The transcript holds no call where the lift's call was read.
    #[error("the lifted call is not where the transcript held it")]
    NoCall,
    /// A kept argument names no stored argument, or one placed already.
    #[error("the lift placed stored argument {0}, which is missing or placed twice")]
    Stored(usize),
    /// A stored argument was not placed.
    #[error("the lift dropped stored argument {0}")]
    Dropped(usize),
    /// Two placed arguments share a name.
    #[error("the lift placed two arguments named `{0}`")]
    Twice(String),
    /// An added argument's value is not JSON.
    #[error("the lift added `{key}` with a value that is not JSON: {source}")]
    Added {
        key: String,
        source: serde_json::Error,
    },
}

/// Lift every stamped call of `messages`, ordered as
/// [`super::context::order_tool_results`] leaves them: each assistant
/// message followed by its tool results in call order.
pub(crate) fn lift_calls(messages: &mut [Message]) {
    let mut sites = Vec::new();
    let mut stored = Vec::new();
    for (index, message) in messages.iter().enumerate() {
        let Message::Assistant(assistant) = message else {
            continue;
        };
        let mut result = index + 1;
        for (block, content) in assistant.content.iter().enumerate() {
            let AssistantContentBlock::ToolCall(tool_call) = content else {
                continue;
            };
            let at = result;
            result += 1;
            let Some(Message::ToolResult(tool_result)) = messages.get(at) else {
                continue;
            };
            if tool_result.tool_call_id != tool_call.id {
                continue;
            }
            let Some((family, rev)) = stamp(tool_result.details.as_ref()) else {
                continue;
            };
            sites.push(Site {
                assistant: index,
                block,
                result: at,
            });
            stored.push(StoredCall {
                family,
                rev,
                keys: tool_call.arguments.keys().map(String::as_str).collect(),
            });
        }
    }
    if sites.is_empty() {
        return;
    }
    let lifts = call_lift::lift(&stored);
    drop(stored);
    for (site, lift) in sites.into_iter().zip(lifts) {
        apply(messages, &site, lift);
    }
}

/// The family and rev of a result's stamp.
fn stamp(details: Option<&JsonValue>) -> Option<(&str, &str)> {
    details?.get("version")?.as_str()?.rsplit_once('@')
}

fn apply(messages: &mut [Message], site: &Site, lift: Lift) {
    let (receipt, rev) = match lift {
        Lift::Unknown | Lift::Current => return,
        Lift::Stranded => (json!({ "outcome": "stranded" }), None),
        Lift::Lifted {
            rev,
            args,
            receipts,
        } => match lift_arguments(messages, site, args) {
            Ok(()) => {
                let receipts: Vec<JsonValue> = receipts.iter().map(receipt_json).collect();
                (
                    json!({ "outcome": "lifted", "receipts": receipts }),
                    Some(rev),
                )
            }
            Err(error) => {
                tracing::warn!(%error, "a stored tool call is replayed as stored");
                (
                    json!({ "outcome": "refused", "reason": error.to_string() }),
                    None,
                )
            }
        },
    };
    record(messages, site, receipt, rev.as_deref());
}

/// The call at `site` with the arguments the lift placed.
fn lift_arguments(messages: &mut [Message], site: &Site, args: Vec<Arg>) -> Result<(), PlaceError> {
    let tool_call = match messages.get_mut(site.assistant) {
        Some(Message::Assistant(assistant)) => match assistant.content.get_mut(site.block) {
            Some(AssistantContentBlock::ToolCall(tool_call)) => tool_call,
            Some(AssistantContentBlock::Text(_) | AssistantContentBlock::Thinking(_)) | None => {
                return Err(PlaceError::NoCall);
            }
        },
        Some(Message::System(_) | Message::User(_) | Message::ToolResult(_)) | None => {
            return Err(PlaceError::NoCall);
        }
    };
    tool_call.arguments = place(&tool_call.arguments, args)?;
    Ok(())
}

/// The `lift` receipt in the result's details, after the stamp it was
/// lifted from; a lifted call's result is stamped with the current `rev`.
fn record(messages: &mut [Message], site: &Site, receipt: JsonValue, rev: Option<&str>) {
    let Some(details) = details_mut(messages, site) else {
        return;
    };
    let Some(from) = details.get("version").and_then(JsonValue::as_str) else {
        return;
    };
    let from = from.to_owned();
    if let (Some(rev), Some((family, _))) = (rev, from.rsplit_once('@')) {
        details.insert("version".to_owned(), format!("{family}@{rev}").into());
    }
    let mut lift = JsonObject::new();
    lift.insert("from".to_owned(), from.into());
    if let JsonValue::Object(receipt) = receipt {
        lift.extend(receipt);
    }
    details.insert("lift".to_owned(), lift.into());
}

fn receipt_json(receipt: &Receipt) -> JsonValue {
    match receipt {
        Receipt::Renamed { from, to } => json!({ "kind": "renamed", "from": from, "to": to }),
        Receipt::Clashed { from, to } => json!({ "kind": "clashed", "from": from, "to": to }),
        Receipt::Filled { key } => json!({ "kind": "filled", "key": key }),
    }
}

fn details_mut<'a>(messages: &'a mut [Message], site: &Site) -> Option<&'a mut JsonObject> {
    match messages.get_mut(site.result)? {
        Message::ToolResult(result) => match result.details.as_mut()? {
            JsonValue::Object(details) => Some(details),
            JsonValue::Null
            | JsonValue::Bool(_)
            | JsonValue::Number(_)
            | JsonValue::String(_)
            | JsonValue::Array(_) => None,
        },
        Message::System(_) | Message::User(_) | Message::Assistant(_) => None,
    }
}

/// The arguments a lift placed: each kept one the stored value at its
/// index under its (new) name, each added one its parsed value.
fn place(stored: &JsonObject, args: Vec<Arg>) -> Result<JsonObject, PlaceError> {
    let mut values: Vec<Option<&JsonValue>> = stored.values().map(Some).collect();
    let mut placed = JsonObject::new();
    for arg in args {
        let (key, value) = match arg {
            Arg::Kept { index, key } => {
                let value = values
                    .get_mut(index)
                    .and_then(Option::take)
                    .ok_or(PlaceError::Stored(index))?;
                (key, value.clone())
            }
            Arg::Added { key, json } => match serde_json::from_str(&json) {
                Ok(value) => (key, value),
                Err(source) => return Err(PlaceError::Added { key, source }),
            },
        };
        if placed.contains_key(&key) {
            return Err(PlaceError::Twice(key));
        }
        placed.insert(key, value);
    }
    match values.iter().position(Option::is_some) {
        Some(index) => Err(PlaceError::Dropped(index)),
        None => Ok(placed),
    }
}

#[cfg(test)]
mod tests;
