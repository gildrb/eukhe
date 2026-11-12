//! `searchTools()`, `describeTool()`, and `describeNamespace()` of code mode
//! scripts (pi-durable `codemode.ts` `CodemodeCall.discover`), answered from
//! the call's start data, so a replay sees what the first run saw.

use std::sync::Arc;

use eukhe_chord::json::{JsonObject, JsonValue};

use super::docs::{CodemodeStart, StartNamespace};
use super::identifier::to_codemode_identifier;
use crate::search::{rank_documents, SearchDocument};

const DEFAULT_SEARCH_LIMIT: usize = 8;

fn object(entries: impl IntoIterator<Item = (&'static str, JsonValue)>) -> JsonValue {
    let object: JsonObject = entries.into_iter().collect();
    JsonValue::Object(Arc::new(object))
}

fn matches_namespace(namespace: &StartNamespace, query: &str) -> bool {
    namespace.name == query
        || to_codemode_identifier(&namespace.name) == to_codemode_identifier(query)
}

/// Why a discovery global's arguments are refused; its Display is the
/// thrown error's message.
#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
pub(super) enum DiscoverError {
    #[error("describeTool() expects a tool name")]
    NoToolName,
    #[error("describeNamespace() expects a namespace name")]
    NoNamespaceName,
    #[error("searchTools() expects a query string")]
    NoQuery,
    #[error("searchTools() limit must be a positive integer")]
    BadLimit,
    #[error("searchTools() namespace must be a string")]
    NamespaceNotAString,
}

/// What discovery global `name` resolves to with the script's argument list
/// `args`; `Ok(None)` is `undefined`, `Err` the thrown error.
#[expect(
    clippy::too_many_lines,
    reason = "one ported upstream routine dispatching every discovery global"
)]
pub(super) fn discover(
    start: &CodemodeStart,
    name: &str,
    args: Option<&JsonValue>,
) -> Result<Option<JsonValue>, DiscoverError> {
    let args = args.and_then(JsonValue::as_array).unwrap_or_default();
    let argument = |index: usize| args.get(index);
    let tools: Vec<_> = start.tools.iter().filter(|tool| !tool.hidden).collect();
    let namespace_of_tool = |tool: &str| {
        start
            .namespaces
            .iter()
            .find(|namespace| namespace.tools.iter().any(|name| name == tool))
    };
    match name {
        "describeTool" => {
            let Some(name) = argument(0).and_then(JsonValue::as_str) else {
                return Err(DiscoverError::NoToolName);
            };
            Ok(tools
                .iter()
                .find(|tool| tool.name == name || tool.js_name == name)
                .map(|tool| JsonValue::from(tool.description.as_str())))
        }
        "describeNamespace" => {
            let Some(name) = argument(0).and_then(JsonValue::as_str) else {
                return Err(DiscoverError::NoNamespaceName);
            };
            let Some(namespace) = start
                .namespaces
                .iter()
                .find(|candidate| matches_namespace(candidate, name))
            else {
                return Ok(None);
            };
            let mut entries = vec![("name", JsonValue::from(namespace.name.as_str()))];
            if let Some(description) = &namespace.description {
                entries.push(("description", JsonValue::from(description.as_str())));
            }
            if let Some(instructions) = &namespace.instructions {
                entries.push(("instructions", JsonValue::from(instructions.as_str())));
            }
            entries.push((
                "tools",
                namespace
                    .tools
                    .iter()
                    .map(|tool| JsonValue::from(to_codemode_identifier(tool)))
                    .collect(),
            ));
            Ok(Some(object(entries)))
        }
        _ => {
            let Some(query) = argument(0).and_then(JsonValue::as_str) else {
                return Err(DiscoverError::NoQuery);
            };
            let options = argument(1);
            let limit = match options.and_then(|options| options.get("limit")) {
                None | Some(JsonValue::Null) => DEFAULT_SEARCH_LIMIT,
                Some(limit) => limit
                    .as_u64()
                    .filter(|limit| *limit > 0)
                    .and_then(|limit| usize::try_from(limit).ok())
                    .ok_or(DiscoverError::BadLimit)?,
            };
            let namespace = match options.and_then(|options| options.get("namespace")) {
                None | Some(JsonValue::Null) => None,
                Some(JsonValue::String(namespace)) => Some(namespace.as_ref()),
                Some(_) => return Err(DiscoverError::NamespaceNotAString),
            };
            let documents: Vec<SearchDocument> = tools
                .iter()
                .filter_map(|tool| {
                    let own = namespace_of_tool(&tool.name);
                    if let Some(namespace) = namespace {
                        if !own.is_some_and(|own| matches_namespace(own, namespace)) {
                            return None;
                        }
                    }
                    let text = [
                        tool.name.clone(),
                        tool.name.replace('_', " "),
                        tool.description.clone(),
                        own.map_or_default(|own| own.name.clone()),
                        own.and_then(|own| own.description.clone())
                            .unwrap_or_default(),
                    ]
                    .join(" ");
                    Some(SearchDocument {
                        name: tool.name.clone(),
                        text,
                    })
                })
                .collect();
            let found: Vec<JsonValue> = rank_documents(query, &documents, limit)
                .into_iter()
                .filter_map(|name| tools.iter().find(|tool| tool.name == name))
                .map(|tool| {
                    object([
                        ("name", JsonValue::from(tool.js_name.as_str())),
                        ("description", JsonValue::from(tool.description.as_str())),
                    ])
                })
                .collect();
            Ok(Some(JsonValue::from(found)))
        }
    }
}
