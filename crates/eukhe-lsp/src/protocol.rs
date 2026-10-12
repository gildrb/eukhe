//! The subset of LSP message types eukhe exchanges with servers.

use std::collections::BTreeMap;

use serde::{Deserialize, Serialize};
use serde_json::Value;
use url::Url;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) struct Position {
    pub(crate) line: u32,
    pub(crate) character: u32,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) struct Range {
    pub(crate) start: Position,
    pub(crate) end: Position,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) struct Location {
    pub(crate) uri: Url,
    pub(crate) range: Range,
}

#[derive(Debug, Clone, PartialEq, Eq, Deserialize)]
#[serde(rename_all = "camelCase")]
pub(crate) struct LocationLink {
    pub(crate) target_uri: Url,
    pub(crate) target_selection_range: Range,
}

/// `Location | Location[] | LocationLink[]` (`null` is the `Option` around
/// it).
#[derive(Debug, Clone, Deserialize)]
#[serde(untagged)]
pub(crate) enum LocationResponse {
    One(Location),
    Many(Vec<Location>),
    Links(Vec<LocationLink>),
}

impl LocationResponse {
    pub(crate) fn into_locations(self) -> Vec<Location> {
        match self {
            Self::One(location) => vec![location],
            Self::Many(locations) => locations,
            Self::Links(links) => links
                .into_iter()
                .map(|link| Location {
                    uri: link.target_uri,
                    range: link.target_selection_range,
                })
                .collect(),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(untagged)]
pub(crate) enum NumberOrString {
    Number(i64),
    String(String),
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub(crate) struct Diagnostic {
    pub(crate) range: Range,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub(crate) severity: Option<u8>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub(crate) code: Option<NumberOrString>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub(crate) source: Option<String>,
    pub(crate) message: String,
}

#[derive(Debug, Clone, Deserialize)]
pub(crate) struct PublishDiagnosticsParams {
    pub(crate) uri: Url,
    #[serde(default)]
    pub(crate) version: Option<i32>,
    pub(crate) diagnostics: Vec<Diagnostic>,
}

/// `textDocument/diagnostic` report; only `full` reports carry items.
#[derive(Debug, Clone, Deserialize)]
#[serde(tag = "kind", rename_all = "camelCase")]
pub(crate) enum DocumentDiagnosticReport {
    Full { items: Vec<Diagnostic> },
    Unchanged {},
}

#[derive(Debug, Clone, Deserialize)]
pub(crate) struct Hover {
    pub(crate) contents: HoverContents,
}

#[derive(Debug, Clone, Deserialize)]
#[serde(untagged)]
pub(crate) enum MarkedString {
    Plain(String),
    Code { language: String, value: String },
}

/// `MarkedString | MarkedString[] | MarkupContent`; the order matters for
/// the untagged parse: a `MarkupContent` object has no `language`.
#[derive(Debug, Clone, Deserialize)]
#[serde(untagged)]
pub(crate) enum HoverContents {
    One(MarkedString),
    Many(Vec<MarkedString>),
    Markup { value: String },
}

impl HoverContents {
    pub(crate) fn into_text(self) -> String {
        fn marked(value: MarkedString) -> String {
            match value {
                MarkedString::Plain(text) => text,
                MarkedString::Code { language, value } => format!("```{language}\n{value}\n```"),
            }
        }
        match self {
            Self::Markup { value, .. } => value,
            Self::One(value) => marked(value),
            Self::Many(values) => values
                .into_iter()
                .map(marked)
                .collect::<Vec<_>>()
                .join("\n\n"),
        }
    }
}

#[derive(Debug, Clone, Deserialize)]
#[serde(rename_all = "camelCase")]
pub(crate) struct DocumentSymbol {
    pub(crate) name: String,
    pub(crate) kind: u32,
    pub(crate) selection_range: Range,
    #[serde(default)]
    pub(crate) children: Vec<DocumentSymbol>,
}

#[derive(Debug, Clone, Deserialize)]
#[serde(rename_all = "camelCase")]
pub(crate) struct SymbolInformation {
    pub(crate) name: String,
    pub(crate) kind: u32,
    pub(crate) location: Location,
    #[serde(default)]
    pub(crate) container_name: Option<String>,
}

/// `DocumentSymbol[] | SymbolInformation[]`.
#[derive(Debug, Clone, Deserialize)]
#[serde(untagged)]
pub(crate) enum DocumentSymbolResponse {
    Nested(Vec<DocumentSymbol>),
    Flat(Vec<SymbolInformation>),
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub(crate) struct TextEdit {
    pub(crate) range: Range,
    pub(crate) new_text: String,
}

#[derive(Debug, Clone, Deserialize)]
pub(crate) struct VersionedDocument {
    pub(crate) uri: Url,
}

#[derive(Debug, Clone, Deserialize)]
#[serde(rename_all = "camelCase")]
pub(crate) struct TextDocumentEdit {
    pub(crate) text_document: VersionedDocument,
    pub(crate) edits: Vec<TextEdit>,
}

/// A `documentChanges` entry. Resource operations are not advertised
/// (`resourceOperations: []`), so a server sends text document edits only.
#[derive(Debug, Clone, Default, Deserialize)]
#[serde(rename_all = "camelCase")]
pub(crate) struct WorkspaceEdit {
    #[serde(default)]
    pub(crate) changes: Option<BTreeMap<Url, Vec<TextEdit>>>,
    #[serde(default)]
    pub(crate) document_changes: Option<Vec<TextDocumentEdit>>,
}

impl WorkspaceEdit {
    /// The edits by document, `documentChanges` taking precedence over
    /// `changes` (LSP rule), in server order.
    pub(crate) fn by_document(self) -> Vec<(Url, Vec<TextEdit>)> {
        match (self.document_changes, self.changes) {
            (Some(changes), _) => changes
                .into_iter()
                .map(|change| (change.text_document.uri, change.edits))
                .collect(),
            (None, Some(changes)) => changes.into_iter().collect(),
            (None, None) => Vec::new(),
        }
    }
}

#[derive(Debug, Clone, Serialize, Deserialize)]
#[allow(clippy::struct_field_names)] // LSP `Command.command`
pub(crate) struct Command {
    pub(crate) title: String,
    pub(crate) command: String,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub(crate) arguments: Option<Vec<Value>>,
}

#[derive(Debug, Clone, Deserialize)]
#[serde(rename_all = "camelCase")]
pub(crate) struct CodeAction {
    pub(crate) title: String,
    #[serde(default)]
    pub(crate) kind: Option<String>,
    #[serde(default)]
    pub(crate) is_preferred: bool,
    #[serde(default)]
    pub(crate) edit: Option<WorkspaceEdit>,
    #[serde(default)]
    pub(crate) command: Option<Command>,
}

/// `(Command | CodeAction)[]` entry: a bare command has a string
/// `command`, an action's `command` is an object.
#[derive(Debug, Clone, Deserialize)]
#[serde(untagged)]
pub(crate) enum CodeActionEntry {
    Action(CodeAction),
    Command(Command),
}

/// The server capabilities eukhe consults.
#[derive(Debug, Clone, Default, Deserialize)]
#[serde(rename_all = "camelCase")]
pub(crate) struct ServerCapabilities {
    #[serde(default)]
    pub(crate) position_encoding: Option<String>,
    #[serde(default)]
    pub(crate) text_document_sync: Option<TextDocumentSync>,
    #[serde(default)]
    pub(crate) definition_provider: Option<Value>,
    #[serde(default)]
    pub(crate) type_definition_provider: Option<Value>,
    #[serde(default)]
    pub(crate) implementation_provider: Option<Value>,
    #[serde(default)]
    pub(crate) references_provider: Option<Value>,
    #[serde(default)]
    pub(crate) hover_provider: Option<Value>,
    #[serde(default)]
    pub(crate) document_symbol_provider: Option<Value>,
    #[serde(default)]
    pub(crate) workspace_symbol_provider: Option<Value>,
    #[serde(default)]
    pub(crate) rename_provider: Option<Value>,
    #[serde(default)]
    pub(crate) code_action_provider: Option<Value>,
    #[serde(default)]
    pub(crate) diagnostic_provider: Option<Value>,
}

/// `TextDocumentSyncKind | TextDocumentSyncOptions`.
#[derive(Debug, Clone, Deserialize)]
#[serde(untagged)]
pub(crate) enum TextDocumentSync {
    Kind(u8),
    Options(TextDocumentSyncOptions),
}

#[derive(Debug, Clone, Default, Deserialize)]
#[serde(rename_all = "camelCase")]
pub(crate) struct TextDocumentSyncOptions {
    #[serde(default)]
    pub(crate) change: Option<u8>,
    #[serde(default)]
    pub(crate) save: Option<Value>,
}

/// Whether a `*Provider` capability is on (`true` or an options object).
pub(crate) fn enabled(capability: Option<&Value>) -> bool {
    capability.is_some_and(|value| !matches!(value, Value::Null | Value::Bool(false)))
}

/// LSP `SymbolKind` (1-26) as a `snake_case` name.
pub(crate) fn symbol_kind_name(kind: u32) -> String {
    const NAMES: [&str; 26] = [
        "file",
        "module",
        "namespace",
        "package",
        "class",
        "method",
        "property",
        "field",
        "constructor",
        "enum",
        "interface",
        "function",
        "variable",
        "constant",
        "string",
        "number",
        "boolean",
        "array",
        "object",
        "key",
        "null",
        "enum_member",
        "struct",
        "event",
        "operator",
        "type_parameter",
    ];
    kind.checked_sub(1)
        .and_then(|index| NAMES.get(index as usize))
        .map_or_else(|| format!("kind_{kind}"), |name| (*name).to_owned())
}
