//! A tiny language server for the eukhe-lsp tests: stdio JSON-RPC, a toy
//! language (`fn NAME`, `struct NAME` with indented `fn` members), and
//! deterministic answers. Columns are UTF-16 code units.
//!
//! Arguments:
//! - `--crash`: exit before reading anything.
//! - `--delay-ms N`: publish diagnostics N ms late.
//! - `--pull`: serve pull diagnostics instead of publishing.
//! - `--check-on-save` (with `--pull`): like rust-analyzer, pull serves
//!   only the errors; each save runs a "check" (a work-done progress
//!   round) that publishes the warnings.

use std::collections::{BTreeMap, VecDeque};
use std::io::{BufRead, BufReader, Write};
use std::sync::{Arc, Mutex, PoisonError};
use std::time::Duration;

use serde_json::{json, Value};

type Out = Arc<Mutex<std::io::Stdout>>;

fn send(out: &Out, message: &Value) {
    let body = message.to_string();
    let mut out = out.lock().unwrap_or_else(PoisonError::into_inner);
    write!(out, "Content-Length: {}\r\n\r\n{body}", body.len()).expect("write stdout");
    out.flush().expect("flush stdout");
}

fn read(input: &mut impl BufRead) -> Option<Value> {
    let mut length = None;
    loop {
        let mut line = String::new();
        if input.read_line(&mut line).ok()? == 0 {
            return None;
        }
        let line = line.trim_end();
        if line.is_empty() {
            break;
        }
        if let Some(value) = line.strip_prefix("Content-Length: ") {
            length = value.parse::<usize>().ok();
        }
    }
    let mut body = vec![0; length?];
    input.read_exact(&mut body).ok()?;
    serde_json::from_slice(&body).ok()
}

fn utf16_len(text: &str) -> usize {
    text.chars().map(char::len_utf16).sum()
}

/// The char index of UTF-16 offset `units` in `line`.
fn char_index(line: &str, units: u64) -> usize {
    let mut seen = 0;
    for (index, character) in line.chars().enumerate() {
        if seen >= units {
            return index;
        }
        seen += character.len_utf16() as u64;
    }
    line.chars().count()
}

fn is_word(character: char) -> bool {
    character.is_alphanumeric() || character == '_'
}

/// UTF-16 start offsets of word-bounded `word` in `line`.
fn occurrences(line: &str, word: &str) -> Vec<usize> {
    let chars: Vec<char> = line.chars().collect();
    let needle: Vec<char> = word.chars().collect();
    let mut found = Vec::new();
    let mut index = 0;
    while index + needle.len() <= chars.len() {
        let bounded = (index == 0 || !is_word(chars[index - 1]))
            && chars
                .get(index + needle.len())
                .is_none_or(|next| !is_word(*next));
        if chars[index..index + needle.len()] == needle[..] && bounded {
            found.push(chars[..index].iter().map(|c| c.len_utf16()).sum());
            index += needle.len();
        } else {
            index += 1;
        }
    }
    found
}

fn range(line: impl Into<Value>, start: usize, end: usize) -> Value {
    let line = line.into();
    json!({ "start": { "line": line, "character": start }, "end": { "line": line, "character": end } })
}

struct Server {
    out: Out,
    documents: BTreeMap<String, (i64, String)>,
    backlog: VecDeque<Value>,
    next_id: u64,
    greeting: Value,
    delay: Option<Duration>,
    pull: bool,
    check_on_save: bool,
}

impl Server {
    fn diagnostics(text: &str) -> Vec<Value> {
        let mut diagnostics = Vec::new();
        for (number, line) in text.split('\n').enumerate() {
            for (needle, severity, message) in [
                ("ERROR", 1, "ERROR is not allowed"),
                ("WARN", 2, "WARN is discouraged"),
            ] {
                if let Some(at) = line.find(needle) {
                    let start = utf16_len(&line[..at]);
                    diagnostics.push(json!({
                        "range": range(number, start, start + needle.len()),
                        "severity": severity,
                        "source": "fake",
                        "code": "E1",
                        "message": format!("{message}\nfor further information visit https://example.invalid"),
                    }));
                }
            }
        }
        diagnostics
    }

    fn publish(&self, uri: &str) {
        if self.pull {
            return;
        }
        let Some((version, text)) = self.documents.get(uri) else {
            return;
        };
        let message = json!({
            "jsonrpc": "2.0",
            "method": "textDocument/publishDiagnostics",
            "params": { "uri": uri, "version": version, "diagnostics": Self::diagnostics(text) },
        });
        match self.delay {
            None => send(&self.out, &message),
            Some(delay) => {
                let out = Arc::clone(&self.out);
                std::thread::spawn(move || {
                    std::thread::sleep(delay);
                    send(&out, &message);
                });
            }
        }
    }

    fn word_at(&self, params: &Value) -> Option<(String, String)> {
        let uri = params.pointer("/textDocument/uri")?.as_str()?.to_owned();
        let line = params.pointer("/position/line")?.as_u64()?;
        let units = params.pointer("/position/character")?.as_u64()?;
        let text = &self.documents.get(&uri)?.1;
        let line = text.split('\n').nth(usize::try_from(line).ok()?)?;
        let chars: Vec<char> = line.chars().collect();
        let mut start = char_index(line, units);
        if start >= chars.len() || !is_word(chars[start]) {
            return None;
        }
        while start > 0 && is_word(chars[start - 1]) {
            start -= 1;
        }
        let word: String = chars[start..].iter().take_while(|c| is_word(**c)).collect();
        Some((uri, word))
    }

    /// Every word-bounded occurrence of `word` in the open documents.
    fn find(&self, word: &str, prefix: &str) -> Vec<Value> {
        let mut found = Vec::new();
        for (uri, (_, text)) in &self.documents {
            for (number, line) in text.split('\n').enumerate() {
                for start in occurrences(line, word) {
                    let before: String =
                        line.chars().take(char_index(line, start as u64)).collect();
                    if before.trim_end().ends_with(prefix.trim_end()) || prefix.is_empty() {
                        found.push(json!({ "uri": uri, "range": range(number, start, start + utf16_len(word)) }));
                    }
                }
            }
        }
        found
    }

    fn definition(&self, params: &Value) -> Option<Value> {
        let (_, word) = self.word_at(params)?;
        self.find(&word, "fn ").into_iter().next()
    }

    fn symbols(&self, uri: &str) -> Value {
        let Some((_, text)) = self.documents.get(uri) else {
            return Value::Null;
        };
        let mut symbols: Vec<Value> = Vec::new();
        for (number, line) in text.split('\n').enumerate() {
            let indented = line.starts_with("    ");
            let trimmed = line.trim_start();
            for (keyword, kind) in [("fn ", 12), ("struct ", 23)] {
                let Some(rest) = trimmed.strip_prefix(keyword) else {
                    continue;
                };
                let name: String = rest.chars().take_while(|c| is_word(*c)).collect();
                let start = utf16_len(&line[..line.len() - rest.len()]);
                let symbol = json!({
                    "name": name,
                    "kind": if indented { 6 } else { kind },
                    "range": range(number, 0, utf16_len(line)),
                    "selectionRange": range(number, start, start + utf16_len(&name)),
                    "children": [],
                });
                match symbols.last_mut() {
                    Some(parent) if indented => parent["children"]
                        .as_array_mut()
                        .expect("children")
                        .push(symbol),
                    _ => symbols.push(symbol),
                }
            }
        }
        Value::Array(symbols)
    }

    /// Send a request to the client and wait for its answer, keeping other
    /// messages for later.
    fn call_client(&mut self, input: &mut impl BufRead, method: &str, params: &Value) -> Value {
        self.next_id += 1;
        let id = format!("fake-{}", self.next_id);
        send(
            &self.out,
            &json!({ "jsonrpc": "2.0", "id": id, "method": method, "params": params }),
        );
        loop {
            let message = read(input).expect("client answer");
            if message.get("method").is_none() && message["id"] == json!(id) {
                return message.get("result").cloned().unwrap_or(Value::Null);
            }
            self.backlog.push_back(message);
        }
    }

    fn line_text(&self, uri: &str, line: u64) -> String {
        self.documents
            .get(uri)
            .and_then(|(_, text)| {
                text.split('\n')
                    .nth(usize::try_from(line).ok()?)
                    .map(str::to_owned)
            })
            .unwrap_or_default()
    }

    #[allow(clippy::too_many_lines)] // one arm per LSP method the fixture serves
    fn handle(&mut self, input: &mut impl BufRead, method: &str, params: &Value) -> Value {
        match method {
            "initialize" => {
                let mut capabilities = json!({
                    "positionEncoding": "utf-16",
                    "textDocumentSync": { "openClose": true, "change": 1, "save": true },
                    "definitionProvider": true,
                    "typeDefinitionProvider": true,
                    "implementationProvider": true,
                    "referencesProvider": true,
                    "hoverProvider": true,
                    "documentSymbolProvider": true,
                    "workspaceSymbolProvider": true,
                    "renameProvider": true,
                    "codeActionProvider": { "resolveProvider": true },
                    "executeCommandProvider": { "commands": ["fake.uppercase"] },
                });
                if self.pull {
                    capabilities["diagnosticProvider"] = json!({ "interFileDependencies": false, "workspaceDiagnostics": false });
                }
                json!({ "capabilities": capabilities })
            }
            "textDocument/definition" | "textDocument/implementation" => {
                self.definition(params).unwrap_or(Value::Null)
            }
            "textDocument/typeDefinition" => self.definition(params).map_or(Value::Null, |location| {
                json!([{ "targetUri": location["uri"], "targetRange": location["range"], "targetSelectionRange": location["range"] }])
            }),
            "textDocument/references" => self
                .word_at(params)
                .map_or(Value::Null, |(_, word)| Value::Array(self.find(&word, ""))),
            "textDocument/hover" => self.word_at(params).map_or(Value::Null, |(_, word)| {
                json!({ "contents": { "kind": "markdown", "value": format!("```fake\nfn {word}\n```\n{}", self.greeting) } })
            }),
            "textDocument/documentSymbol" => {
                let uri = params.pointer("/textDocument/uri").and_then(Value::as_str).unwrap_or_default().to_owned();
                self.symbols(&uri)
            }
            "workspace/symbol" => {
                let query = params["query"].as_str().unwrap_or_default().to_owned();
                let uris: Vec<String> = self.documents.keys().cloned().collect();
                let mut found = Vec::new();
                for uri in uris {
                    for (number, line) in self.documents[&uri].1.split('\n').enumerate() {
                        if let Some(rest) = line.trim_start().strip_prefix("fn ") {
                            let name: String = rest.chars().take_while(|c| is_word(*c)).collect();
                            if name.contains(&query) {
                                let start = utf16_len(&line[..line.len() - rest.len()]);
                                found.push(json!({
                                    "name": name,
                                    "kind": 12,
                                    "location": { "uri": uri, "range": range(number, start, start + utf16_len(&name)) },
                                }));
                            }
                        }
                    }
                }
                found.push(json!({ "name": "unresolved", "kind": 12, "location": { "uri": "file:///nowhere" } }));
                Value::Array(found)
            }
            "textDocument/rename" => {
                let Some((_, word)) = self.word_at(params) else {
                    return Value::Null;
                };
                let new_name = params["newName"].as_str().unwrap_or_default();
                let mut changes: BTreeMap<String, Vec<Value>> = BTreeMap::new();
                for location in self.find(&word, "") {
                    changes
                        .entry(location["uri"].as_str().unwrap_or_default().to_owned())
                        .or_default()
                        .push(json!({ "range": location["range"], "newText": new_name }));
                }
                json!({
                    "documentChanges": changes
                        .into_iter()
                        .map(|(uri, edits)| json!({ "textDocument": { "uri": uri, "version": null }, "edits": edits }))
                        .collect::<Vec<_>>(),
                })
            }
            "textDocument/codeAction" => {
                let uri = params.pointer("/textDocument/uri").and_then(Value::as_str).unwrap_or_default().to_owned();
                let line = params.pointer("/range/start/line").and_then(Value::as_u64).unwrap_or_default();
                let text = self.line_text(&uri, line);
                let mut actions = Vec::new();
                if let Some(at) = text.find("ERROR") {
                    let start = utf16_len(&text[..at]);
                    actions.push(json!({
                        "title": "Replace ERROR with OK",
                        "kind": "quickfix",
                        "isPreferred": true,
                        "diagnostics": params.pointer("/context/diagnostics").cloned().unwrap_or(Value::Null),
                        "edit": { "changes": { uri.clone(): [{ "range": range(line, start, start + 5), "newText": "OK" }] } },
                    }));
                }
                actions.push(json!({
                    "title": "Uppercase line",
                    "kind": "refactor",
                    "command": { "title": "Uppercase line", "command": "fake.uppercase", "arguments": [uri, line] },
                }));
                actions.push(json!({ "title": "Append marker", "kind": "refactor", "data": { "uri": uri, "line": line } }));
                Value::Array(actions)
            }
            "codeAction/resolve" => {
                let uri = params.pointer("/data/uri").and_then(Value::as_str).unwrap_or_default().to_owned();
                let line = params.pointer("/data/line").and_then(Value::as_u64).unwrap_or_default();
                let end = utf16_len(&self.line_text(&uri, line));
                let mut resolved = params.clone();
                resolved["edit"] = json!({ "changes": { uri: [{ "range": range(line, end, end), "newText": " // marker" }] } });
                resolved
            }
            "workspace/executeCommand" => {
                let arguments = params["arguments"].as_array().cloned().unwrap_or_default();
                let uri = arguments.first().and_then(Value::as_str).unwrap_or_default().to_owned();
                let line = arguments.get(1).and_then(Value::as_u64).unwrap_or_default();
                let text = self.line_text(&uri, line);
                let edit = json!({ "changes": { uri: [{ "range": range(line, 0, utf16_len(&text)), "newText": text.to_uppercase() }] } });
                let applied = self.call_client(input, "workspace/applyEdit", &json!({ "edit": edit }));
                json!({ "applied": applied })
            }
            "textDocument/diagnostic" => {
                let uri = params.pointer("/textDocument/uri").and_then(Value::as_str).unwrap_or_default();
                let text = self.documents.get(uri).map(|(_, text)| text.as_str()).unwrap_or_default();
                let mut items = Self::diagnostics(text);
                if self.check_on_save {
                    items.retain(|item| item["severity"] == 1);
                }
                json!({ "kind": "full", "items": items })
            }
            _ => Value::Null,
        }
    }

    fn notify(&mut self, input: &mut impl BufRead, method: &str, params: &Value) {
        match method {
            "initialized" => {
                let settings = self.call_client(
                    input,
                    "workspace/configuration",
                    &json!({ "items": [{ "section": "fake.greeting" }] }),
                );
                self.greeting = settings.get(0).cloned().unwrap_or(Value::Null);
                self.call_client(
                    input,
                    "window/workDoneProgress/create",
                    &json!({ "token": "index" }),
                );
                send(
                    &self.out,
                    &json!({ "jsonrpc": "2.0", "method": "$/progress", "params": { "token": "index", "value": { "kind": "begin", "title": "indexing" } } }),
                );
                send(
                    &self.out,
                    &json!({ "jsonrpc": "2.0", "method": "$/progress", "params": { "token": "index", "value": { "kind": "end" } } }),
                );
            }
            "textDocument/didOpen" => {
                let document = &params["textDocument"];
                let uri = document["uri"].as_str().unwrap_or_default().to_owned();
                self.documents.insert(
                    uri.clone(),
                    (
                        document["version"].as_i64().unwrap_or_default(),
                        document["text"].as_str().unwrap_or_default().to_owned(),
                    ),
                );
                self.publish(&uri);
            }
            "textDocument/didChange" => {
                let uri = params
                    .pointer("/textDocument/uri")
                    .and_then(Value::as_str)
                    .unwrap_or_default()
                    .to_owned();
                let version = params
                    .pointer("/textDocument/version")
                    .and_then(Value::as_i64)
                    .unwrap_or_default();
                let text = params
                    .pointer("/contentChanges/0/text")
                    .and_then(Value::as_str)
                    .unwrap_or_default()
                    .to_owned();
                self.documents.insert(uri.clone(), (version, text));
                self.publish(&uri);
            }
            "textDocument/didSave" if self.check_on_save => {
                let uri = params
                    .pointer("/textDocument/uri")
                    .and_then(Value::as_str)
                    .unwrap_or_default();
                let Some((version, text)) = self.documents.get(uri) else {
                    return;
                };
                let mut warnings = Self::diagnostics(text);
                warnings.retain(|item| item["severity"] == 2);
                let progress = |kind: &str| json!({ "jsonrpc": "2.0", "method": "$/progress", "params": { "token": "check", "value": { "kind": kind, "title": "check" } } });
                let (begin, end) = (progress("begin"), progress("end"));
                let publish = json!({
                    "jsonrpc": "2.0",
                    "method": "textDocument/publishDiagnostics",
                    "params": { "uri": uri, "version": version, "diagnostics": warnings },
                });
                let out = Arc::clone(&self.out);
                std::thread::spawn(move || {
                    std::thread::sleep(Duration::from_millis(50));
                    send(&out, &begin);
                    std::thread::sleep(Duration::from_millis(100));
                    send(&out, &publish);
                    send(&out, &end);
                });
            }
            "exit" => std::process::exit(0),
            _ => {}
        }
    }
}

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    if args.iter().any(|arg| arg == "--crash") {
        std::process::exit(3);
    }
    let mut input = BufReader::new(std::io::stdin().lock());
    let mut server = Server {
        out: Arc::new(Mutex::new(std::io::stdout())),
        documents: BTreeMap::new(),
        backlog: VecDeque::new(),
        next_id: 0,
        greeting: Value::Null,
        delay: args
            .iter()
            .position(|arg| arg == "--delay-ms")
            .and_then(|at| args.get(at + 1)?.parse().ok())
            .map(Duration::from_millis),
        pull: args.iter().any(|arg| arg == "--pull"),
        check_on_save: args.iter().any(|arg| arg == "--check-on-save"),
    };
    loop {
        let message = match server.backlog.pop_front() {
            Some(message) => message,
            None => match read(&mut input) {
                Some(message) => message,
                None => return,
            },
        };
        let Some(method) = message
            .get("method")
            .and_then(Value::as_str)
            .map(str::to_owned)
        else {
            continue;
        };
        let params = message.get("params").cloned().unwrap_or(Value::Null);
        match message.get("id").cloned() {
            Some(id) => {
                let result = server.handle(&mut input, &method, &params);
                send(
                    &server.out,
                    &json!({ "jsonrpc": "2.0", "id": id, "result": result }),
                );
            }
            None => server.notify(&mut input, &method, &params),
        }
    }
}
