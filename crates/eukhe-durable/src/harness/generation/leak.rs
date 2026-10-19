//! Tool calls a model leaked into its visible text. Some models write a tool
//! call as markup in the text, not in the native tool-call channel. [`scan`]
//! finds this markup and rebuilds the calls. It reads five markup families
//! ([`Markup`]), one family for each omp in-band scanner
//! (`packages/ai/src/dialect/{hermes,qwen3,qwen-xml,kimi,deepseek}.ts`).
//! Markup in quoted code (a fence or an inline code span) is not a leak: the
//! model shows the markup in its answer (omp `utils/dsml-leak.ts`,
//! `QUOTED_CODE_PATTERN`). The scan is pure. It borrows the text until it
//! builds the result.

use eukhe_ai::utils::json_parse::parse_json_with_repair;
use eukhe_types::pi_ai::{JsonObject, JsonValue};

/// The open tag of a Hermes or Qwen3 call section.
const TOOL_CALL_OPEN: &str = "<tool_call>";
/// The close tag of a Hermes or Qwen3 call section.
const TOOL_CALL_CLOSE: &str = "</tool_call>";
/// The open tag of one Qwen3-Coder XML call.
const FUNCTION_OPEN: &str = "<function=";
/// The close tag of one Qwen3-Coder XML call.
const FUNCTION_CLOSE: &str = "</function>";
/// The open tag of one Qwen3-Coder XML argument.
const PARAMETER_OPEN: &str = "<parameter=";
/// The close tag of one Qwen3-Coder XML argument.
const PARAMETER_CLOSE: &str = "</parameter>";
/// The open tag of an omp "qwen" call section.
const TOOL_CALLS_OPEN: &str = "<tool_calls>";
/// The close tag of an omp "qwen" call section.
const TOOL_CALLS_CLOSE: &str = "</tool_calls>";
/// The token that opens a Kimi call section.
const KIMI_SECTION_BEGIN: &str = "<|tool_calls_section_begin|>";
/// The token that closes a Kimi call section.
const KIMI_SECTION_END: &str = "<|tool_calls_section_end|>";
/// The token that opens one Kimi call.
const KIMI_CALL_BEGIN: &str = "<|tool_call_begin|>";
/// The token that closes one Kimi call.
const KIMI_CALL_END: &str = "<|tool_call_end|>";
/// The token between the Kimi call id and its JSON arguments.
const KIMI_ARGUMENT_BEGIN: &str = "<|tool_call_argument_begin|>";
/// The two spellings of the DSML pipe: fullwidth (U+FF5C) and ASCII.
const DSML_PIPES: [char; 2] = ['｜', '|'];

/// The markup family a leaked call was written in.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Markup {
    /// Hermes, Qwen2.5 and Qwen3 JSON:
    /// `<tool_call>{"name": "x", "arguments": {...}}</tool_call>`.
    Hermes,
    /// Qwen3-Coder XML: `<tool_call><function=x><parameter=k>v</parameter>
    /// </function></tool_call>`.
    Qwen3,
    /// The omp "qwen" pattern: self-closing elements in a section,
    /// `<tool_calls><x k="v"/></tool_calls>`.
    QwenXml,
    /// Kimi section tokens: `<|tool_calls_section_begin|>` and
    /// `<|tool_call_begin|>functions.x:0<|tool_call_argument_begin|>{...}`.
    Kimi,
    /// `DeepSeek` DSML: `<｜DSML｜tool_calls><｜DSML｜invoke name="x">...`,
    /// with fullwidth or ASCII pipes.
    Dsml,
}

impl Markup {
    /// The name of the family: `hermes`, `qwen3`, `qwen-xml`, `kimi` or
    /// `dsml`.
    pub(crate) fn as_str(self) -> &'static str {
        match self {
            Self::Hermes => "hermes",
            Self::Qwen3 => "qwen3",
            Self::QwenXml => "qwen-xml",
            Self::Kimi => "kimi",
            Self::Dsml => "dsml",
        }
    }

    /// Reads one call section of this family. `body` starts after the open
    /// tag of the section. The calls of the section go to `calls` in text
    /// order. Returns the length of `body` up to the end of the close tag, or
    /// the reason the section does not parse.
    #[allow(clippy::too_many_lines)] // One arm per family, as omp has one scanner per dialect.
    fn section(self, body: &str, calls: &mut Vec<LeakedCall>) -> Result<usize, String> {
        match self {
            // omp dialect/hermes.ts:147-159 (`#parseCall`).
            Self::Hermes => {
                let close = body
                    .find(TOOL_CALL_CLOSE)
                    .ok_or("the <tool_call> section has no close tag")?;
                let JsonValue::Object(mut call) = parse_json_with_repair(body[..close].trim())
                    .map_err(|error| format!("the tool call is not valid JSON: {error}"))?
                else {
                    return Err("the tool call is not a JSON object".to_owned());
                };
                let Some(JsonValue::String(name)) = call.remove("name") else {
                    return Err("the tool call has no name".to_owned());
                };
                if name.is_empty() {
                    return Err("the tool call has no name".to_owned());
                }
                let arguments = match call
                    .remove("arguments")
                    .or_else(|| call.remove("parameters"))
                {
                    None => JsonObject::new(),
                    Some(JsonValue::Object(arguments)) => arguments,
                    Some(JsonValue::String(arguments)) => parse_object(&arguments)?,
                    Some(
                        JsonValue::Null
                        | JsonValue::Bool(_)
                        | JsonValue::Number(_)
                        | JsonValue::Array(_),
                    ) => return Err("the tool call arguments are not a JSON object".to_owned()),
                };
                calls.push(LeakedCall { name, arguments });
                Ok(close + TOOL_CALL_CLOSE.len())
            }
            // The Qwen3-Coder XML call format (the `qwen3coder` parser of vLLM).
            Self::Qwen3 => {
                let close = body
                    .find(TOOL_CALL_CLOSE)
                    .ok_or("the <tool_call> section has no close tag")?;
                let mut rest = body[..close].trim_start();
                while let Some(function) = rest.strip_prefix(FUNCTION_OPEN) {
                    let tag_end = function.find('>').ok_or("the <function=> tag has no end")?;
                    let name = function[..tag_end].trim();
                    if name.is_empty() {
                        return Err("the <function=> tag has no name".to_owned());
                    }
                    let function = &function[tag_end + 1..];
                    let function_end = function
                        .find(FUNCTION_CLOSE)
                        .ok_or_else(|| format!("the function {name} has no close tag"))?;
                    let mut parameters = &function[..function_end];
                    let mut arguments = JsonObject::new();
                    while let Some(start) = parameters.find(PARAMETER_OPEN) {
                        let parameter = &parameters[start + PARAMETER_OPEN.len()..];
                        let tag_end = parameter
                            .find('>')
                            .ok_or("the <parameter=> tag has no end")?;
                        let key = parameter[..tag_end].trim();
                        if key.is_empty() {
                            return Err("the <parameter=> tag has no name".to_owned());
                        }
                        let parameter = &parameter[tag_end + 1..];
                        let value_end = parameter
                            .find(PARAMETER_CLOSE)
                            .ok_or_else(|| format!("the parameter {key} has no close tag"))?;
                        let raw = &parameter[..value_end];
                        let raw = raw.strip_prefix('\n').unwrap_or(raw);
                        let raw = raw.strip_suffix('\n').unwrap_or(raw);
                        arguments.insert(key.to_owned(), json_or_string(raw));
                        parameters = &parameter[value_end + PARAMETER_CLOSE.len()..];
                    }
                    calls.push(LeakedCall {
                        name: name.to_owned(),
                        arguments,
                    });
                    rest = function[function_end + FUNCTION_CLOSE.len()..].trim_start();
                }
                Ok(close + TOOL_CALL_CLOSE.len())
            }
            // omp dialect/qwen-xml.ts:52-80 (`#drain`, `parseToolElement`).
            Self::QwenXml => {
                let close = body
                    .find(TOOL_CALLS_CLOSE)
                    .ok_or("the <tool_calls> section has no close tag")?;
                let mut section = &body[..close];
                while let Some(start) = section.find('<') {
                    let element = &section[start + 1..];
                    let Some(end) = element.find(['<', '>']) else {
                        break;
                    };
                    if element[end..].starts_with('<') {
                        section = &element[end..];
                        continue;
                    }
                    section = &element[end + 1..];
                    // omp skips an element that is not self-closing.
                    let Some(tag) = element[..end].strip_suffix('/') else {
                        continue;
                    };
                    let (name, mut attributes) = tag.split_at(name_len(tag));
                    if name.is_empty()
                        || !(attributes.is_empty() || attributes.starts_with(char::is_whitespace))
                    {
                        return Err("a <tool_calls> element has no tool name".to_owned());
                    }
                    let mut arguments = JsonObject::new();
                    attributes = attributes.trim();
                    while !attributes.is_empty() {
                        let malformed = || format!("the {name} element has a bad attribute");
                        let (key, rest) = attributes.split_at(name_len(attributes));
                        if key.is_empty() {
                            return Err(malformed());
                        }
                        let rest = rest
                            .trim_start()
                            .strip_prefix('=')
                            .ok_or_else(malformed)?
                            .trim_start();
                        let quote = rest
                            .chars()
                            .next()
                            .filter(|&quote| matches!(quote, '"' | '\''))
                            .ok_or_else(malformed)?;
                        let value = &rest[1..];
                        let value_end = value.find(quote).ok_or_else(malformed)?;
                        arguments.insert(
                            key.to_owned(),
                            JsonValue::String(value[..value_end].to_owned()),
                        );
                        attributes = value[value_end + 1..].trim_start();
                    }
                    calls.push(LeakedCall {
                        name: name.to_owned(),
                        arguments,
                    });
                }
                Ok(close + TOOL_CALLS_CLOSE.len())
            }
            // omp dialect/kimi.ts:155-222 (`#consumeSection`, `#consumeHeader`,
            // `#consumeArgs`) and dialect/coercion.ts:128-132
            // (`normalizeKimiFunctionName`).
            Self::Kimi => {
                let mut at = 0;
                loop {
                    let rest = &body[at..];
                    let section_end = rest.find(KIMI_SECTION_END);
                    let Some(call_start) = rest
                        .find(KIMI_CALL_BEGIN)
                        .filter(|call| section_end.is_none_or(|end| *call < end))
                    else {
                        let end =
                            section_end.ok_or("the Kimi tool-call section has no end token")?;
                        return Ok(at + end + KIMI_SECTION_END.len());
                    };
                    let header = &rest[call_start + KIMI_CALL_BEGIN.len()..];
                    let header_end = header
                        .find(KIMI_ARGUMENT_BEGIN)
                        .ok_or("a Kimi tool call has no argument token")?;
                    let id = header[..header_end].trim();
                    let before_index = id.split(':').next().unwrap_or(id);
                    let name = before_index
                        .rsplit('.')
                        .next()
                        .unwrap_or(before_index)
                        .trim();
                    if name.is_empty() {
                        return Err("a Kimi tool call has no name".to_owned());
                    }
                    let raw = &header[header_end + KIMI_ARGUMENT_BEGIN.len()..];
                    let raw_end = raw
                        .find(KIMI_CALL_END)
                        .ok_or_else(|| format!("the Kimi tool call {name} has no end token"))?;
                    calls.push(LeakedCall {
                        name: name.to_owned(),
                        arguments: parse_object(&raw[..raw_end])?,
                    });
                    at = body.len() - raw.len() + raw_end + KIMI_CALL_END.len();
                }
            }
            // omp dialect/deepseek.ts:651-757 (`#consumeDsmlSection`,
            // `#consumeDsmlInvoke`, `#consumeDsmlParam`), 851-863
            // (`#matchDsmlOpen`) and 897-906 (`coerceDsmlValue`).
            Self::Dsml => {
                let mut rest = body;
                loop {
                    rest = rest.trim_start();
                    if let Some(after) =
                        dsml_tag(rest, "</", "tool_calls").and_then(|tag| tag.strip_prefix('>'))
                    {
                        return Ok(body.len() - after.len());
                    }
                    let Some(invoke) = dsml_tag(rest, "<", "invoke") else {
                        let mut chars = rest.chars();
                        if chars.next().is_none() {
                            return Err("the DSML tool_calls section has no close tag".to_owned());
                        }
                        rest = chars.as_str();
                        continue;
                    };
                    let tag_end = invoke.find('>').ok_or("a DSML invoke tag has no end")?;
                    let name = attribute(&invoke[..tag_end], "name")
                        .filter(|name| !name.is_empty())
                        .ok_or("a DSML invoke has no name")?;
                    let mut arguments = JsonObject::new();
                    rest = &invoke[tag_end + 1..];
                    loop {
                        rest = rest.trim_start();
                        if let Some(after) =
                            dsml_tag(rest, "</", "invoke").and_then(|tag| tag.strip_prefix('>'))
                        {
                            rest = after;
                            break;
                        }
                        let Some(parameter) = dsml_tag(rest, "<", "parameter") else {
                            let mut chars = rest.chars();
                            if chars.next().is_none() {
                                return Err(format!("the DSML invoke {name} has no close tag"));
                            }
                            rest = chars.as_str();
                            continue;
                        };
                        let tag_end = parameter
                            .find('>')
                            .ok_or("a DSML parameter tag has no end")?;
                        let tag = &parameter[..tag_end];
                        let key = attribute(tag, "name")
                            .filter(|key| !key.is_empty())
                            .ok_or_else(|| format!("a parameter of {name} has no name"))?;
                        let value = &parameter[tag_end + 1..];
                        let (raw_end, after) = value
                            .match_indices("</")
                            .find_map(|(at, _)| {
                                dsml_tag(&value[at..], "</", "parameter")
                                    .and_then(|tag| tag.strip_prefix('>'))
                                    .map(|after| (at, after))
                            })
                            .ok_or_else(|| format!("the parameter {key} has no close tag"))?;
                        let raw = &value[..raw_end];
                        let value = if attribute(tag, "string") == Some("false") {
                            json_or_string(raw)
                        } else {
                            JsonValue::String(raw.to_owned())
                        };
                        arguments.insert(key.to_owned(), value);
                        rest = after;
                    }
                    calls.push(LeakedCall {
                        name: name.to_owned(),
                        arguments,
                    });
                }
            }
        }
    }
}

/// One rebuilt call.
#[derive(Clone, Debug, PartialEq)]
pub(crate) struct LeakedCall {
    /// The name of the tool.
    pub(crate) name: String,
    /// The arguments of the call.
    pub(crate) arguments: JsonObject,
}

/// What the scan found in a text.
#[derive(Clone, Debug, PartialEq)]
pub(crate) enum Leak {
    /// No tool-call markup.
    None,
    /// Every leaked call parsed: the calls in text order, and the text with
    /// each markup section removed (trimmed).
    Calls {
        /// The family of the markup.
        markup: Markup,
        /// The rebuilt calls, in text order.
        calls: Vec<LeakedCall>,
        /// The text without the markup sections, trimmed.
        text: String,
    },
    /// Markup was found but a call in it did not parse (unclosed section, bad
    /// JSON, no name): the markup family and a short reason.
    Broken {
        /// The family of the markup.
        markup: Markup,
        /// Why the call does not parse.
        reason: String,
    },
}

/// Finds tool calls that a model wrote as markup in `text`.
///
/// The scan reads the first markup family it finds. It ignores markup of
/// other families. It ignores markup in a code fence (```` ``` ```` or
/// `~~~`, to the close fence or the end of the text) and in an inline code
/// span. A section that is not closed, a call that has no name, arguments
/// that are not a JSON object, or a section that has no call give
/// [`Leak::Broken`].
pub(crate) fn scan(text: &str) -> Leak {
    let mut family = None;
    let mut calls = Vec::new();
    let mut kept = String::new();
    let mut copied = 0;
    let mut cursor = 0;
    while let Some(offset) = text[cursor..].find(['<', '`', '~']) {
        let at = cursor + offset;
        let rest = &text[at..];
        // omp utils/dsml-leak.ts:26 (`QUOTED_CODE_PATTERN`).
        if rest.starts_with("```") || rest.starts_with("~~~") {
            cursor = rest[3..]
                .find(&rest[..3])
                .map_or(text.len(), |end| at + 3 + end + 3);
            continue;
        }
        if let Some(span) = rest.strip_prefix('`') {
            cursor = match span.find(['`', '\n']) {
                Some(end) if span[end..].starts_with('`') => at + end + 2,
                Some(_) | None => at + 1,
            };
            continue;
        }
        let opened = if let Some(body) = rest.strip_prefix(TOOL_CALL_OPEN) {
            let markup = if body.trim_start().starts_with(FUNCTION_OPEN) {
                Markup::Qwen3
            } else {
                Markup::Hermes
            };
            Some((markup, TOOL_CALL_OPEN.len()))
        } else if rest.starts_with(TOOL_CALLS_OPEN) {
            Some((Markup::QwenXml, TOOL_CALLS_OPEN.len()))
        } else if rest.starts_with(KIMI_SECTION_BEGIN) {
            Some((Markup::Kimi, KIMI_SECTION_BEGIN.len()))
        } else if let Some(body) =
            dsml_tag(rest, "<", "tool_calls").and_then(|tag| tag.strip_prefix('>'))
        {
            Some((Markup::Dsml, rest.len() - body.len()))
        } else if dsml_tag(rest, "<", "invoke").is_some()
            || dsml_tag(rest, "<", "parameter").is_some()
        {
            // omp deepseek.ts:228-230 (`BARE_DSML_OPEN`): the tool_calls
            // wrapper is missing, so the section starts at this tag.
            Some((Markup::Dsml, 0))
        } else {
            None
        };
        let Some((markup, open_len)) = opened else {
            cursor = at + 1;
            continue;
        };
        if family.is_some_and(|family| family != markup) {
            cursor = at + open_len.max(1);
            continue;
        }
        family = Some(markup);
        let found = calls.len();
        let section_len = match markup.section(&rest[open_len..], &mut calls) {
            Ok(section_len) => section_len,
            Err(reason) => return Leak::Broken { markup, reason },
        };
        if calls.len() == found {
            return Leak::Broken {
                markup,
                reason: "the tool-call section has no call".to_owned(),
            };
        }
        kept.push_str(&text[copied..at]);
        copied = at + open_len + section_len;
        cursor = copied;
    }
    let Some(markup) = family else {
        return Leak::None;
    };
    kept.push_str(&text[copied..]);
    kept.truncate(kept.trim_end().len());
    kept.replace_range(..kept.len() - kept.trim_start().len(), "");
    Leak::Calls {
        markup,
        calls,
        text: kept,
    }
}

/// The text after a DSML tag start: `open` (`<` or `</`), a pipe, `DSML`, a
/// pipe and `kind`. Each pipe is fullwidth or ASCII.
fn dsml_tag<'a>(text: &'a str, open: &str, kind: &str) -> Option<&'a str> {
    text.strip_prefix(open)?
        .strip_prefix(DSML_PIPES)?
        .strip_prefix("DSML")?
        .strip_prefix(DSML_PIPES)?
        .strip_prefix(kind)
}

/// The value of the attribute `key="value"` in a tag. A whitespace comes
/// before the key (omp deepseek.ts:858-860).
fn attribute<'a>(tag: &'a str, key: &str) -> Option<&'a str> {
    tag.match_indices(key).find_map(|(at, _)| {
        if !tag[..at].ends_with(char::is_whitespace) {
            return None;
        }
        let value = tag[at + key.len()..].strip_prefix("=\"")?;
        value.find('"').map(|end| &value[..end])
    })
}

/// The byte length of the name at the start of `text`: a letter or `_`, then
/// letters, digits, `_`, `.` or `-` (omp qwen-xml.ts:6-7). Zero when `text`
/// does not start with a name.
fn name_len(text: &str) -> usize {
    if !text.starts_with(|first: char| first.is_ascii_alphabetic() || first == '_') {
        return 0;
    }
    text.find(|next: char| !(next.is_ascii_alphanumeric() || matches!(next, '_' | '.' | '-')))
        .unwrap_or(text.len())
}

/// Tool-call arguments as a JSON object. Empty text gives an empty object
/// (omp utils/tool-call-arguments.ts:5-13).
fn parse_object(raw: &str) -> Result<JsonObject, String> {
    let raw = raw.trim();
    if raw.is_empty() {
        return Ok(JsonObject::new());
    }
    match parse_json_with_repair(raw) {
        Ok(JsonValue::Object(arguments)) => Ok(arguments),
        Ok(
            JsonValue::Null
            | JsonValue::Bool(_)
            | JsonValue::Number(_)
            | JsonValue::String(_)
            | JsonValue::Array(_),
        ) => Err("the tool call arguments are not a JSON object".to_owned()),
        Err(error) => Err(format!(
            "the tool call arguments are not valid JSON: {error}"
        )),
    }
}

/// An argument value: the JSON value when `raw` parses as JSON, else `raw`
/// as a string (omp deepseek.ts:897-906).
fn json_or_string(raw: &str) -> JsonValue {
    let trimmed = raw.trim();
    if trimmed.is_empty() {
        return JsonValue::String(raw.to_owned());
    }
    parse_json_with_repair(trimmed).unwrap_or_else(|_| JsonValue::String(raw.to_owned()))
}

#[cfg(test)]
mod tests {
    use eukhe_ai::utils::json_parse::parse_json_with_repair;
    use eukhe_types::pi_ai::JsonValue;
    use serde_json::json;

    use super::{scan, Leak, LeakedCall, Markup};

    fn call(name: &str, arguments: JsonValue) -> LeakedCall {
        let JsonValue::Object(arguments) = arguments else {
            panic!("the test arguments must be a JSON object")
        };
        LeakedCall {
            name: name.to_owned(),
            arguments,
        }
    }

    fn broken(markup: Markup, reason: &str) -> Leak {
        Leak::Broken {
            markup,
            reason: reason.to_owned(),
        }
    }

    #[test]
    fn names_each_markup_family() {
        assert_eq!(
            [
                Markup::Hermes,
                Markup::Qwen3,
                Markup::QwenXml,
                Markup::Kimi,
                Markup::Dsml
            ]
            .map(Markup::as_str),
            ["hermes", "qwen3", "qwen-xml", "kimi", "dsml"]
        );
    }

    #[test]
    fn plain_text_is_no_leak() {
        assert_eq!(scan("If a < b and c > d, run `ls` ~ done."), Leak::None);
        assert_eq!(scan(""), Leak::None);
    }

    #[test]
    fn rebuilds_a_hermes_call_and_keeps_the_text_around_it() {
        let text = "Let me look.\n<tool_call>\n{\"name\": \"read\", \"arguments\": {\"path\": \"src/lib.rs\"}}\n</tool_call>\nThen I will edit it.";
        assert_eq!(
            scan(text),
            Leak::Calls {
                markup: Markup::Hermes,
                calls: vec![call("read", json!({"path": "src/lib.rs"}))],
                text: "Let me look.\n\nThen I will edit it.".to_owned(),
            }
        );
    }

    #[test]
    fn rebuilds_two_hermes_sections_with_string_arguments_and_parameters_key() {
        let text = concat!(
            r#"<tool_call>{"name": "bash", "arguments": "{\"command\": \"ls\"}"}</tool_call>"#,
            "\n",
            r#"<tool_call>{"name": "read", "parameters": {"path": "a.rs"}}</tool_call>"#,
        );
        assert_eq!(
            scan(text),
            Leak::Calls {
                markup: Markup::Hermes,
                calls: vec![
                    call("bash", json!({"command": "ls"})),
                    call("read", json!({"path": "a.rs"})),
                ],
                text: String::new(),
            }
        );
    }

    #[test]
    fn rebuilds_two_qwen3_xml_calls_in_one_section() {
        let text = "Checking.\n<tool_call>\n<function=bash>\n<parameter=command>\nls -la\n</parameter>\n<parameter=timeout>\n30\n</parameter>\n</function>\n<function=read>\n<parameter=path>\nsrc/main.rs\n</parameter>\n</function>\n</tool_call>";
        assert_eq!(
            scan(text),
            Leak::Calls {
                markup: Markup::Qwen3,
                calls: vec![
                    call("bash", json!({"command": "ls -la", "timeout": 30})),
                    call("read", json!({"path": "src/main.rs"})),
                ],
                text: "Checking.".to_owned(),
            }
        );
    }

    #[test]
    fn rebuilds_two_qwen_xml_elements_in_one_section() {
        let text =
            "<tool_calls><read path=\"a.rs\"/>\n<bash command='ls -la' />\n</tool_calls>Done.";
        assert_eq!(
            scan(text),
            Leak::Calls {
                markup: Markup::QwenXml,
                calls: vec![
                    call("read", json!({"path": "a.rs"})),
                    call("bash", json!({"command": "ls -la"})),
                ],
                text: "Done.".to_owned(),
            }
        );
    }

    #[test]
    fn rebuilds_two_kimi_calls_in_one_section() {
        let text = "I will read and list.\n<|tool_calls_section_begin|><|tool_call_begin|>functions.read:0<|tool_call_argument_begin|>{\"path\": \"a.rs\"}<|tool_call_end|><|tool_call_begin|>functions.bash:1<|tool_call_argument_begin|>{\"command\": \"ls\"}<|tool_call_end|><|tool_calls_section_end|>";
        assert_eq!(
            scan(text),
            Leak::Calls {
                markup: Markup::Kimi,
                calls: vec![
                    call("read", json!({"path": "a.rs"})),
                    call("bash", json!({"command": "ls"})),
                ],
                text: "I will read and list.".to_owned(),
            }
        );
    }

    #[test]
    fn rebuilds_a_dsml_call_with_fullwidth_pipes() {
        let text = "Run it.\n<｜DSML｜tool_calls>\n<｜DSML｜invoke name=\"bash\">\n<｜DSML｜parameter name=\"command\" string=\"true\">ls -la</｜DSML｜parameter>\n<｜DSML｜parameter name=\"timeout\" string=\"false\">30</｜DSML｜parameter>\n</｜DSML｜invoke>\n</｜DSML｜tool_calls>";
        assert_eq!(
            scan(text),
            Leak::Calls {
                markup: Markup::Dsml,
                calls: vec![call("bash", json!({"command": "ls -la", "timeout": 30}))],
                text: "Run it.".to_owned(),
            }
        );
    }

    #[test]
    fn rebuilds_two_dsml_calls_with_ascii_pipes() {
        // A parameter without `string` keeps its raw text, as in omp.
        let text = "<|DSML|tool_calls><|DSML|invoke name=\"read\"><|DSML|parameter name=\"path\">42</|DSML|parameter></|DSML|invoke><|DSML|invoke name=\"bash\"><|DSML|parameter name=\"command\" string=\"true\">ls</|DSML|parameter></|DSML|invoke></|DSML|tool_calls> Done.";
        assert_eq!(
            scan(text),
            Leak::Calls {
                markup: Markup::Dsml,
                calls: vec![
                    call("read", json!({"path": "42"})),
                    call("bash", json!({"command": "ls"})),
                ],
                text: "Done.".to_owned(),
            }
        );
    }

    #[test]
    fn ignores_markup_in_fences_and_code_spans() {
        let text = "Use this format:\n```\n<tool_call>{\"name\": \"bash\"}</tool_call>\n```\nand `<tool_calls>` too.";
        assert_eq!(scan(text), Leak::None);
        assert_eq!(scan("~~~\n<|tool_calls_section_begin|>"), Leak::None);
    }

    #[test]
    fn finds_a_leak_after_a_fence() {
        let text = "```\n<tool_call>{}</tool_call>\n```\n<tool_call>{\"name\": \"bash\", \"arguments\": {}}</tool_call>";
        assert_eq!(
            scan(text),
            Leak::Calls {
                markup: Markup::Hermes,
                calls: vec![call("bash", json!({}))],
                text: "```\n<tool_call>{}</tool_call>\n```".to_owned(),
            }
        );
    }

    #[test]
    fn scans_only_the_first_family() {
        let text = "<tool_call>{\"name\": \"a\", \"arguments\": {}}</tool_call> <|tool_calls_section_begin|>junk";
        assert_eq!(
            scan(text),
            Leak::Calls {
                markup: Markup::Hermes,
                calls: vec![call("a", json!({}))],
                text: "<|tool_calls_section_begin|>junk".to_owned(),
            }
        );
    }

    #[test]
    fn broken_hermes_calls() {
        // The relaxed dialect reads `{name: bash}` (an unquoted key and a
        // bareword), as omp does; an object with no close brace stays broken.
        let bad_json =
            parse_json_with_repair("{\"name\": \"bash\", \"arguments\": {}").unwrap_err();
        assert_eq!(
            [
                "<tool_call>{\"name\": \"bash\"",
                "<tool_call>{\"name\": \"bash\", \"arguments\": {}</tool_call>",
                "<tool_call>[1]</tool_call>",
                "<tool_call>{\"arguments\": {}}</tool_call>",
                "<tool_call>{\"name\": \"\"}</tool_call>",
                "<tool_call>{\"name\": \"bash\", \"arguments\": [1]}</tool_call>",
                "<tool_call>{\"name\": \"bash\", \"arguments\": \"[1]\"}</tool_call>",
            ]
            .map(scan),
            [
                broken(Markup::Hermes, "the <tool_call> section has no close tag"),
                broken(
                    Markup::Hermes,
                    &format!("the tool call is not valid JSON: {bad_json}")
                ),
                broken(Markup::Hermes, "the tool call is not a JSON object"),
                broken(Markup::Hermes, "the tool call has no name"),
                broken(Markup::Hermes, "the tool call has no name"),
                broken(
                    Markup::Hermes,
                    "the tool call arguments are not a JSON object"
                ),
                broken(
                    Markup::Hermes,
                    "the tool call arguments are not a JSON object"
                ),
            ]
        );
    }

    #[test]
    fn broken_qwen3_calls() {
        assert_eq!(
            [
                "<tool_call><function=bash><parameter=command>ls</parameter></function>",
                "<tool_call><function=bash><parameter=command>ls</parameter></tool_call>",
                "<tool_call><function=><parameter=a>1</parameter></function></tool_call>",
                "<tool_call><function=bash><parameter=command>ls</function></tool_call>",
            ]
            .map(scan),
            [
                broken(Markup::Qwen3, "the <tool_call> section has no close tag"),
                broken(Markup::Qwen3, "the function bash has no close tag"),
                broken(Markup::Qwen3, "the <function=> tag has no name"),
                broken(Markup::Qwen3, "the parameter command has no close tag"),
            ]
        );
    }

    #[test]
    fn broken_qwen_xml_sections() {
        assert_eq!(
            [
                "<tool_calls><read path=\"a\"/>",
                "<tool_calls></tool_calls>",
                "<tool_calls><9x a=\"b\"/></tool_calls>",
                "<tool_calls><read path=a/></tool_calls>",
            ]
            .map(scan),
            [
                broken(Markup::QwenXml, "the <tool_calls> section has no close tag"),
                broken(Markup::QwenXml, "the tool-call section has no call"),
                broken(Markup::QwenXml, "a <tool_calls> element has no tool name"),
                broken(Markup::QwenXml, "the read element has a bad attribute"),
            ]
        );
    }

    #[test]
    fn broken_kimi_sections() {
        assert_eq!(
            [
                "<|tool_calls_section_begin|><|tool_call_begin|>functions.read:0<|tool_call_argument_begin|>{}<|tool_call_end|>",
                "<|tool_calls_section_begin|><|tool_call_begin|>functions.read:0<|tool_calls_section_end|>",
                "<|tool_calls_section_begin|><|tool_call_begin|>functions.read:0<|tool_call_argument_begin|>{}",
                "<|tool_calls_section_begin|><|tool_call_begin|>functions.:0<|tool_call_argument_begin|>{}<|tool_call_end|><|tool_calls_section_end|>",
                "<|tool_calls_section_begin|><|tool_call_begin|>functions.read:0<|tool_call_argument_begin|>[1]<|tool_call_end|><|tool_calls_section_end|>",
                "<|tool_calls_section_begin|><|tool_calls_section_end|>",
            ]
            .map(scan),
            [
                broken(Markup::Kimi, "the Kimi tool-call section has no end token"),
                broken(Markup::Kimi, "a Kimi tool call has no argument token"),
                broken(Markup::Kimi, "the Kimi tool call read has no end token"),
                broken(Markup::Kimi, "a Kimi tool call has no name"),
                broken(Markup::Kimi, "the tool call arguments are not a JSON object"),
                broken(Markup::Kimi, "the tool-call section has no call"),
            ]
        );
    }

    #[test]
    fn broken_dsml_sections() {
        assert_eq!(
            [
                "<｜DSML｜tool_calls><｜DSML｜invoke></｜DSML｜invoke></｜DSML｜tool_calls>",
                "<|DSML|tool_calls><|DSML|invoke name=\"bash\"><|DSML|parameter name=\"command\">ls",
                "<|DSML|tool_calls><|DSML|invoke name=\"bash\"><|DSML|parameter>ls</|DSML|parameter></|DSML|invoke></|DSML|tool_calls>",
                "<|DSML|tool_calls><|DSML|invoke name=\"bash\">",
                "bash\n<｜DSML｜invoke name=\"bash\"><｜DSML｜parameter name=\"command\" string=\"true\">ls</｜DSML｜parameter></｜DSML｜invoke>",
                "<｜DSML｜tool_calls></｜DSML｜tool_calls>",
            ]
            .map(scan),
            [
                broken(Markup::Dsml, "a DSML invoke has no name"),
                broken(Markup::Dsml, "the parameter command has no close tag"),
                broken(Markup::Dsml, "a parameter of bash has no name"),
                broken(Markup::Dsml, "the DSML invoke bash has no close tag"),
                broken(Markup::Dsml, "the DSML tool_calls section has no close tag"),
                broken(Markup::Dsml, "the tool-call section has no call"),
            ]
        );
    }
}
