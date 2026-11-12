//! Python-side preview analysis: the python half of
//! `packages/coding-agent/src/core/tools/code-preview.ts`.
//!
//! Covers `previewPythonCode`/`previewIpythonCode` and their statement
//! scanner. Split from the bash-side preview module for module-size
//! hygiene; behavior matches the TS source.

use super::bash::{
    descriptor, js_trim, js_trim_end, path_tail, preview_bash_command, simplify_bash_command_line,
    CodePreview,
};
use super::cell::parse_ipython_bash_cell;
use super::shapes::PreviewShape;
use crate::text_shapes::{first_of, TextShape};

fn python_indent(line: &str) -> usize {
    PreviewShape::Indent
        .find(line)
        .map_or(0, |m| m.as_str().chars().count())
}

fn python_call_pattern(inner: &str) -> bool {
    PreviewShape::Call.is_match(inner)
}

fn python_low_signal_call_pattern(inner: &str) -> bool {
    PreviewShape::LowCall.is_match(inner)
}

fn python_print_inner_call(line: &str) -> Option<String> {
    let trimmed = js_trim(line);
    let inner = PreviewShape::PrintCall
        .captures(trimmed)
        .and_then(|c| c.get(1).map(|m| js_trim(m).to_string()));
    inner.filter(|inner| python_call_pattern(inner))
}

fn python_path_vars(lines: &[String]) -> std::collections::HashMap<String, String> {
    let mut vars = std::collections::HashMap::new();
    for line in lines {
        let m = first_of(
            &[PreviewShape::PathAssign, PreviewShape::StringAssign],
            line,
        );
        if let Some((_, c)) = m {
            let name = c.get(1).map(str::to_string);
            let value = c.get(3).map(str::to_string);
            if let (Some(name), Some(value)) = (name, value) {
                if value.contains('/') {
                    vars.insert(name, value);
                }
            }
        }
    }
    vars
}

fn python_file_operation(
    line: &str,
    paths: &std::collections::HashMap<String, String>,
) -> Option<String> {
    let m = PreviewShape::FileOp.captures(js_trim(line))?;
    let name = m.get(1)?;
    let method = m.get(2)?;
    let path = paths.get(name)?;
    let action = match method {
        "write_text" | "write_bytes" => "write",
        "read_text" | "read_bytes" => "read",
        "mkdir" => "mkdir",
        "unlink" => "delete",
        "rename" => "rename",
        "replace" => "replace",
        "touch" => "touch",
        other => other,
    };
    Some(format!("{action} {}", path_tail(path)))
}

fn python_subprocess_command(line: &str) -> Option<String> {
    let trimmed = js_trim(line);
    if let Some(c) = PreviewShape::SubprocessString.captures(trimmed) {
        return c.get(2).map(simplify_bash_command_line);
    }
    if let Some(c) = PreviewShape::SubprocessList.captures(trimmed) {
        let inner = c.get(1)?;
        let words: Vec<String> = PreviewShape::Quoted
            .captures_iter(inner)
            .into_iter()
            .filter_map(|c| c.get(1).map(str::to_string))
            .collect();
        return Some(simplify_bash_command_line(&words.join(" ")));
    }
    None
}

fn simplify_python_preview_line(
    line: &str,
    paths: &std::collections::HashMap<String, String>,
) -> String {
    python_file_operation(line, paths)
        .or_else(|| python_subprocess_command(line))
        .or_else(|| python_print_inner_call(line))
        .unwrap_or_else(|| js_trim(line).to_string())
}

fn python_preview_line(
    lines: &[String],
    index: usize,
    paths: &std::collections::HashMap<String, String>,
) -> String {
    let line = lines.get(index).map_or("", String::as_str);
    if index > 0 && PreviewShape::DefLine.is_match(line) {
        let previous = lines.get(index - 1).map_or("", String::as_str);
        if PreviewShape::Decorator.is_match(js_trim(previous)) {
            return format!("{} {}", js_trim(previous), js_trim(line));
        }
    }
    if PreviewShape::Compound.is_match(line) {
        if let Some(child_index) = first_python_child_line(lines, index) {
            let head = PreviewShape::ColonEnd.replace(js_trim(line), ":");
            let child = lines.get(child_index).cloned().unwrap_or_default();
            return format!("{head} {}", simplify_python_preview_line(&child, paths));
        }
    }
    simplify_python_preview_line(line, paths)
}

fn first_python_child_line(lines: &[String], parent_index: usize) -> Option<usize> {
    let parent_line = lines.get(parent_index).cloned().unwrap_or_default();
    let parent_indent = python_indent(&parent_line);
    for (i, line) in lines.iter().enumerate().skip(parent_index + 1) {
        let trimmed = js_trim(line);
        if trimmed.is_empty()
            || first_of(
                &[
                    PreviewShape::Comment,
                    PreviewShape::ImportLine,
                    PreviewShape::Decorator,
                ],
                trimmed,
            )
            .is_some()
        {
            continue;
        }
        if python_indent(line) <= parent_indent {
            return None;
        }
        return Some(i);
    }
    None
}

/// The signal score of line `index`, given `later`: the scores of the lines
/// after it (a compound statement takes its first child's).
fn python_line_score(
    lines: &[String],
    index: usize,
    paths: &std::collections::HashMap<String, String>,
    later: &[i64],
) -> i64 {
    let line = lines.get(index).cloned().unwrap_or_default();
    let trimmed = js_trim(&line);
    if trimmed.is_empty()
        || first_of(
            &[
                PreviewShape::Comment,
                PreviewShape::ImportLine,
                PreviewShape::Decorator,
                PreviewShape::Closers,
            ],
            trimmed,
        )
        .is_some()
    {
        return -1;
    }
    if python_file_operation(&line, paths).is_some() {
        return 95;
    }
    // A line is a subprocess command exactly when one of the two subprocess
    // shapes fits it (`python_subprocess_command` then always answers).
    if first_of(
        &[PreviewShape::SubprocessString, PreviewShape::SubprocessList],
        trimmed,
    )
    .is_some()
    {
        return 90;
    }
    let lead = first_of(
        &[
            PreviewShape::MainGuard,
            PreviewShape::MethodCall,
            PreviewShape::Compound,
            PreviewShape::DefLine,
            PreviewShape::ValueAssign,
        ],
        &line,
    )
    .map(|(shape, _)| shape);
    if lead == Some(PreviewShape::MainGuard) {
        return 70;
    }
    if lead == Some(PreviewShape::MethodCall) {
        return 80;
    }
    if lead == Some(PreviewShape::Compound) {
        return match first_python_child_line(lines, index) {
            None => 20,
            Some(child_index) => (later[child_index] - 5).max(20),
        };
    }
    if lead == Some(PreviewShape::DefLine) {
        return 50;
    }
    if lead == Some(PreviewShape::ValueAssign) {
        return 25;
    }
    let print_inner_call = python_print_inner_call(&line);
    let is_low_signal_call = print_inner_call
        .as_deref()
        .is_some_and(python_low_signal_call_pattern);
    if print_inner_call.is_some() && !is_low_signal_call {
        return 55;
    }
    let call =
        first_of(&[PreviewShape::CallAssign, PreviewShape::Call], &line).map(|(shape, _)| shape);
    if call == Some(PreviewShape::CallAssign) {
        return 60;
    }
    if call.is_none() {
        return 30;
    }
    if python_low_signal_call_pattern(&line) {
        15
    } else {
        65
    }
}

fn python_preview_index(lines: &[String], index: usize) -> usize {
    let line = lines.get(index).cloned().unwrap_or_default();
    if !PreviewShape::Compound.is_match(&line) {
        return index;
    }
    match first_python_child_line(lines, index) {
        None => index,
        Some(child_index) => python_preview_index(lines, child_index),
    }
}

struct PythonStringScan {
    value: String,
    end: usize,
    closed: bool,
    /// Saw a cooked escape whose value is not computed here.
    unsupported_escape: bool,
}

fn is_unsupported_escape_char(ch: char) -> bool {
    matches!(
        ch,
        'x' | 'u' | 'U' | 'N' | 'a' | 'b' | 'f' | 'v' | '0'..='7'
    )
}

/// Walk a python string-literal body from just after the opening delimiter,
/// following python's escape rules (in raw strings backslash-quote never
/// closes). Offsets index bytes into `code`.
fn scan_python_string_literal(
    code: &str,
    start: usize,
    quote: &str,
    raw: bool,
) -> PythonStringScan {
    let mut value = String::new();
    let mut i = start;
    let mut unsupported_escape = false;
    let quote_bytes = quote.as_bytes();
    while i < code.len() {
        let ch = code[i..].chars().next().expect("char boundary");
        if ch == '\\' && i + 1 < code.len() {
            let next = code[i + 1..].chars().next().expect("char boundary");
            if raw {
                value.push('\\');
                value.push(next);
            } else {
                if is_unsupported_escape_char(next) {
                    unsupported_escape = true;
                }
                match next {
                    '\n' => {} // backslash-newline is a line continuation
                    '"' => value.push('"'),
                    '\'' => value.push('\''),
                    '\\' => value.push('\\'),
                    'n' => value.push('\n'),
                    'r' => value.push('\r'),
                    't' => value.push('\t'),
                    other => {
                        value.push('\\');
                        value.push(other);
                    }
                }
            }
            i += 1 + next.len_utf8();
            continue;
        }
        if code.as_bytes()[i..].starts_with(quote_bytes) {
            return PythonStringScan {
                value,
                end: i + quote.len(),
                closed: true,
                unsupported_escape,
            };
        }
        if quote.len() == 1 && ch == '\n' {
            break; // single-quoted literals cannot span lines
        }
        value.push(ch);
        i += ch.len_utf8();
    }
    PythonStringScan {
        value,
        end: i,
        closed: false,
        unsupported_escape,
    }
}

/// Keep source-line positions while masking multiline-string continuations.
///
/// # Panics
///
/// Cannot panic for any valid `code`: the `expect` guards the scanner
/// invariant that the loop only ever advances to a char start (whole
/// chars, escapes, or quote delimiters).
pub fn python_statement_lines(code: &str) -> Vec<String> {
    let mut lines: Vec<String> = code.split('\n').map(String::from).collect();
    let mut line = 0usize;
    let mut i = 0usize;
    while i < code.len() {
        let ch = code[i..].chars().next().expect("char boundary");
        if ch == '#' {
            let Some(nl) = code[i..].find('\n') else {
                break;
            };
            i += nl;
            continue;
        }
        if ch == '"' || ch == '\'' {
            let quote = if code[i..].starts_with(&ch.to_string().repeat(3)) {
                ch.to_string().repeat(3)
            } else {
                ch.to_string()
            };
            let scan = scan_python_string_literal(code, i + quote.len(), &quote, true);
            let start_line = line;
            for end in i..scan.end {
                if code.as_bytes().get(end) == Some(&b'\n') {
                    line += 1;
                    while lines.len() <= line {
                        lines.push(String::new());
                    }
                    lines[line] = String::new();
                }
            }
            if scan.closed && line > start_line {
                let column = scan.end - (code[..scan.end].rfind('\n').map_or(0, |p| p + 1));
                let rest_start = scan.end;
                let rest_end = code[rest_start..]
                    .find('\n')
                    .map_or(code.len(), |p| rest_start + p);
                while lines.len() <= line {
                    lines.push(String::new());
                }
                lines[line] = format!("{}{}", " ".repeat(column), &code[rest_start..rest_end]);
            }
            i = scan.end;
            continue;
        }
        if ch == '\n' {
            line += 1;
        }
        i += ch.len_utf8();
    }
    lines
}

fn extract_bash_skill_command(code: &str) -> Option<String> {
    let m = PreviewShape::BashCall.captures(code)?;
    let quote = m.get(1)?;
    let start = m.end();
    // The character before the quote (r/R) marks a raw literal.
    let head: Vec<char> = code[..start].chars().collect();
    let quote_chars = quote.chars().count();
    let prefix_char = if head.len() > quote_chars {
        head[head.len() - quote_chars - 1]
    } else {
        ' '
    };
    let raw = matches!(prefix_char, 'r' | 'R');
    let scan = scan_python_string_literal(code, start, quote, raw);
    if !scan.closed || scan.unsupported_escape {
        return None;
    }
    let rest = code[scan.end..].trim_start();
    // Require a plain literal first argument; concatenation or other
    // expressions fall back.
    if !rest.starts_with(',') && !rest.starts_with(')') {
        return None;
    }
    Some(scan.value)
}

/// Pick the highest-signal line of a python cell as its preview.
pub fn preview_python_code(code: &str) -> CodePreview {
    let raw_lines: Vec<String> = code.split('\n').map(String::from).collect();
    let lines: Vec<String> = python_statement_lines(code)
        .into_iter()
        .map(|line| PreviewShape::Semicolon.replace(&line, "$1"))
        .collect();
    let paths = python_path_vars(&lines);
    let mut best_index: Option<usize> = None;
    let mut best_score: i64 = -1;
    // Scored last to first: a compound statement's score takes its first
    // child's, a later line.
    let mut scores = vec![0i64; lines.len()];
    for i in (0..lines.len()).rev() {
        let score = python_line_score(&lines, i, &paths, &scores);
        scores[i] = score;
    }
    for (i, score) in scores.into_iter().enumerate() {
        if score > best_score {
            best_index = Some(i);
            best_score = score;
        }
    }

    if let Some(best_index) = best_index.filter(|_| best_score >= 0) {
        let preview_index = python_preview_index(&lines, best_index);
        // Keep the original tail for multiline commands, excluding any
        // preceding string continuation.
        let mut joined = String::new();
        if let Some(first) = lines.get(preview_index) {
            joined.push_str(first);
        }
        for raw in raw_lines.iter().skip(preview_index + 1) {
            joined.push('\n');
            joined.push_str(raw);
        }
        if let Some(bash_command) = extract_bash_skill_command(&joined) {
            return preview_bash_command(&bash_command);
        }
        let text = python_preview_line(&lines, preview_index, &paths);
        return CodePreview::python(descriptor(&text));
    }
    CodePreview::python(String::new())
}

/// Preview an python cell: %%bash cells preview as bash, the rest as python.
#[must_use]
pub fn preview_ipython_code(code: &str) -> CodePreview {
    let trimmed = js_trim_end(code);
    if let Some(cell) = parse_ipython_bash_cell(trimmed) {
        return preview_bash_command(&cell.body);
    }
    preview_python_code(trimmed)
}
