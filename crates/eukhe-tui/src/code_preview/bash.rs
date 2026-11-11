//! Bash/Python command preview extraction for tool-call rendering.
//!
//! Port of `packages/coding-agent/src/core/tools/code-preview.ts`. Its
//! regexes are shapes in the compiled core ([`PreviewShape`]), with
//! JavaScript's whitespace and word classes; strings index UTF-16 as JS does.

use super::python::preview_python_code;
#[cfg(test)]
use super::python::{preview_ipython_code, python_statement_lines};
use super::shapes::PreviewShape;
use crate::text_shapes::{first_of, TextShape};

const DESCRIPTOR_MAX_WIDTH: usize = 64;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CodePreviewLanguage {
    Bash,
    Python,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CodePreview {
    pub language: CodePreviewLanguage,
    pub text: String,
}

impl CodePreview {
    fn bash(text: impl Into<String>) -> Self {
        CodePreview {
            language: CodePreviewLanguage::Bash,
            text: text.into(),
        }
    }

    pub(crate) fn python(text: impl Into<String>) -> Self {
        CodePreview {
            language: CodePreviewLanguage::Python,
            text: text.into(),
        }
    }
}

/// JS String.prototype.trim whitespace set.
fn is_js_whitespace(ch: char) -> bool {
    matches!(
        ch,
        '\u{09}'
            ..='\u{0D}'
                | ' '
                | '\u{00A0}'
                | '\u{1680}'
                | '\u{2028}'
                | '\u{2029}'
                | '\u{202F}'
                | '\u{205F}'
                | '\u{3000}'
                | '\u{FEFF}'
    ) || ('\u{2000}'..='\u{200A}').contains(&ch)
}

pub(crate) fn js_trim(text: &str) -> &str {
    text.trim_matches(is_js_whitespace)
}

pub(crate) fn js_trim_end(s: &str) -> &str {
    s.trim_end_matches(is_js_whitespace)
}

/// Number of UTF-16 code units (JS String.length).
fn utf16_len(s: &str) -> usize {
    s.chars().map(char::len_utf16).sum()
}

/// JS s.slice(0, n): first n UTF-16 code units.
fn utf16_slice_prefix(s: &str, n: usize) -> String {
    let mut units = 0usize;
    for (idx, ch) in s.char_indices() {
        if units + ch.len_utf16() > n {
            return s[..idx].to_string();
        }
        units += ch.len_utf16();
    }
    s.to_string()
}

pub(crate) fn collapse_whitespace(text: &str) -> String {
    PreviewShape::WhitespaceRun.replace_all(text, " ")
}

fn truncate_descriptor(text: &str) -> String {
    if utf16_len(text) <= DESCRIPTOR_MAX_WIDTH {
        return text.to_string();
    }
    let ellipsis = crate::glyphs::ELLIPSIS;
    let cut = utf16_slice_prefix(text, DESCRIPTOR_MAX_WIDTH - ellipsis.len());
    format!("{}{ellipsis}", js_trim_end(&cut))
}

/// Mask secrets, blobs, and oversized strings before display.
pub(crate) fn redact_noise(text: &str) -> String {
    let step1 = PreviewShape::Blob.replace_all(text, "<blob>");
    let step2 = PreviewShape::SecretQuoted.replace_all(&step1, "$1=<redacted>");
    let step3 = PreviewShape::SecretBare.replace_all(&step2, "$1=<redacted>");
    let step4 = PreviewShape::Authorization.replace_all(&step3, "$1<redacted>");
    let step5 = PreviewShape::SkKey.replace_all(&step4, "$1<redacted>$1");
    let clipped = format!("$1{}$1", crate::glyphs::ELLIPSIS);
    PreviewShape::LongString.replace_all(&step5, &clipped)
}

pub(crate) fn descriptor(text: &str) -> String {
    truncate_descriptor(js_trim(&collapse_whitespace(&redact_noise(text))))
}

/// Strip a leading ! magic and a leading cd-prefix chain segment.
pub(crate) fn strip_bash_prefix(line: &str) -> String {
    let no_magic = PreviewShape::Magic.replace(line, "");
    let trimmed = js_trim(&no_magic);
    let no_cd = PreviewShape::CdPrefix.replace(trimmed, "");
    js_trim(&no_cd).to_string()
}

pub(crate) fn is_skippable_bash_line(line: &str) -> bool {
    let trimmed = js_trim(line);
    trimmed.is_empty()
        || first_of(
            &[
                PreviewShape::Comment,
                PreviewShape::SetLine,
                PreviewShape::EnvLine,
            ],
            trimmed,
        )
        .is_some()
}

/// Split a command line into shell-quoted words.
fn shell_words(line: &str) -> Vec<String> {
    PreviewShape::ShellWord
        .captures_iter(line)
        .into_iter()
        .filter_map(|c| {
            c.get(1)
                .or_else(|| c.get(2))
                .or_else(|| c.get(3))
                .map(str::to_string)
        })
        .collect()
}

/// Drop a leading ./ from a path.
pub(crate) fn path_tail(path: &str) -> String {
    PreviewShape::DotSlash.replace(path, "")
}

/// Shorten well-known runner invocations (given as their shell words) for
/// display.
fn simplify_runner_command(words: &[String]) -> Option<String> {
    let joined = words.join(" ");
    if words.first().map(String::as_str) == Some("npx")
        && words.get(1).map(String::as_str) == Some("tsx")
    {
        let vitest_index = words
            .iter()
            .position(|w| PreviewShape::VitestCli.is_match(w));
        if let Some(vi) = vitest_index.filter(|&i| i >= 2) {
            return Some(
                format!("vitest {}", words[vi + 1..].join(" "))
                    .trim()
                    .to_string(),
            );
        }
    }
    if words.first().map(String::as_str) == Some("npm") {
        let prefix_index = words.iter().position(|w| w == "--prefix");
        let cwd = prefix_index.and_then(|i| words.get(i + 1)).cloned();
        if let Some(ri) = words.iter().position(|w| w == "run") {
            if let Some(next) = words.get(ri + 1) {
                let command = format!("npm {} {}", next, words[ri + 2..].join(" "))
                    .trim()
                    .to_string();
                return cwd
                    .map(|cwd| format!("{command} ({})", path_tail(&cwd)))
                    .or(Some(command));
            }
        }
    }
    if words.first().map(String::as_str) == Some("pnpm") {
        let cwd_index = words.iter().position(|w| w == "-C" || w == "--dir");
        let cwd = cwd_index.and_then(|i| words.get(i + 1)).cloned();
        if let Some(ci) = cwd_index {
            let rest: Vec<&str> = words
                .iter()
                .enumerate()
                .filter(|(i, _)| *i != ci && *i != ci + 1)
                .map(|(_, w)| w.as_str())
                .collect();
            return cwd.map(|cwd| format!("{} ({})", rest.join(" "), path_tail(&cwd)));
        }
        return None;
    }
    // TS findIndex: word === "pytest" (the -m clause is unreachable there).
    if words.first().map(String::as_str) == Some("uv")
        && words.get(1).map(String::as_str) == Some("run")
    {
        if let Some(pi) = words.iter().position(|w| w == "pytest") {
            return Some(
                format!("pytest {}", words[pi + 1..].join(" "))
                    .trim()
                    .to_string(),
            );
        }
    }
    if matches!(
        words.first().map(String::as_str),
        Some("python" | "python3")
    ) && words.get(1).map(String::as_str) == Some("-m")
        && words.get(2).map(String::as_str) == Some("pytest")
    {
        return Some(
            format!("pytest {}", words[3..].join(" "))
                .trim()
                .to_string(),
        );
    }
    if joined.contains("node_modules/.bin/") {
        return Some(PreviewShape::BinPrefix.replace_all(&joined, ""));
    }
    None
}

/// Shorten file-mutation commands (cat >, tee, `apply_patch`; `words` are
/// the line's shell words) for display.
fn simplify_mutation_command(line: &str, words: &[String]) -> Option<String> {
    if words.is_empty() {
        return None;
    }
    let first = words[0].as_str();
    if first == "cat" && words.get(1).map(String::as_str) == Some(">") && words.len() > 2 {
        return Some(format!("write {}", path_tail(&words[2])));
    }
    if first == "tee" {
        if let Some(last) = words.last() {
            let action = if words.iter().any(|w| w == "-a") {
                "append"
            } else {
                "write"
            };
            return Some(format!("{action} {}", path_tail(last)));
        }
    }
    if first == "apply_patch" {
        return Some("apply patch".to_string());
    }
    if matches!(first, "rm" | "mv" | "cp" | "git" | "npm") {
        return Some(line.to_string());
    }
    if (first == "sed" && words.iter().any(|w| w.starts_with("-i")))
        || (first == "perl" && words.iter().any(|w| w == "-pi"))
    {
        return Some(line.to_string());
    }
    None
}

pub(crate) fn simplify_bash_command_line(line: &str) -> String {
    simplify_words(line, &shell_words(line))
}

/// [`simplify_bash_command_line`] of a line whose shell words are `words`.
fn simplify_words(line: &str, words: &[String]) -> String {
    simplify_runner_command(words)
        .or_else(|| simplify_mutation_command(line, words))
        .unwrap_or_else(|| line.to_string())
}

/// Split a && b; c into its command segments.
pub(crate) fn split_command_chain(line: &str) -> Vec<String> {
    PreviewShape::ChainSeparator
        .split(line)
        .into_iter()
        .map(|p| js_trim(p).to_string())
        .filter(|p| !p.is_empty())
        .collect()
}

fn heredoc_body(lines: &[String], start_index: usize, delimiter: &str) -> Option<String> {
    // While args stream, preview the partial heredoc body rather than the
    // low-signal heredoc opener.
    let mut body: Vec<&str> = Vec::new();
    for line in lines.iter().skip(start_index + 1) {
        if js_trim(line) == delimiter {
            return Some(body.join("\n"));
        }
        body.push(line);
    }
    if body.is_empty() {
        None
    } else {
        Some(body.join("\n"))
    }
}

pub(crate) fn preview_heredoc(lines: &[String]) -> Option<CodePreview> {
    // A generic heredoc body is low-signal; keep it as a fallback and prefer a
    // later, more specific heredoc (python/bash/node/write) if one follows.
    let mut fallback: Option<CodePreview> = None;
    for (i, raw) in lines.iter().enumerate() {
        let line = strip_bash_prefix(raw);
        if is_skippable_bash_line(&line) {
            continue;
        }
        let captures = PreviewShape::Heredoc.captures(&line);
        let delimiter = captures.as_ref().and_then(|c| c.get(1)).map(str::to_string);
        let Some(delimiter) = delimiter else { continue };
        let Some(body) = heredoc_body(lines, i, &delimiter) else {
            continue;
        };
        if PreviewShape::PythonRun.is_match(&line) {
            let preview = preview_python_code(&body);
            if !preview.text.is_empty() {
                return Some(preview);
            }
            continue;
        }
        // Match bash/sh as an interpreter word (incl. /bin/sh), not a path
        // suffix like script.sh.
        if PreviewShape::ShellRun.is_match(&line) {
            let preview = preview_bash_command(&body);
            if !preview.text.is_empty() {
                return Some(preview);
            }
            return Some(CodePreview::bash(descriptor(&body)));
        }
        if PreviewShape::NodeRun.is_match(&line) {
            return Some(CodePreview::bash(format!("node: {}", descriptor(&body))));
        }
        let cat_write = PreviewShape::CatWrite
            .captures(&line)
            .and_then(|c| c.get(1).map(str::to_string));
        if let Some(target) = cat_write {
            let action = if line.contains("tee -a") {
                "append"
            } else {
                "write"
            };
            return Some(CodePreview::bash(format!(
                "{action} {}",
                path_tail(&target)
            )));
        }
        if PreviewShape::ApplyPatch.is_match(&line) {
            return Some(CodePreview::bash("apply patch".to_string()));
        }
        fallback = Some(CodePreview::bash(descriptor(&body)));
    }
    fallback
}

/// The signal score of a command line, given its simplified form and its
/// shell words.
pub(crate) fn bash_line_score(
    line: &str,
    simplified: &str,
    words: &[String],
    index: usize,
) -> usize {
    let mut score = 30usize;
    if simplified != line {
        score += 40;
    }
    if words.first().is_some_and(|w| {
        matches!(
            w.as_str(),
            "rm" | "mv" | "cp" | "git" | "npm" | "pnpm" | "pytest" | "vitest"
        )
    }) {
        score += 20;
    }
    if PreviewShape::Mutation.is_match(line) {
        score += 40;
    }
    score + index
}

/// Pick the highest-signal line of a bash command as its preview.
pub fn preview_bash_command(command: &str) -> CodePreview {
    let lines: Vec<String> = command.split('\n').map(String::from).collect();
    let heredoc = preview_heredoc(&lines);
    if let Some(h) = heredoc.filter(|h| !h.text.is_empty()) {
        return CodePreview {
            language: h.language,
            text: descriptor(&h.text),
        };
    }

    let mut best: Option<(String, usize)> = None;
    let mut index = 0usize;
    for raw_line in &lines {
        for raw_part in split_command_chain(raw_line) {
            let command_line = strip_bash_prefix(js_trim(&raw_part));
            if command_line.is_empty() || is_skippable_bash_line(&command_line) {
                continue;
            }
            let words = shell_words(&command_line);
            let text = simplify_words(&command_line, &words);
            let score = bash_line_score(&command_line, &text, &words, index);
            if best.as_ref().is_none_or(|(_, s)| score > *s) {
                best = Some((text, score));
            }
            index += 1;
        }
    }
    CodePreview::bash(best.map_or(String::new(), |(text, _)| descriptor(&text)))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn descriptor_truncates_at_64_units() {
        let long = "hello world ".repeat(12);
        let d = descriptor(&long);
        assert_eq!(utf16_len(&d), 64);
        assert!(d.ends_with("..."));
    }

    #[test]
    fn redact_hides_tokens_and_blobs() {
        let text = "api_token = \"abc123\" and 01234567890123456789012345678901234567890123456789012345678901234567890123456789";
        let red = redact_noise(text);
        assert!(red.contains("api_token=<redacted>"));
        assert!(red.contains("<blob>"));
    }

    #[test]
    fn bash_preview_prefers_mutation_line() {
        let p = preview_bash_command("echo start && git commit -m x && ls");
        assert_eq!(p.text, "git commit -m x");
        assert_eq!(p.language, CodePreviewLanguage::Bash);
    }

    #[test]
    fn bash_preview_simplifies_npm_run() {
        let p = preview_bash_command("npm run test -- --watch");
        assert_eq!(p.text, "npm test -- --watch");
    }

    #[test]
    fn bash_preview_heredoc_python() {
        let cmd = "python3 <<'EOF'\nprint('hi')\nEOF";
        let p = preview_bash_command(cmd);
        assert_eq!(p.text, "print('hi')");
    }

    #[test]
    fn python_preview_file_operation() {
        let code = "p = Path('src/a.ts')\nprint('x')\np.write_text('data')";
        let p = preview_python_code(code);
        assert_eq!(p.text, "write src/a.ts");
        assert_eq!(p.language, CodePreviewLanguage::Python);
    }

    #[test]
    fn python_preview_bash_skill_call() {
        let code = "print('x')\nawait bash(\"git status --porcelain\")";
        let p = preview_python_code(code);
        assert_eq!(p.language, CodePreviewLanguage::Bash);
        assert_eq!(p.text, "git status --porcelain");
    }

    #[test]
    fn python_cell_magic_preview() {
        let p = preview_ipython_code("%%bash\necho hi");
        assert_eq!(p.language, CodePreviewLanguage::Bash);
        assert_eq!(p.text, "echo hi");
    }

    #[test]
    fn statement_lines_mask_multiline_strings() {
        let code = "x = \"\"\"\na\nb\n\"\"\"\nrun(1)";
        let lines = python_statement_lines(code);
        assert_eq!(lines[0], "x = \"\"\"");
        assert_eq!(lines[3].trim(), "");
        assert_eq!(lines[4], "run(1)");
    }
}
