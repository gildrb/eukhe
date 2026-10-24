//! Prompt templates: slash-command expandable markdown templates.
//! Port of core/prompt-templates.ts.

use std::path::{Path, PathBuf};

use serde::Serialize;

use super::check::template_description;
use super::diagnostics::ResourceDiagnostic;
use super::frontmatter::parse_frontmatter;
use super::{create_synthetic_source_info, skill_markdown_name, SourceInfo, SourceScope};
pub use eukhe_types::slash_commands::parse_slash_command;

/// A prompt template loaded from a markdown file.
#[derive(Debug, Clone, Serialize, PartialEq)]
#[serde(rename_all = "camelCase")]
pub struct PromptTemplate {
    pub name: String,
    pub description: String,
    pub argument_hint: Option<String>,
    pub content: String,
    pub source_info: SourceInfo,
    pub file_path: String,
}

/// Parse command arguments respecting quoted strings (bash-style).
#[must_use]
pub fn parse_command_args(args_string: &str) -> Vec<String> {
    let mut args = Vec::new();
    let mut current = String::new();
    let mut in_quote: Option<char> = None;
    // An explicitly quoted token is an argument even when empty.
    let mut quoted = false;
    for char in args_string.chars() {
        if let Some(quote) = in_quote {
            if char == quote {
                in_quote = None;
            } else {
                current.push(char);
            }
        } else if char == '"' || char == '\'' {
            in_quote = Some(char);
            quoted = true;
        } else if char.is_whitespace() {
            if !current.is_empty() || quoted {
                args.push(current.clone());
                current.clear();
                quoted = false;
            }
        } else {
            current.push(char);
        }
    }
    if !current.is_empty() || quoted {
        args.push(current);
    }
    args
}

/// Substitute `$1`, `$@`, `$ARGUMENTS`, and `${@:N:L}` placeholders.
/// No recursive substitution of argument values.
pub fn substitute_args(content: &str, args: &[String]) -> String {
    let all_args = args.join(" ");
    let mut out = String::with_capacity(content.len());
    let bytes: Vec<char> = content.chars().collect();
    let mut i = 0;
    while i < bytes.len() {
        if bytes[i] != '$' {
            out.push(bytes[i]);
            i += 1;
            continue;
        }
        // $ at end of string.
        if i + 1 >= bytes.len() {
            out.push('$');
            break;
        }
        let next = bytes[i + 1];
        // ${@:N[:L]}
        if next == '{' {
            if let Some(close) = bytes[i + 2..].iter().position(|c| *c == '}') {
                let inner: String = bytes[i + 2..i + 2 + close].iter().collect();
                if let Some(rest) = inner.strip_prefix("@:") {
                    let mut parts = rest.splitn(2, ':');
                    let start = parts.next().unwrap_or("0").parse::<usize>().unwrap_or(1);
                    let start = start.saturating_sub1_or_zero();
                    let length = parts.next().and_then(|l| l.parse::<usize>().ok());
                    let slice: Vec<&str> = match length {
                        Some(length) => args
                            .iter()
                            .skip(start)
                            .take(length)
                            .map(String::as_str)
                            .collect(),
                        None => args.iter().skip(start).map(String::as_str).collect(),
                    };
                    out.push_str(&slice.join(" "));
                    i += 2 + close + 1;
                    continue;
                }
            }
            out.push('$');
            i += 1;
            continue;
        }
        // ARGUMENTS
        if content[i..].starts_with("$ARGUMENTS") {
            out.push_str(&all_args);
            i += "$ARGUMENTS".len();
            continue;
        }
        if next == '@' {
            out.push_str(&all_args);
            i += 2;
            continue;
        }
        if next.is_ascii_digit() {
            let mut j = i + 1;
            while j < bytes.len() && bytes[j].is_ascii_digit() {
                j += 1;
            }
            let number: String = bytes[i + 1..j].iter().collect();
            let index: usize = number.parse().unwrap_or(0);
            if let Some(value) = args.get(index.saturating_sub(1)) {
                out.push_str(value);
            }
            i = j;
            continue;
        }
        out.push('$');
        i += 1;
    }
    out
}

trait SaturatingSub1OrZero {
    fn saturating_sub1_or_zero(self) -> usize;
}
impl SaturatingSub1OrZero for usize {
    fn saturating_sub1_or_zero(self) -> usize {
        if self == 0 {
            0
        } else {
            self - 1
        }
    }
}

/// Load one template file.
///
/// # Errors
///
/// The file is not read, or its frontmatter is not valid YAML: the
/// diagnostic carries the file's path and the error text.
fn load_template_from_file(
    file_path: &Path,
    source_info: SourceInfo,
) -> Result<PromptTemplate, Box<ResourceDiagnostic>> {
    let failed = |message: String| {
        Box::new(ResourceDiagnostic::Warning {
            message,
            path: Some(file_path.display().to_string()),
        })
    };
    let raw_content = std::fs::read_to_string(file_path)
        .map_err(|error| failed(format!("prompt template not read: {error}")))?;
    let (frontmatter, body) = parse_frontmatter(&raw_content).map_err(failed)?;
    let name = file_path
        .file_name()
        .ok_or_else(|| failed("prompt template path has no file name".to_owned()))?
        .to_string_lossy()
        .trim_end_matches(".md")
        .to_string();

    // The frontmatter's description, else the body's first line that is
    // not blank, trimmed and cut to 60 chars: the compiled core's.
    let description = template_description(
        frontmatter
            .get("description")
            .and_then(|value| value.as_str()),
        &body,
    )
    .map_err(|error| failed(format!("prompt template not checked: {error}")))?;
    let argument_hint = frontmatter
        .get("argument-hint")
        .and_then(|value| value.as_str())
        .map(str::to_string);
    Ok(PromptTemplate {
        name,
        description,
        argument_hint,
        content: body,
        source_info,
        file_path: file_path.display().to_string(),
    })
}

/// Load the templates of `dir` into `result`. A missing directory holds
/// none; every other failure is a diagnostic.
fn load_templates_from_dir(
    dir: &Path,
    get_source_info: &dyn Fn(&Path) -> SourceInfo,
    result: &mut LoadPromptTemplatesResult,
) {
    let entries = match std::fs::read_dir(dir) {
        Ok(entries) => entries,
        Err(error) if error.kind() == std::io::ErrorKind::NotFound => return,
        Err(error) => {
            result.diagnostics.push(ResourceDiagnostic::Warning {
                message: format!("prompt template directory not read: {error}"),
                path: Some(dir.display().to_string()),
            });
            return;
        }
    };
    for entry in entries {
        let entry = match entry {
            Ok(entry) => entry,
            Err(error) => {
                result.diagnostics.push(ResourceDiagnostic::Warning {
                    message: format!("prompt template directory entry not read: {error}"),
                    path: Some(dir.display().to_string()),
                });
                continue;
            }
        };
        let path = entry.path();
        let name = entry.file_name().to_string_lossy().to_string();
        if !skill_markdown_name(&name) {
            continue;
        }
        match std::fs::metadata(&path) {
            Ok(metadata) if metadata.is_file() => {
                match load_template_from_file(&path, get_source_info(&path)) {
                    Ok(template) => result.templates.push(template),
                    Err(diagnostic) => result.diagnostics.push(*diagnostic),
                }
            }
            // A directory named `*.md` is no template file.
            Ok(_) => {}
            Err(error) => result.diagnostics.push(ResourceDiagnostic::Warning {
                message: format!("prompt template not read: {error}"),
                path: Some(path.display().to_string()),
            }),
        }
    }
}

/// The templates a load found, and a diagnostic for each file or path that
/// failed (with its path and the error text).
#[derive(Debug, Default, PartialEq)]
pub struct LoadPromptTemplatesResult {
    pub templates: Vec<PromptTemplate>,
    pub diagnostics: Vec<ResourceDiagnostic>,
}

#[derive(Debug, Default)]
pub struct LoadPromptTemplatesOptions {
    pub cwd: PathBuf,
    pub agent_dir: PathBuf,
    pub prompt_paths: Vec<String>,
    pub include_defaults: bool,
}

fn normalize_path(input: &str) -> PathBuf {
    let trimmed = input.trim();
    let home = || eukhe_types::platform::home_dir().unwrap_or_default();
    if trimmed == "~" {
        return home();
    }
    if let Some(rest) = trimmed.strip_prefix("~/") {
        return home().join(rest);
    }
    if let Some(rest) = trimmed.strip_prefix('~') {
        return home().join(rest);
    }
    PathBuf::from(trimmed)
}

fn resolve_prompt_path(path: &str, cwd: &Path) -> PathBuf {
    let normalized = normalize_path(path);
    if normalized.is_absolute() {
        normalized
    } else {
        cwd.join(normalized)
    }
}

/// Load templates from agentDir/prompts/, `cwd/{CONFIG_DIR_NAME}/prompts/`, and
/// explicit paths (later entries win nothing: templates append in order).
/// Every template file or explicit path that fails is a diagnostic with its
/// path and the error text.
#[must_use]
pub fn load_prompt_templates(options: &LoadPromptTemplatesOptions) -> LoadPromptTemplatesResult {
    let mut result = LoadPromptTemplatesResult::default();
    let global_prompts_dir = options.agent_dir.join("prompts");
    let project_prompts_dir = options
        .cwd
        .join(super::loader::CONFIG_DIR_NAME)
        .join("prompts");

    let is_under = |target: &Path, root: &Path| -> bool {
        std::fs::canonicalize(root).is_ok_and(|root| target == root || target.starts_with(root))
            || target == root
            || target.starts_with(root)
    };

    let get_source_info = |path: &Path| -> SourceInfo {
        if is_under(path, &global_prompts_dir) {
            return create_synthetic_source_info(
                &path.display().to_string(),
                "local",
                SourceScope::User,
                Some(&global_prompts_dir.display().to_string()),
            );
        }
        if is_under(path, &project_prompts_dir) {
            return create_synthetic_source_info(
                &path.display().to_string(),
                "local",
                SourceScope::Project,
                Some(&project_prompts_dir.display().to_string()),
            );
        }
        let base = if path.is_dir() {
            path.to_path_buf()
        } else {
            path.parent().unwrap_or(path).to_path_buf()
        };
        create_synthetic_source_info(
            &path.display().to_string(),
            "local",
            SourceScope::Temporary,
            Some(&base.display().to_string()),
        )
    };

    if options.include_defaults {
        load_templates_from_dir(&global_prompts_dir, &get_source_info, &mut result);
        load_templates_from_dir(&project_prompts_dir, &get_source_info, &mut result);
    }
    for raw_path in &options.prompt_paths {
        let resolved = resolve_prompt_path(raw_path, &options.cwd);
        let failed = |message: String| ResourceDiagnostic::Warning {
            message,
            path: Some(resolved.display().to_string()),
        };
        let metadata = match std::fs::metadata(&resolved) {
            Ok(metadata) => metadata,
            Err(error) if error.kind() == std::io::ErrorKind::NotFound => {
                result
                    .diagnostics
                    .push(failed("prompt template path does not exist".to_owned()));
                continue;
            }
            Err(error) => {
                result
                    .diagnostics
                    .push(failed(format!("prompt template path not read: {error}")));
                continue;
            }
        };
        if metadata.is_dir() {
            load_templates_from_dir(&resolved, &get_source_info, &mut result);
        } else if metadata.is_file() && resolved.to_string_lossy().ends_with(".md") {
            match load_template_from_file(&resolved, get_source_info(&resolved)) {
                Ok(template) => result.templates.push(template),
                Err(diagnostic) => result.diagnostics.push(*diagnostic),
            }
        } else {
            result.diagnostics.push(failed(
                "prompt template path is not a markdown file".to_owned(),
            ));
        }
    }
    result
}

/// Expand `/name args...` into the matching template, else return the text.
#[must_use]
pub fn expand_prompt_template(text: &str, templates: &[PromptTemplate]) -> String {
    let Some(parsed) = parse_slash_command(text) else {
        return text.to_string();
    };
    if let Some(template) = templates.iter().find(|t| t.name == parsed.0) {
        let args = parse_command_args(&parsed.1);
        return substitute_args(&template.content, &args);
    }
    text.to_string()
}

// `parseSlashCommand` (name, args for `/name args...`) is shared vocabulary:
// `eukhe_types::slash_commands::parse_slash_command`, re-exported above.

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn command_args_quoting() {
        assert_eq!(
            parse_command_args("a \"b c\" 'd e' \"\""),
            vec!["a", "b c", "d e", ""]
        );
        assert_eq!(parse_command_args("  "), Vec::<String>::new());
    }

    #[test]
    fn substitutes_positional_and_slices() {
        let args = vec!["one".to_string(), "two".to_string(), "three".to_string()];
        assert_eq!(substitute_args("$1 and $2", &args), "one and two");
        assert_eq!(substitute_args("$@", &args), "one two three");
        assert_eq!(substitute_args("$ARGUMENTS", &args), "one two three");
        assert_eq!(substitute_args("${@:2}", &args), "two three");
        assert_eq!(substitute_args("${@:2:1}", &args), "two");
        assert_eq!(substitute_args("${@:9}", &args), "");
        assert_eq!(substitute_args("$5", &args), "");
        assert_eq!(substitute_args("plain text", &args), "plain text");
        // TS regex greedily matches $10 as positional 10 (missing -> empty).
        assert_eq!(substitute_args("cost is $10", &args), "cost is ");
    }

    #[test]
    fn slash_command_parsing() {
        assert_eq!(
            parse_slash_command("/review do it"),
            Some(("review".to_string(), "do it".to_string()))
        );
        assert_eq!(
            parse_slash_command("/review"),
            Some(("review".to_string(), String::new()))
        );
        assert_eq!(parse_slash_command("no slash"), None);
    }

    #[test]
    fn template_expansion() {
        let template = PromptTemplate {
            name: "fix".to_string(),
            description: "Fix issues".to_string(),
            argument_hint: Some("[issue]".to_string()),
            content: "Fix $1 and also $2 now".to_string(),
            source_info: create_synthetic_source_info("/p", "local", SourceScope::User, None),
            file_path: "/p/fix.md".to_string(),
        };
        assert_eq!(
            expand_prompt_template("/fix lint types", std::slice::from_ref(&template)),
            "Fix lint and also types now"
        );
        // Unknown commands pass through.
        assert_eq!(
            expand_prompt_template("/unknown x", std::slice::from_ref(&template)),
            "/unknown x"
        );
    }

    #[test]
    fn loads_templates_from_dirs() {
        let tmp = tempfile::tempdir().unwrap();
        let agent_dir = tmp.path().join("agent");
        let project = tmp.path().join("project");
        std::fs::create_dir_all(agent_dir.join("prompts")).unwrap();
        std::fs::create_dir_all(project.join(".eukhe").join("prompts")).unwrap();
        std::fs::write(
            agent_dir.join("prompts").join("global.md"),
            "Global prompt body",
        )
        .unwrap();
        std::fs::write(
            project.join(".eukhe").join("prompts").join("local.md"),
            "---\ndescription: A local one\n---\nBody here",
        )
        .unwrap();
        let loaded = load_prompt_templates(&LoadPromptTemplatesOptions {
            cwd: project,
            agent_dir,
            prompt_paths: vec![],
            include_defaults: true,
        });
        assert_eq!(loaded.diagnostics, Vec::new());
        let templates = loaded.templates;
        let names: Vec<&str> = templates.iter().map(|t| t.name.as_str()).collect();
        assert!(names.contains(&"global"));
        assert!(names.contains(&"local"));
        let local = templates.iter().find(|t| t.name == "local").unwrap();
        assert_eq!(local.description, "A local one");
        assert_eq!(local.content, "Body here");
        // Description falls back to the first body line, truncated at 60.
        let global = templates.iter().find(|t| t.name == "global").unwrap();
        assert_eq!(global.description, "Global prompt body");
    }

    /// Every template file or path that fails is a diagnostic with its path
    /// and the error text: an unreadable file, invalid frontmatter, a
    /// dangling link, a missing path, and a path that is no markdown file.
    /// Before, each one was dropped without a word.
    #[cfg(unix)]
    #[test]
    fn reports_each_template_that_fails() {
        let tmp = tempfile::tempdir().unwrap();
        let prompts = tmp.path().join("prompts");
        std::fs::create_dir_all(&prompts).unwrap();
        std::fs::write(prompts.join("good.md"), "---\ndescription: Good\n---\nBody").unwrap();
        std::fs::write(prompts.join("binary.md"), [0xff, 0xfe, 0x00]).unwrap();
        let malformed = "---\ndescription: [x\n---\nBody";
        std::fs::write(prompts.join("malformed.md"), malformed).unwrap();
        std::os::unix::fs::symlink(tmp.path().join("gone.md"), prompts.join("dangling.md"))
            .unwrap();
        let text = tmp.path().join("notes.txt");
        std::fs::write(&text, "not a template").unwrap();
        let missing = tmp.path().join("missing.md");
        let loaded = load_prompt_templates(&LoadPromptTemplatesOptions {
            cwd: tmp.path().to_path_buf(),
            agent_dir: tmp.path().join("agent"),
            prompt_paths: vec![
                prompts.display().to_string(),
                missing.display().to_string(),
                text.display().to_string(),
            ],
            include_defaults: true,
        });
        let names: Vec<&str> = loaded.templates.iter().map(|t| t.name.as_str()).collect();
        assert_eq!(names, ["good"]);
        let warning = |path: &std::path::Path, message: String| ResourceDiagnostic::Warning {
            message,
            path: Some(path.display().to_string()),
        };
        let mut diagnostics = loaded.diagnostics;
        diagnostics.sort_by_key(|diagnostic| format!("{diagnostic:?}"));
        let mut expected = vec![
            warning(
                &prompts.join("binary.md"),
                "prompt template not read: stream did not contain valid UTF-8".to_owned(),
            ),
            warning(
                &prompts.join("malformed.md"),
                parse_frontmatter(malformed).unwrap_err(),
            ),
            warning(
                &prompts.join("dangling.md"),
                "prompt template not read: No such file or directory (os error 2)".to_owned(),
            ),
            warning(&missing, "prompt template path does not exist".to_owned()),
            warning(
                &text,
                "prompt template path is not a markdown file".to_owned(),
            ),
        ];
        expected.sort_by_key(|diagnostic| format!("{diagnostic:?}"));
        assert_eq!(diagnostics, expected);
    }
}
