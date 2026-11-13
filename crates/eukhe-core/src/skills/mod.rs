//! Skill discovery, validation, and prompt formatting. Port of core/skills.ts.

mod check;
pub mod diagnostics;
pub mod discovery;
pub mod frontmatter;
pub mod loader;
pub mod prompt_templates;

use std::path::PathBuf;

use serde::Serialize;

pub use diagnostics::{ResourceCollision, ResourceDiagnostic};
pub use discovery::load_skills_from_dir;
pub use eukhe_types::slash_commands::parse_slash_command;
pub use loader::{load_skills, LoadSkillsOptions, LoadSkillsResult};
pub use prompt_templates::{
    expand_prompt_template, load_prompt_templates, substitute_args, LoadPromptTemplatesOptions,
    LoadPromptTemplatesResult, PromptTemplate,
};

/// Source provenance for a resource (port of source-info.ts, synthetic form).
#[derive(Debug, Clone, Serialize, PartialEq)]
#[serde(rename_all = "camelCase")]
pub struct SourceInfo {
    pub path: String,
    pub source: String,
    pub scope: SourceScope,
    pub origin: SourceOrigin,
    pub base_dir: Option<String>,
}

#[derive(Debug, Clone, Copy, Serialize, PartialEq)]
#[serde(rename_all = "camelCase")]
pub enum SourceScope {
    User,
    Project,
    Temporary,
}

#[derive(Debug, Clone, Copy, Serialize, PartialEq)]
#[serde(rename_all = "camelCase")]
pub enum SourceOrigin {
    Package,
    TopLevel,
}

/// Markdown entry test: the file name carries a lowercase `.md` extension
/// (TS `endsWith('.md')` parity: mixed-case suffixes stay undiscovered, and a
/// bare `.md` name has no extension and does not count).
#[must_use]
pub fn skill_markdown_name(name: &str) -> bool {
    std::path::Path::new(name)
        .extension()
        .is_some_and(|ext| ext == "md")
}

pub fn create_synthetic_source_info(
    path: &str,
    source: &str,
    scope: SourceScope,
    base_dir: Option<&str>,
) -> SourceInfo {
    SourceInfo {
        path: path.to_string(),
        source: source.to_string(),
        scope,
        origin: SourceOrigin::TopLevel,
        base_dir: base_dir.map(str::to_string),
    }
}

/// Python runtime metadata for a Python-backed skill.
#[derive(Debug, Clone, Serialize, PartialEq)]
#[serde(rename_all = "camelCase")]
pub struct SkillPythonMetadata {
    pub import_name: String,
    pub package_path: PathBuf,
    pub pyproject_path: PathBuf,
}

/// A discovered skill.
#[derive(Debug, Clone, Serialize, PartialEq)]
#[serde(rename_all = "camelCase")]
pub struct Skill {
    pub name: String,
    pub description: String,
    pub file_path: PathBuf,
    pub base_dir: PathBuf,
    pub source_info: SourceInfo,
    pub disable_model_invocation: bool,
    pub kind: SkillKind,
    pub python: Option<SkillPythonMetadata>,
}

#[derive(Debug, Clone, Copy, Serialize, PartialEq)]
#[serde(rename_all = "camelCase")]
pub enum SkillKind {
    Markdown,
    Python,
}

impl Skill {
    #[must_use]
    pub fn is_python(&self) -> bool {
        self.kind == SkillKind::Python
    }
}

/// The longest skill description the prompt lists, in characters.
const SKILL_DESCRIPTION_CHARS: usize = 80;

/// Format skills for a system prompt: inside `<skills>` tags, one
/// `- name: description` line per skill, a Python skill's line naming its
/// import (`- name (python: import): description`), under a heading that
/// says where the skills' files are: `<dir>/<name>/SKILL.md:` for a run of
/// skills whose directory is their name under one parent, else the skill's
/// own file path. A description longer than [`SKILL_DESCRIPTION_CHARS`]
/// keeps its first sentence when that has at least 40 characters, else its
/// words up to the limit and `…` (omp's preview); the skill file has the
/// rest. The core layer says how to load one. Skills with
/// disableModelInvocation are excluded.
#[must_use]
pub fn format_skills_for_prompt(skills: &[Skill]) -> String {
    let mut text = String::new();
    let mut heading = String::new();
    for skill in skills
        .iter()
        .filter(|skill| !skill.disable_model_invocation)
    {
        let named_dir = skill.base_dir.file_name() == Some(std::ffi::OsStr::new(&skill.name))
            && skill.file_path == skill.base_dir.join("SKILL.md");
        let this_heading = match skill.base_dir.parent() {
            Some(parent) if named_dir => format!("{}/<name>/SKILL.md:", parent.display()),
            Some(_) | None => format!("{}:", skill.file_path.display()),
        };
        if this_heading != heading {
            text.push_str("\n\n");
            text.push_str(&this_heading);
            heading = this_heading;
        }
        text.push_str("\n- ");
        text.push_str(&skill.name);
        if let Some(python) = &skill.python {
            text.push_str(" (python: ");
            text.push_str(&python.import_name);
            text.push(')');
        }
        text.push_str(": ");
        // One line: every run of whitespace a single space.
        let description = skill.description.split_whitespace().collect::<Vec<_>>();
        let description = description.join(" ");
        if description.chars().count() <= SKILL_DESCRIPTION_CHARS {
            text.push_str(&description);
        } else {
            let window_end = description
                .char_indices()
                .nth(SKILL_DESCRIPTION_CHARS - 1)
                .map_or(description.len(), |(at, _)| at);
            let window = &description[..window_end];
            let sentence = window
                .match_indices(['.', '!', '?'])
                .map(|(at, _)| at + 1)
                .find(|&end| description[end..].starts_with(' '))
                .map(|end| &window[..end])
                .filter(|sentence| sentence.chars().count() >= 40);
            if let Some(sentence) = sentence {
                text.push_str(sentence);
            } else {
                let words = window
                    .rfind(' ')
                    .map_or(window, |space| window[..space].trim_end());
                text.push_str(words);
                text.push('…');
            }
        }
    }
    if text.is_empty() {
        return text;
    }
    format!("<skills>\n{}\n</skills>", text.trim_start_matches('\n'))
}

/// Expand skill commands (`/skill:<name> [args]`) into the `<skill ...>`
/// message block. Port of `AgentSession._expandSkillCommand`: a non-skill
/// input passes through unchanged; an unknown skill name passes through
/// (the surfaces show their own unknown-command notice); a skill file that
/// fails to read passes through. Returns the skill the expansion used so
/// the caller can report the invocation.
#[must_use]
pub fn expand_skill_command<'a>(text: &str, skills: &'a [Skill]) -> (String, Option<&'a Skill>) {
    let Some((name, args)) = parse_slash_command(text) else {
        return (text.to_string(), None);
    };
    let Some(skill_name) = name.strip_prefix("skill:") else {
        return (text.to_string(), None);
    };
    let Some(skill) = skills.iter().find(|skill| skill.name == skill_name) else {
        return (text.to_string(), None);
    };
    let Ok(content) = std::fs::read_to_string(&skill.file_path) else {
        return (text.to_string(), None);
    };
    let body = frontmatter::strip_frontmatter(&content).trim().to_string();
    let block = format!(
        "<skill name=\"{}\" location=\"{}\">\nReferences are relative to {}.\n\n{}\n</skill>",
        skill.name,
        skill.file_path.display(),
        skill.base_dir.display(),
        body
    );
    let expanded = if args.is_empty() {
        block
    } else {
        format!("{block}\n\n{args}")
    };
    (expanded, Some(skill))
}

#[cfg(test)]
mod tests {
    use super::*;

    fn temp_skill(name: &str, dir: &std::path::Path) -> Skill {
        let file_path = dir.join("SKILL.md");
        std::fs::write(
            &file_path,
            format!("---\nname: {name}\ndescription: test skill\n---\nUse {name} well."),
        )
        .expect("write skill file");
        Skill {
            name: name.to_string(),
            description: "test skill".to_string(),
            file_path: file_path.clone(),
            base_dir: dir.to_path_buf(),
            source_info: create_synthetic_source_info(
                &file_path.display().to_string(),
                "user",
                SourceScope::User,
                None,
            ),
            disable_model_invocation: false,
            kind: SkillKind::Markdown,
            python: None,
        }
    }

    #[test]
    fn expands_a_known_skill_command_with_and_without_args() {
        let dir = tempfile::tempdir().expect("tempdir");
        let skill = temp_skill("web-search", dir.path());
        let skills = [skill];
        let (expanded, used) = expand_skill_command("/skill:web-search", &skills);
        assert_eq!(used.map(|skill| skill.name.as_str()), Some("web-search"));
        let parsed = eukhe_types::skill_blocks::parse_skill_block(&expanded).expect("parses");
        assert_eq!(parsed.name, "web-search");
        // TS block shape: the references note rides inside the body,
        // ahead of the frontmatter-stripped skill content.
        assert_eq!(
            parsed.content,
            format!(
                "References are relative to {}.\n\nUse web-search well.",
                dir.path().display()
            )
        );
        assert_eq!(parsed.user_message, None);
        assert!(parsed.location.ends_with("SKILL.md"));

        let (expanded, used) = expand_skill_command("/skill:web-search find rust tuis", &skills);
        assert_eq!(used.map(|skill| skill.name.as_str()), Some("web-search"));
        let parsed = eukhe_types::skill_blocks::parse_skill_block(&expanded).expect("parses");
        assert_eq!(
            parsed.user_message.as_deref(),
            Some("find rust tuis"),
            "args follow the block after a blank line"
        );
    }

    #[test]
    fn an_empty_frontmatter_block_is_a_warned_skip_not_a_panic() {
        // TS no-frontmatter semantics: the whole document is the body, the
        // description is missing, the skill is NOT loaded (warning).
        let dir = tempfile::tempdir().expect("tempdir");
        let skill_dir = dir.path().join("bare");
        std::fs::create_dir_all(&skill_dir).expect("mkdir");
        std::fs::write(skill_dir.join("SKILL.md"), "---\n---\nUse it well.").expect("write");
        let result = crate::skills::load_skills_from_dir(dir.path(), "user");
        assert_eq!(result.skills, []);
        assert!(result.diagnostics.iter().any(
            |d| matches!(d, crate::skills::ResourceDiagnostic::Warning { message, .. }
                if message == "description is required")
        ));
    }

    #[test]
    fn an_empty_frontmatter_name_falls_back_to_the_parent_directory() {
        // TS `frontmatter.name || parentDirName`.
        let dir = tempfile::tempdir().expect("tempdir");
        let skill_dir = dir.path().join("named-dir");
        std::fs::create_dir_all(&skill_dir).expect("mkdir");
        std::fs::write(
            skill_dir.join("SKILL.md"),
            "---\nname: \"\"\ndescription: The named dir skill\n---\nbody",
        )
        .expect("write");
        let result = crate::skills::load_skills_from_dir(dir.path(), "user");
        assert_eq!(
            result
                .skills
                .iter()
                .map(|skill| skill.name.as_str())
                .collect::<Vec<_>>(),
            vec!["named-dir"]
        );
    }

    #[test]
    fn non_skill_and_unknown_inputs_pass_through() {
        let dir = tempfile::tempdir().expect("tempdir");
        let skills = [temp_skill("web-search", dir.path())];
        for text in [
            "hello world",
            "/compact",
            "/skill:missing do something",
            "/skill:",
        ] {
            let (expanded, used) = expand_skill_command(text, &skills);
            assert_eq!(expanded, text, "{text} must pass through");
            assert!(used.is_none(), "{text} must not report a skill");
        }
    }

    #[test]
    fn an_unreadable_skill_file_passes_through() {
        let dir = tempfile::tempdir().expect("tempdir");
        let mut skill = temp_skill("gone", dir.path());
        std::fs::remove_file(&skill.file_path).expect("remove skill file");
        skill.file_path = dir.path().join("missing-SKILL.md");
        let skills = [skill];
        let (expanded, used) = expand_skill_command("/skill:gone", &skills);
        assert_eq!(expanded, "/skill:gone");
        assert!(used.is_none());
    }

    #[test]
    fn prompt_formatting_lists_one_line_per_visible_skill_under_its_directory() {
        let skill = |name: &str, dir: &str, disable: bool| Skill {
            name: name.to_string(),
            description: format!("Does {name},\n  then  stops."),
            file_path: PathBuf::from(dir).join("SKILL.md"),
            base_dir: PathBuf::from(dir),
            source_info: create_synthetic_source_info(dir, "user", SourceScope::User, None),
            disable_model_invocation: disable,
            kind: SkillKind::Markdown,
            python: None,
        };
        assert_eq!(
            format_skills_for_prompt(&[skill("hidden", "/r/hidden", true)]),
            ""
        );
        let mut python = skill("web-tool", "/r/web-tool", false);
        python.kind = SkillKind::Python;
        python.python = Some(SkillPythonMetadata {
            import_name: "web_tool".to_string(),
            package_path: PathBuf::from("/r/web-tool/src"),
            pyproject_path: PathBuf::from("/r/web-tool/pyproject.toml"),
        });
        assert_eq!(
            format_skills_for_prompt(&[
                skill("web-search", "/r/web-search", false),
                skill("hidden", "/r/hidden", true),
                python,
                skill("odd", "/p/elsewhere", false),
                skill("other", "/r/other", false),
            ]),
            "<skills>\n/r/<name>/SKILL.md:\n\
             - web-search: Does web-search, then stops.\n\
             - web-tool (python: web_tool): Does web-tool, then stops.\n\n\
             /p/elsewhere/SKILL.md:\n\
             - odd: Does odd, then stops.\n\n\
             /r/<name>/SKILL.md:\n\
             - other: Does other, then stops.\n</skills>"
        );
    }

    /// A long description keeps its first sentence when that is long
    /// enough, else its whole words up to the limit and `…`.
    #[test]
    fn long_descriptions_are_cut_at_a_sentence_or_a_word() {
        let skill = |name: &str, description: &str| Skill {
            name: name.to_string(),
            description: description.to_string(),
            file_path: PathBuf::from("/r").join(name).join("SKILL.md"),
            base_dir: PathBuf::from("/r").join(name),
            source_info: create_synthetic_source_info("/r", "user", SourceScope::User, None),
            disable_model_invocation: false,
            kind: SkillKind::Markdown,
            python: None,
        };
        let words = "word ".repeat(30);
        assert_eq!(
            format_skills_for_prompt(&[
                skill(
                    "sentence",
                    &format!("Build decks from lecture notes and slides. {words}")
                ),
                skill("short", &format!("Short one. {words}")),
                skill("fits", "Fits the limit."),
            ]),
            format!(
                "<skills>\n/r/<name>/SKILL.md:\n\
                 - sentence: Build decks from lecture notes and slides.\n\
                 - short: Short one. {}…\n\
                 - fits: Fits the limit.\n</skills>",
                "word ".repeat(13).trim_end()
            )
        );
    }
}
