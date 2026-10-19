//! Skill directory discovery. Port of loadSkillsFromDir in core/skills.ts.

use std::path::{Path, PathBuf};

use ignore::gitignore::{Gitignore, GitignoreBuilder};

use super::diagnostics::ResourceDiagnostic;
use super::frontmatter::parse_frontmatter;
use super::skill_markdown_name;
use super::{
    create_synthetic_source_info, validate_skill_description, validate_skill_name, Skill,
    SkillKind, SkillPythonMetadata, SourceScope,
};

/// Sources that pick up a synthetic scope.
fn scope_for_source(source: &str) -> SourceScope {
    match source {
        "user" => SourceScope::User,
        "project" => SourceScope::Project,
        _ => SourceScope::Temporary,
    }
}

fn python_import_name_for_skill(name: &str) -> String {
    name.replace('-', "_")
}

fn is_valid_python_import_name(name: &str) -> bool {
    let mut chars = name.chars();
    match chars.next() {
        Some(first) if first.is_ascii_alphabetic() || first == '_' => {}
        _ => return false,
    }
    chars.all(|c| c.is_ascii_alphanumeric() || c == '_')
}

fn detect_python_skill(
    skill_dir: &Path,
    name: &str,
    diagnostics: &mut Vec<ResourceDiagnostic>,
) -> Option<SkillPythonMetadata> {
    let pyproject_path = skill_dir.join("pyproject.toml");
    if !pyproject_path.is_file() {
        return None;
    }
    let import_name = python_import_name_for_skill(name);
    if !is_valid_python_import_name(&import_name) {
        diagnostics.push(ResourceDiagnostic::Warning {
            message: format!("python skill import name \"{import_name}\" is invalid"),
            path: Some(pyproject_path.display().to_string()),
        });
        return None;
    }
    let package_init_path = skill_dir.join("src").join(&import_name).join("__init__.py");
    if !package_init_path.is_file() {
        diagnostics.push(ResourceDiagnostic::Warning {
            message: format!("python skill package src/{import_name}/__init__.py not found"),
            path: Some(pyproject_path.display().to_string()),
        });
        return None;
    }
    Some(SkillPythonMetadata {
        import_name,
        package_path: skill_dir.to_path_buf(),
        pyproject_path,
    })
}

/// Load a single skill file (SKILL.md or root .md).
pub(crate) fn load_skill_from_file(
    file_path: &Path,
    source: &str,
) -> (Option<Skill>, Vec<ResourceDiagnostic>) {
    let mut diagnostics = Vec::new();
    let raw_content = match std::fs::read_to_string(file_path) {
        Ok(content) => content,
        Err(error) => {
            diagnostics.push(ResourceDiagnostic::Warning {
                message: error.to_string(),
                path: Some(file_path.display().to_string()),
            });
            return (None, diagnostics);
        }
    };
    let frontmatter = match parse_frontmatter(&raw_content) {
        Ok((frontmatter, _body)) => frontmatter,
        Err(message) => {
            diagnostics.push(ResourceDiagnostic::Warning {
                message,
                path: Some(file_path.display().to_string()),
            });
            return (None, diagnostics);
        }
    };
    let skill_dir = file_path.parent().unwrap_or_else(|| Path::new("."));
    let parent_dir_name = skill_dir
        .file_name()
        .map(|name| name.to_string_lossy().to_string())
        .unwrap_or_default();

    let description = frontmatter
        .get("description")
        .and_then(|value| value.as_str())
        .unwrap_or_default()
        .to_string();
    for error in validate_skill_description(&description) {
        diagnostics.push(ResourceDiagnostic::Warning {
            message: error,
            path: Some(file_path.display().to_string()),
        });
    }

    // TS `frontmatter.name || parentDirName`: a falsy name (missing or the
    // empty string) falls back to the parent directory name.
    let name = frontmatter
        .get("name")
        .and_then(|value| value.as_str())
        .filter(|name| !name.is_empty())
        .map_or_else(|| parent_dir_name.clone(), str::to_string);

    for error in validate_skill_name(&name, &parent_dir_name) {
        diagnostics.push(ResourceDiagnostic::Warning {
            message: error,
            path: Some(file_path.display().to_string()),
        });
    }

    if description.trim().is_empty() {
        return (None, diagnostics);
    }

    let python = if file_path.file_name().is_some_and(|n| n == "SKILL.md") {
        detect_python_skill(skill_dir, &name, &mut diagnostics)
    } else {
        None
    };
    let skill = Skill {
        name,
        description,
        file_path: file_path.to_path_buf(),
        base_dir: skill_dir.to_path_buf(),
        source_info: create_synthetic_source_info(
            &file_path.display().to_string(),
            source,
            scope_for_source(source),
            Some(&skill_dir.display().to_string()),
        ),
        disable_model_invocation: frontmatter
            .get("disable-model-invocation")
            .and_then(serde_json::Value::as_bool)
            .unwrap_or(false),
        kind: if python.is_some() {
            SkillKind::Python
        } else {
            SkillKind::Markdown
        },
        python,
    };
    (Some(skill), diagnostics)
}

/// Where the discovery recursion keeps shared ignore rules: the builder
/// holds every rule found so far, the matcher is its last good build.
struct DiscoveryState {
    root: PathBuf,
    builder: GitignoreBuilder,
    matcher: Gitignore,
}

impl DiscoveryState {
    /// Add the rules of the ignore files in `dir`. A missing file adds
    /// nothing. An unreadable file, a rule that is not a glob, and rules
    /// that do not build into a matcher are reported in `diagnostics`; the
    /// other rules still apply.
    fn add_ignore_rules(&mut self, dir: &Path, diagnostics: &mut Vec<ResourceDiagnostic>) {
        let relative = dir.strip_prefix(&self.root).unwrap_or(dir);
        let prefix = if relative.as_os_str().is_empty() {
            String::new()
        } else {
            format!("{}/", relative.to_string_lossy().replace('\\', "/"))
        };
        let mut added = false;
        for filename in [".gitignore", ".ignore", ".fdignore"] {
            let ignore_path = dir.join(filename);
            let content = match std::fs::read_to_string(&ignore_path) {
                Ok(content) => content,
                Err(error) if error.kind() == std::io::ErrorKind::NotFound => continue,
                Err(error) => {
                    diagnostics.push(ResourceDiagnostic::Warning {
                        message: format!("ignore file not read: {error}"),
                        path: Some(ignore_path.display().to_string()),
                    });
                    continue;
                }
            };
            for pattern in content
                .lines()
                .filter_map(|line| prefix_ignore_pattern(line, &prefix))
            {
                match self.builder.add_line(Some(ignore_path.clone()), &pattern) {
                    Ok(_) => added = true,
                    Err(error) => diagnostics.push(ResourceDiagnostic::Warning {
                        message: format!("ignore rule \"{pattern}\" not used: {error}"),
                        path: Some(ignore_path.display().to_string()),
                    }),
                }
            }
        }
        if !added {
            return;
        }
        match self.builder.build() {
            Ok(matcher) => self.matcher = matcher,
            Err(error) => diagnostics.push(ResourceDiagnostic::Warning {
                message: format!("ignore rules not used: {error}"),
                path: Some(dir.display().to_string()),
            }),
        }
    }

    fn ignores(&self, rel_path: &str, is_dir: bool) -> bool {
        matches!(
            self.matcher.matched(rel_path, is_dir),
            ignore::Match::Ignore(_)
        )
    }
}

fn prefix_ignore_pattern(line: &str, prefix: &str) -> Option<String> {
    let trimmed = line.trim();
    if trimmed.is_empty() {
        return None;
    }
    if trimmed.starts_with('#') && !trimmed.starts_with("\\#") {
        return None;
    }
    let mut pattern = line.to_string();
    let mut negated = false;
    if pattern.starts_with('!') {
        negated = true;
        pattern = pattern[1..].to_string();
    } else if pattern.starts_with("\\!") {
        pattern = pattern[1..].to_string();
    }
    if pattern.starts_with('/') {
        pattern = pattern[1..].to_string();
    }
    let prefixed = format!("{prefix}{pattern}");
    Some(if negated {
        format!("!{prefixed}")
    } else {
        prefixed
    })
}

pub struct LoadSkillsFromDirResult {
    pub skills: Vec<Skill>,
    pub diagnostics: Vec<ResourceDiagnostic>,
}

/// Discovery rules:
/// - a directory containing SKILL.md is a skill root; no further recursion
/// - otherwise direct .md children of the root count as skills
/// - recurse into subdirectories looking for SKILL.md
#[must_use]
pub fn load_skills_from_dir(dir: &Path, source: &str) -> LoadSkillsFromDirResult {
    let state = DiscoveryState {
        root: dir.to_path_buf(),
        builder: GitignoreBuilder::new(dir),
        matcher: Gitignore::empty(),
    };
    load_skills_from_dir_internal(dir, source, true, state).0
}

/// The path of `path` under the discovery root, with `/` separators (the
/// form the ignore rules match).
fn relative_to(path: &Path, root: &Path) -> String {
    path.strip_prefix(root)
        .unwrap_or(path)
        .to_string_lossy()
        .replace('\\', "/")
}

fn load_skills_from_dir_internal(
    dir: &Path,
    source: &str,
    include_root_files: bool,
    mut state: DiscoveryState,
) -> (LoadSkillsFromDirResult, DiscoveryState) {
    let mut result = LoadSkillsFromDirResult {
        skills: Vec::new(),
        diagnostics: Vec::new(),
    };
    if !dir.is_dir() {
        return (result, state);
    }
    state.add_ignore_rules(dir, &mut result.diagnostics);

    let entries = match std::fs::read_dir(dir) {
        Ok(entries) => entries,
        Err(error) => {
            result.diagnostics.push(ResourceDiagnostic::Warning {
                message: format!("skill directory not read: {error}"),
                path: Some(dir.display().to_string()),
            });
            return (result, state);
        }
    };
    // Each entry: its name, its path, and its metadata (links followed).
    let mut children = Vec::new();
    for entry in entries {
        match entry {
            Ok(entry) => {
                let path = entry.path();
                let metadata = std::fs::metadata(&path);
                children.push((
                    entry.file_name().to_string_lossy().to_string(),
                    path,
                    metadata,
                ));
            }
            Err(error) => result.diagnostics.push(ResourceDiagnostic::Warning {
                message: format!("skill directory entry not read: {error}"),
                path: Some(dir.display().to_string()),
            }),
        }
    }
    // SKILL.md in this directory: stop after loading it.
    if let Some((_, path, metadata)) = children.iter().find(|(name, ..)| name == "SKILL.md") {
        if !state.ignores(&relative_to(path, &state.root), false) {
            match metadata {
                Ok(metadata) if metadata.is_file() => {
                    let (skill, file_diagnostics) = load_skill_from_file(path, source);
                    result.skills.extend(skill);
                    result.diagnostics.extend(file_diagnostics);
                }
                // A directory named SKILL.md is no skill file.
                Ok(_) => {}
                Err(error) => result.diagnostics.push(ResourceDiagnostic::Warning {
                    message: format!("skill file not read: {error}"),
                    path: Some(path.display().to_string()),
                }),
            }
        }
        return (result, state);
    }

    for (name, path, metadata) in children {
        if name.starts_with('.') || name == "node_modules" {
            continue;
        }
        let rel = relative_to(&path, &state.root);
        let metadata = match metadata {
            Ok(metadata) => metadata,
            Err(error) => {
                if !state.ignores(&rel, false) {
                    result.diagnostics.push(ResourceDiagnostic::Warning {
                        message: format!("skill entry not read: {error}"),
                        path: Some(path.display().to_string()),
                    });
                }
                continue;
            }
        };
        let is_dir = metadata.is_dir();
        let ignore_path = if is_dir { format!("{rel}/") } else { rel };
        if state.ignores(&ignore_path, is_dir) {
            continue;
        }
        if is_dir {
            // Recurse: children inherit this dir's ignore rules; sibling
            // directories see rules children discovered too (TS shares one ig).
            let (sub, returned) = load_skills_from_dir_internal(&path, source, false, state);
            state = returned;
            result.skills.extend(sub.skills);
            result.diagnostics.extend(sub.diagnostics);
            continue;
        }
        if !metadata.is_file() || !include_root_files || !skill_markdown_name(&name) {
            continue;
        }
        let (skill, file_diagnostics) = load_skill_from_file(&path, source);
        result.skills.extend(skill);
        result.diagnostics.extend(file_diagnostics);
    }
    (result, state)
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Every skill file or ignore rule that fails is a diagnostic with its
    /// path and the error text. Before, the unreadable ignore file, the bad rule,
    /// the invalid frontmatter, and the dangling link were dropped without
    /// a word.
    #[cfg(unix)]
    #[test]
    fn reports_each_skill_file_and_ignore_rule_that_fails() {
        let tmp = tempfile::tempdir().unwrap();
        let root = tmp.path();
        let skill = |name: &str, content: &[u8]| {
            std::fs::create_dir_all(root.join(name)).unwrap();
            std::fs::write(root.join(name).join("SKILL.md"), content).unwrap();
        };
        skill(
            "good",
            b"---\nname: good\ndescription: A good skill\n---\nbody",
        );
        skill("binary", &[0xff, 0xfe, 0x00]);
        let malformed = "---\nname: malformed\ndescription: [x\n---\nbody";
        skill("malformed", malformed.as_bytes());
        std::fs::create_dir_all(root.join("dangling")).unwrap();
        std::os::unix::fs::symlink(root.join("gone.md"), root.join("dangling").join("SKILL.md"))
            .unwrap();
        std::fs::write(root.join(".ignore"), "a{b\n").unwrap();
        std::fs::create_dir_all(root.join("sub")).unwrap();
        std::fs::write(root.join("sub").join(".gitignore"), [0xff, 0xfe]).unwrap();

        let result = load_skills_from_dir(root, "user");
        let names: Vec<&str> = result.skills.iter().map(|s| s.name.as_str()).collect();
        assert_eq!(names, ["good"]);
        let warning = |path: PathBuf, message: String| ResourceDiagnostic::Warning {
            message,
            path: Some(path.display().to_string()),
        };
        let rule_error = GitignoreBuilder::new(root)
            .add_line(None, "a{b")
            .unwrap_err()
            .to_string();
        let mut diagnostics = result.diagnostics;
        diagnostics.sort_by_key(|diagnostic| format!("{diagnostic:?}"));
        let mut expected = vec![
            warning(
                root.join(".ignore"),
                format!("ignore rule \"a{{b\" not used: {rule_error}"),
            ),
            warning(
                root.join("sub").join(".gitignore"),
                "ignore file not read: stream did not contain valid UTF-8".to_owned(),
            ),
            warning(
                root.join("binary").join("SKILL.md"),
                "stream did not contain valid UTF-8".to_owned(),
            ),
            warning(
                root.join("malformed").join("SKILL.md"),
                parse_frontmatter(malformed).unwrap_err(),
            ),
            warning(
                root.join("dangling").join("SKILL.md"),
                "skill file not read: No such file or directory (os error 2)".to_owned(),
            ),
        ];
        expected.sort_by_key(|diagnostic| format!("{diagnostic:?}"));
        assert_eq!(diagnostics, expected);
    }
}
