//! Port of pi-durable `codemode/describe.ts`: the code mode tool's
//! description and the `codemode` system prompt section listing the tools
//! scripts can call.
//!
//! The rules run as the compiled Bend core
//! (`eukhe_bend::rules::codemode_describe`; `bend/codemode_describe.bend`,
//! `laws/codemode_describe.bend`): each tool's namespace, the groups and
//! their order, which tool sections fit the budget, every heading, marker
//! and joint of the section, and the whole description text. This module
//! renders each tool's section (its heading, description and declaration)
//! and measures it in UTF-16 units, lowercases and trims the namespaces'
//! names and descriptions, and joins the core's parts.

use std::sync::Arc;

use eukhe_bend::rules::codemode_describe::{self, Globals, Namespace, Part, Tool};
use eukhe_bend::{expect_core, Entry};
use serde_json::json;

use super::declarations::{render_tool_sample, CodemodeToolDeclaration};
use super::identifier::to_codemode_identifier;
use super::models::ClassifierDefault;
use crate::harness::types::ToolRegistration;

/// Default token budget of the tool declarations in the `codemode`
/// section, as in the coding agent.
pub const DEFAULT_CODEMODE_INLINE_BUDGET: usize = 3000;

/// Whether scripts get the `models.*` globals.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CodemodeModels {
    /// Scripts can call `models.*`; the description documents them.
    Included,
    /// No `models.*` globals.
    Excluded,
}

/// A group of tools that share a name prefix (pi-durable
/// `CodemodeNamespace`).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CodemodeNamespace {
    /// The namespace's name, its `##` heading.
    pub name: String,
    /// Shown under the heading.
    pub description: Option<String>,
    /// What `describeNamespace()` adds.
    pub instructions: Option<String>,
    /// Tools whose names start with it belong to the namespace.
    pub prefix: String,
}

/// The code mode tool's description: the script environment and its
/// globals, the same for every conversation.
#[must_use]
pub fn codemode_description(models: CodemodeModels, classifier: &ClassifierDefault) -> String {
    let globals = Globals {
        models: match models {
            CodemodeModels::Included => true,
            CodemodeModels::Excluded => false,
        },
        default_classifier: match classifier {
            ClassifierDefault::Unset => false,
            ClassifierDefault::Resolver(_) => true,
        },
    };
    expect_core(
        Entry::CodemodeDescribe,
        codemode_describe::description(globals),
    )
}

/// What a script sees of a tool: its declaration. Tools without an output
/// schema resolve to their text output.
#[must_use]
pub fn declaration_of(tool: &ToolRegistration) -> CodemodeToolDeclaration {
    CodemodeToolDeclaration {
        name: tool.name.clone(),
        description: Some(tool.description.clone()),
        input_schema: Some((*tool.parameters).clone()),
        output_schema: Some(
            tool.structured_output_schema
                .as_ref()
                .map_or_else(|| json!({"type": "string"}), |schema| (**schema).clone()),
        ),
    }
}

/// `toolSample` of a tool: its description and TypeScript declaration.
#[must_use]
pub fn sample_of(tool: &ToolRegistration) -> String {
    render_tool_sample(&declaration_of(tool))
}

/// The namespace of each tool named in `names`: the one with the longest
/// prefix the name starts with; of equally long prefixes, the first.
pub(crate) fn namespaces_of<'a>(
    names: &[&str],
    namespaces: &'a [CodemodeNamespace],
) -> Vec<Option<&'a CodemodeNamespace>> {
    let prefixes: Vec<&str> = namespaces
        .iter()
        .map(|namespace| namespace.prefix.as_str())
        .collect();
    expect_core(
        Entry::CodemodeDescribe,
        codemode_describe::namespaces(names, &prefixes),
    )
    .into_iter()
    .map(|found| found.map(|index| &namespaces[index]))
    .collect()
}

fn utf16_len(text: &str) -> u64 {
    u64::try_from(text.encode_utf16().count()).unwrap_or(u64::MAX)
}

/// A `### id (raw name)` heading (identifiers in backticks) followed by the
/// tool's description and declaration.
fn render_tool_section(tool: &ToolRegistration) -> String {
    let id = to_codemode_identifier(&tool.name);
    let heading = if id == tool.name {
        format!("### `{id}`")
    } else {
        format!("### `{id}` (`{}`)", tool.name)
    };
    format!("{heading}\n{}", sample_of(tool).trim())
}

/// The `codemode` section: the tools scripts can call, grouped by
/// namespace, with their declarations as far as the budget (tokens)
/// allows. `None` without callable tools.
#[must_use]
pub fn codemode_section(
    tools: &[Arc<ToolRegistration>],
    namespaces: &[CodemodeNamespace],
    budget: usize,
) -> Option<String> {
    let sections: Vec<String> = tools.iter().map(|tool| render_tool_section(tool)).collect();
    let facts: Vec<Tool<'_>> = tools
        .iter()
        .zip(&sections)
        .map(|(tool, section)| Tool {
            name: &tool.name,
            size: utf16_len(section),
        })
        .collect();
    let keys: Vec<String> = namespaces
        .iter()
        .map(|namespace| namespace.name.to_lowercase())
        .collect();
    let spaces: Vec<Namespace<'_>> = namespaces
        .iter()
        .zip(&keys)
        .map(|(namespace, key)| Namespace {
            name: &namespace.name,
            key,
            prefix: &namespace.prefix,
            about: namespace.description.as_deref().map_or("", str::trim),
        })
        .collect();
    let parts = expect_core(
        Entry::CodemodeDescribe,
        codemode_describe::section(&facts, &spaces, u64::try_from(budget).unwrap_or(u64::MAX)),
    )?;
    let mut text = String::new();
    for part in parts {
        match part {
            Part::Text(piece) => text.push_str(&piece),
            Part::Section(index) => text.push_str(&sections[index]),
        }
    }
    Some(text)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::harness::define::define_tool;
    use crate::harness::types::ToolExecutionResult;

    fn tool(name: &str, description: &str) -> Arc<ToolRegistration> {
        define_tool(ToolRegistration::new(
            name,
            description,
            json!({"type": "object", "properties": {}}),
            |_, _, _| async { Ok(ToolExecutionResult::default()) },
        ))
    }

    fn namespace(name: &str, description: Option<&str>, prefix: &str) -> CodemodeNamespace {
        CodemodeNamespace {
            name: name.to_owned(),
            description: description.map(str::to_owned),
            instructions: None,
            prefix: prefix.to_owned(),
        }
    }

    fn namespaces() -> Vec<CodemodeNamespace> {
        vec![
            namespace("GitHub", Some("GitHub tools."), "gh-"),
            namespace("alpha", Some("  Alpha tools  "), "ab-"),
            namespace("empty", None, "zz-"),
        ]
    }

    fn tools() -> Vec<Arc<ToolRegistration>> {
        vec![
            tool("gh-issues", "Lists issues."),
            tool("read", " Read a file.\n"),
            tool("ab-x", ""),
        ]
    }

    #[test]
    fn description_follows_models_and_classifier() {
        let resolver: crate::codemode::ClassifierResolver =
            Arc::new(|_, _| Box::pin(async { Err("none".to_owned()) }));
        let parts = |text: String| {
            (
                text.contains("`models` (all functions return promises)"),
                text.contains("the session's default classifier"),
            )
        };
        assert_eq!(
            [
                parts(codemode_description(
                    CodemodeModels::Excluded,
                    &ClassifierDefault::Unset
                )),
                parts(codemode_description(
                    CodemodeModels::Excluded,
                    &ClassifierDefault::Resolver(Arc::clone(&resolver))
                )),
                parts(codemode_description(
                    CodemodeModels::Included,
                    &ClassifierDefault::Unset
                )),
                parts(codemode_description(
                    CodemodeModels::Included,
                    &ClassifierDefault::Resolver(resolver)
                )),
            ],
            [(false, false), (false, false), (true, false), (true, true)]
        );
    }

    #[test]
    fn declaration_defaults_to_text_output() {
        let mut registration =
            ToolRegistration::new("t", "T", json!({"type": "object"}), |_, _, _| async {
                Ok(ToolExecutionResult::default())
            });
        assert_eq!(
            declaration_of(&registration),
            CodemodeToolDeclaration {
                name: "t".to_owned(),
                description: Some("T".to_owned()),
                input_schema: Some(json!({"type": "object"})),
                output_schema: Some(json!({"type": "string"})),
            }
        );
        registration.structured_output_schema = Some(json!({"type": "number"}).into());
        assert_eq!(
            sample_of(&registration),
            "T\n\ncodemode tool declaration:\n```ts\ndeclare const tools: { t(args: { [key: string]: unknown; }): Promise<number>; };\n```"
        );
    }

    #[test]
    fn section_lists_groups_in_order() {
        assert_eq!(
            codemode_section(&tools(), &namespaces(), DEFAULT_CODEMODE_INLINE_BUDGET).as_deref(),
            Some(concat!(
                "Tools scripts can call (`await tools.<name>(args)`):\n\n",
                "### `read`\nRead a file.\n\ncodemode tool declaration:\n```ts\ndeclare const tools: { read(args: { [key: string]: unknown; }): Promise<string>; };\n```\n\n",
                "## alpha\nAlpha tools\n\n",
                "### `ab_x` (`ab-x`)\ncodemode tool declaration:\n```ts\ndeclare const tools: { ab_x(args: { [key: string]: unknown; }): Promise<string>; };\n```\n\n",
                "## GitHub\nGitHub tools.\n\n",
                "### `gh_issues` (`gh-issues`)\nLists issues.\n\ncodemode tool declaration:\n```ts\ndeclare const tools: { gh_issues(args: { [key: string]: unknown; }): Promise<string>; };\n```",
            ))
        );
    }
}
