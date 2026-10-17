//! Port of pi-durable `codemode/describe.ts`: the code mode tool's
//! description and the `codemode` system prompt section listing the tools
//! scripts can call.

use std::cmp::Ordering;
use std::collections::{HashSet, VecDeque};
use std::sync::Arc;

use indexmap::IndexMap;
use serde_json::json;

use super::declarations::{render_tool_sample, CodemodeToolDeclaration};
use super::identifier::to_codemode_identifier;
use super::models::{ClassifierDefault, CLASSIFIER_DEFAULT_DESCRIPTION, MODELS_DESCRIPTION};
use crate::harness::types::ToolRegistration;

/// Default token budget of the tool declarations in the `codemode`
/// section, as in the coding agent.
pub const DEFAULT_CODEMODE_INLINE_BUDGET: usize = 3000;
/// Characters per token when estimating the cost of a tool section.
const CHARS_PER_TOKEN: usize = 4;

const DESCRIPTION_INTRO: &str = "Run JavaScript that calls other tools. The input is raw JavaScript (not JSON, no code fence), run as an async function body in a QuickJS sandbox: top-level `await` and `return` work. No Node, file system, network, or timers.
- `await tools.<name>({ ...args })` resolves to a string, or an object if the tool's declaration says so, and rejects with an Error on failure. A tool whose declaration returns an object resolves on failure too when it returned that object; check its fields. Calls still running when the script ends are cancelled.
- The script survives a restart: it resumes where it was, without running finished calls again.
- Optional first line: `// @options: {\"max_output_tokens\": 10000, \"timeout_ms\": 60000}`";

const GLOBALS: [&str; 4] = [
    "Globals:",
    "- `text(value)`, `image(dataUrlOrImageBlock)`, `console.log(...)`, and top-level `return` add output; `exit()` ends the script. With several text items, each starts with a `==> text N/M <==` line, and `console` lines follow the other output in one `<console_output>` block. `image()` also saves the image to a temp file and the result names its path.",
    "- `store(key, value)` and `load(key)` keep JSON values across codemode calls.",
    "- `ALL_TOOLS`, `await searchTools(query, { limit?, namespace? })`, `await describeTool(name)`, `await describeNamespace(name)`: find tools the `codemode` section does not list.",
];

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
    let globals = GLOBALS.join("\n");
    let models_section = match (models, classifier) {
        (CodemodeModels::Included, ClassifierDefault::Unset) => Some(MODELS_DESCRIPTION.to_owned()),
        (CodemodeModels::Included, ClassifierDefault::Resolver(_)) => Some(format!(
            "{MODELS_DESCRIPTION}\n{CLASSIFIER_DEFAULT_DESCRIPTION}"
        )),
        (CodemodeModels::Excluded, ClassifierDefault::Unset | ClassifierDefault::Resolver(_)) => {
            None
        }
    };
    let mut sections = vec![DESCRIPTION_INTRO, globals.as_str()];
    if let Some(section) = &models_section {
        sections.push(section);
    }
    sections.push(
        "The `codemode` section of the system prompt lists the tools scripts can call, by namespace, as far as space allows.",
    );
    sections.join("\n\n")
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

/// The namespace of a tool: the one with the longest prefix its name
/// starts with; of equally long prefixes, the first.
#[must_use]
pub fn namespace_of<'a>(
    name: &str,
    namespaces: &'a [CodemodeNamespace],
) -> Option<&'a CodemodeNamespace> {
    let mut found: Option<&CodemodeNamespace> = None;
    for namespace in namespaces {
        if name.starts_with(&namespace.prefix)
            && found.is_none_or(|current| utf16_len(&namespace.prefix) > utf16_len(&current.prefix))
        {
            found = Some(namespace);
        }
    }
    found
}

fn utf16_len(text: &str) -> usize {
    text.encode_utf16().count()
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

/// JS `a.localeCompare(b)`, approximated: case-insensitive first, then
/// lowercase before uppercase as ICU's tertiary strength orders them. ICU
/// also weighs accents and punctuation differently; namespace names are
/// expected to be plain words.
fn locale_compare(left: &str, right: &str) -> Ordering {
    left.to_lowercase()
        .cmp(&right.to_lowercase())
        .then_with(|| right.cmp(left))
}

struct Entry {
    name: String,
    section: String,
    cost: usize,
}

struct Group<'a> {
    namespace: Option<&'a CodemodeNamespace>,
    entries: Vec<Entry>,
}

/// Pick the tool sections that fit the budget: in each round every group
/// (tools without a namespace first, then namespaces by name) places its
/// cheapest remaining tool; a group whose next tool does not fit drops out
/// while the others continue. Every namespace is represented before any
/// namespace is complete.
fn select_catalog<'g>(groups: &'g [Group<'_>], budget: usize) -> HashSet<&'g str> {
    let mut queues: Vec<VecDeque<&Entry>> = groups
        .iter()
        .map(|group| {
            let mut queue: Vec<&Entry> = group.entries.iter().collect();
            queue.sort_by_key(|entry| entry.cost);
            VecDeque::from(queue)
        })
        .filter(|queue| !queue.is_empty())
        .collect();
    let mut shown = HashSet::new();
    let mut remaining = budget;
    while !queues.is_empty() {
        queues.retain_mut(|queue| {
            let Some(next) = queue.front() else {
                return false;
            };
            if next.cost > remaining {
                return false;
            }
            remaining -= next.cost;
            shown.insert(next.name.as_str());
            queue.pop_front();
            !queue.is_empty()
        });
    }
    shown
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
    if tools.is_empty() {
        return None;
    }
    let mut groups: IndexMap<String, Group<'_>> = IndexMap::new();
    groups.insert(
        String::new(),
        Group {
            namespace: None,
            entries: Vec::new(),
        },
    );
    for tool in tools {
        let namespace = namespace_of(&tool.name, namespaces);
        let key = namespace.map_or_else(String::new, |namespace| format!("ns:{}", namespace.name));
        let group = groups.entry(key).or_insert_with(|| Group {
            namespace,
            entries: Vec::new(),
        });
        let section = render_tool_section(tool);
        let cost = utf16_len(&section).div_ceil(CHARS_PER_TOKEN);
        group.entries.push(Entry {
            name: tool.name.clone(),
            section,
            cost,
        });
    }
    let mut ordered: Vec<Group<'_>> = groups.into_values().collect();
    ordered.sort_by(|a, b| match (a.namespace, b.namespace) {
        (None, _) => Ordering::Less,
        (Some(_), None) => Ordering::Greater,
        (Some(a), Some(b)) => locale_compare(&a.name, &b.name),
    });
    let shown = select_catalog(&ordered, budget);
    let mut tool_sections = vec!["Tools scripts can call (`await tools.<name>(args)`):".to_owned()];
    for Group { namespace, entries } in &ordered {
        if entries.is_empty() {
            continue;
        }
        let visible: Vec<&Entry> = entries
            .iter()
            .filter(|entry| shown.contains(entry.name.as_str()))
            .collect();
        match namespace {
            Some(namespace) => {
                let listing = if visible.len() == entries.len() {
                    ""
                } else if visible.is_empty() {
                    " (tools not listed)"
                } else {
                    " (some tools not listed)"
                };
                let description = namespace.description.as_deref().map_or("", str::trim);
                let description = if description.is_empty() {
                    String::new()
                } else {
                    format!("\n{description}")
                };
                tool_sections.push(format!("## {}{listing}{description}", namespace.name));
            }
            None if visible.len() < entries.len() => {
                tool_sections
                    .push("Some tools are not listed: find them with `searchTools()`.".to_owned());
            }
            None => {}
        }
        tool_sections.extend(visible.iter().map(|entry| entry.section.clone()));
    }
    Some(tool_sections.join("\n\n"))
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
    fn description_adds_models_section() {
        let without = codemode_description(CodemodeModels::Excluded, &ClassifierDefault::Unset);
        let with = codemode_description(CodemodeModels::Included, &ClassifierDefault::Unset);
        let resolver: crate::codemode::ClassifierResolver =
            Arc::new(|_, _| Box::pin(async { Err("none".to_owned()) }));
        let with_default = codemode_description(
            CodemodeModels::Included,
            &ClassifierDefault::Resolver(resolver),
        );
        let (head, tail) = without.rsplit_once("\n\n").expect("sections");
        assert_eq!(
            (with, with_default),
            (
                format!("{head}\n\n{MODELS_DESCRIPTION}\n\n{tail}"),
                format!(
                    "{head}\n\n{MODELS_DESCRIPTION}\n{CLASSIFIER_DEFAULT_DESCRIPTION}\n\n{tail}"
                )
            )
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
    fn namespace_is_longest_prefix() {
        let namespaces = vec![
            namespace("a", None, "mcp__"),
            namespace("b", None, "mcp__docs__"),
            namespace("c", None, "mcp__docs__"),
        ];
        assert_eq!(
            namespace_of("mcp__docs__search", &namespaces),
            Some(&namespaces[1])
        );
        assert_eq!(namespace_of("mcp__x", &namespaces), Some(&namespaces[0]));
        assert_eq!(namespace_of("read", &namespaces), None);
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

    #[test]
    fn section_without_budget_lists_no_tools() {
        assert_eq!(
            codemode_section(&tools(), &namespaces(), 0).as_deref(),
            Some(concat!(
                "Tools scripts can call (`await tools.<name>(args)`):\n\n",
                "Some tools are not listed: find them with `searchTools()`.\n\n",
                "## alpha (tools not listed)\nAlpha tools\n\n",
                "## GitHub (tools not listed)\nGitHub tools.",
            ))
        );
        assert_eq!(codemode_section(&[], &namespaces(), 100), None);
    }

    fn entry(name: &str, cost: usize) -> Entry {
        Entry {
            name: name.to_owned(),
            section: String::new(),
            cost,
        }
    }

    #[test]
    fn catalog_is_round_robin_by_cost() {
        let groups = vec![
            Group {
                namespace: None,
                entries: vec![entry("a1", 5), entry("a2", 1)],
            },
            Group {
                namespace: None,
                entries: Vec::new(),
            },
            Group {
                namespace: None,
                entries: vec![entry("b1", 3), entry("b2", 3)],
            },
        ];
        assert_eq!(
            select_catalog(&groups, 8),
            HashSet::from(["a2", "b1", "b2"])
        );
        assert_eq!(select_catalog(&groups, 3), HashSet::from(["a2"]));
    }

    #[test]
    fn some_tools_not_listed() {
        let tools = vec![
            tool("gh-a", "A"),
            tool("gh-bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb", "B"),
        ];
        let namespaces = vec![namespace("GitHub", None, "gh-")];
        let section = codemode_section(&tools, &namespaces, 40).expect("section");
        assert_eq!(
            section,
            "Tools scripts can call (`await tools.<name>(args)`):\n\n## GitHub (some tools not listed)\n\n### `gh_a` (`gh-a`)\nA\n\ncodemode tool declaration:\n```ts\ndeclare const tools: { gh_a(args: { [key: string]: unknown; }): Promise<string>; };\n```"
        );
    }
}
