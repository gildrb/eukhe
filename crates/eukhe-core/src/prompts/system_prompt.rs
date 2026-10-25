//! Layered system-prompt assembly: static layer files first (cacheable),
//! every session-specific value last. See the parent module docs.

use std::borrow::Cow;
use std::path::PathBuf;

use crate::skills::{format_skills_for_prompt, Skill};

use super::layers;

/// The bundled skill the refinement trigger guidance keys on.
pub const REFINE_SKILL_NAME: &str = "refine";

/// Whether a prompt segment belongs to the cache-stable prefix or the
/// session-specific tail.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SegmentKind {
    /// Cacheable static prefix content (layer files, or a user replacement).
    Static,
    /// Session-specific tail content; must never leak into [`SegmentKind::Static`].
    Dynamic,
}

/// One named slice of the assembled prompt.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PromptSegment {
    /// Stable segment name (`core`, `usage`, `packages`, `environment`, ...).
    pub name: &'static str,
    pub kind: SegmentKind,
    /// Provenance: the layer file, or what generated the segment. A user
    /// prompt names its flag or its file path.
    pub source: Cow<'static, str>,
    pub text: String,
}

impl PromptSegment {
    fn static_segment(
        name: &'static str,
        source: impl Into<Cow<'static, str>>,
        text: String,
    ) -> Self {
        Self {
            name,
            kind: SegmentKind::Static,
            source: source.into(),
            text,
        }
    }

    fn dynamic_segment(
        name: &'static str,
        source: impl Into<Cow<'static, str>>,
        text: String,
    ) -> Self {
        Self {
            name,
            kind: SegmentKind::Dynamic,
            source: source.into(),
            text,
        }
    }
}

/// The origin of system prompt text that the user gave.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum PromptOrigin {
    /// Text in this flag (`--system-prompt` or `--append-system-prompt`).
    Flag(&'static str),
    /// Text from this file. The file is the argument of
    /// `--system-prompt-file` or `--append-system-prompt-file`, or a
    /// discovered `SYSTEM.md` or `APPEND_SYSTEM.md`.
    File(PathBuf),
}

impl std::fmt::Display for PromptOrigin {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            PromptOrigin::Flag(flag) => f.write_str(flag),
            PromptOrigin::File(path) => write!(f, "{}", path.display()),
        }
    }
}

/// System prompt text that the user gave, with its origin.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SourcedPrompt {
    pub origin: PromptOrigin,
    pub text: String,
}

/// The assembled prompt plus its per-layer breakdown. `cached_prefix_len` is
/// the byte length of the static prefix: `assembled[..cached_prefix_len]` is
/// byte-identical across every session that shares the same custom-prompt
/// and model-selection inputs.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SystemPromptBreakdown {
    pub segments: Vec<PromptSegment>,
    pub assembled: String,
    pub cached_prefix_len: usize,
}

/// Inputs for one session's prompt. Static inputs (`custom_prompt`,
/// `model_prompt_extras`, `memory`) select the cached prefix; everything
/// else feeds the dynamic tail.
#[derive(Debug, Default)]
pub struct BuildSystemPromptOptions<'a> {
    /// Replaces the layered static prefix with user text. The dynamic tail
    /// still applies. The `custom` segment names its origin.
    pub custom_prompt: Option<SourcedPrompt>,
    /// The per-model additions resolved for the session's model
    /// (`model_prompts::load_model_prompts`); the last cached segment.
    pub model_prompt_extras: Option<&'a str>,
    /// Whether the resolved model accepts image input, when known.
    pub vision_capable: Option<bool>,
    /// Active tools. Tool schemas carry tool descriptions outside the prompt.
    pub selected_tools: Option<Vec<&'a str>>,
    /// Additional guideline bullets appended to the dynamic tail.
    pub prompt_guidelines: Option<Vec<String>>,
    /// Texts appended to the end of the prompt, in order. The
    /// `appended-prompt` segment names their origins.
    pub append_system_prompt: Vec<SourcedPrompt>,
    /// Working directory.
    pub cwd: String,
    /// Conversation log path.
    pub messages_path: Option<String>,
    /// Pre-loaded context files (path, content).
    pub context_files: Vec<(String, String)>,
    /// Pre-loaded skills.
    pub skills: Vec<Skill>,
    /// Whether to include the subagent surface in this session.
    pub allow_recursion: Option<bool>,
    /// Fixed recursive-agent depth for this session.
    pub rlm_depth: Option<u32>,
    /// Human-readable parent name or id for child communication doctrine.
    pub rlm_parent_agent: Option<&'a str>,
    /// Whether the session has no RLM child runtime (no daemon to spawn through).
    pub daemonless: bool,
    /// Enabled user-configured generic MCP servers.
    pub generic_mcp_servers: Vec<String>,
    /// The session's side of the chat memory: adds its static layer (how
    /// to read and navigate the view) and keeps volatile dates out of the
    /// prompt. A static input like `model_prompt_extras`, never derived
    /// from the depth.
    pub memory: Option<crate::memory::MemoryRole>,
    /// The session's part in the `main-worker` shape: main's and the
    /// worker's memory layers carry their doctrine.
    pub shape_role: ShapeRole,
}

/// A session's part in the `main-worker` shape (docs/usage.md).
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub enum ShapeRole {
    /// Not part of it: a `single` session, or any other child.
    #[default]
    Alone,
    /// Main: talks with the user and routes each message by tool.
    Main,
    /// Main's worker: does the work.
    Worker,
}

/// Build the system prompt (assembled text only).
#[must_use]
pub fn build_system_prompt(options: &BuildSystemPromptOptions) -> String {
    system_prompt_breakdown(options).assembled
}

/// Build the system prompt with its per-layer breakdown.
pub fn system_prompt_breakdown(options: &BuildSystemPromptOptions) -> SystemPromptBreakdown {
    let mut segments: Vec<PromptSegment> = Vec::new();
    let harness_memory = match options.memory {
        Some(_) => crate::refinement::HarnessMemory::Chat,
        None => crate::refinement::HarnessMemory::Harness,
    };

    // The chat memory layer leads (`OptChat` §5: one system prompt for
    // turns and compactions, the user's instructions after it). It is
    // static and survives a replaced prompt: the model must know how to
    // read the view either way.
    if let Some(role) = options.memory {
        segments.push(PromptSegment::static_segment(
            "memory",
            "chat memory (OptChat)",
            match (role, options.shape_role) {
                (crate::memory::MemoryRole::Root, ShapeRole::Main) => {
                    crate::memory::main_system_layer()
                }
                (crate::memory::MemoryRole::Root, ShapeRole::Alone | ShapeRole::Worker) => {
                    crate::memory::memory_system_layer()
                }
                (crate::memory::MemoryRole::Subagent, ShapeRole::Worker) => {
                    crate::memory::worker_system_layer()
                }
                (crate::memory::MemoryRole::Subagent, ShapeRole::Alone | ShapeRole::Main) => {
                    crate::memory::subagent_system_layer()
                }
            },
        ));
    }
    // The static prefix: the user's replacement prompt, or the layered
    // files rendered for the session's memory.
    let custom = options
        .custom_prompt
        .as_ref()
        .filter(|custom| !custom.text.is_empty());
    if let Some(custom) = custom {
        segments.push(PromptSegment::static_segment(
            "custom",
            custom.origin.to_string(),
            custom.text.clone(),
        ));
    } else {
        for (name, text) in layers::constant_layers(harness_memory) {
            segments.push(PromptSegment::static_segment(
                name,
                layers::layer_source(name).unwrap_or_default(),
                text,
            ));
        }
        if let Some(extras) = options.model_prompt_extras {
            segments.push(PromptSegment::static_segment(
                "model-prompts",
                layers::layer_source("model-prompts").unwrap_or_default(),
                extras.to_string(),
            ));
        }
    }
    let cached_prefix_len = segments
        .iter()
        .map(|segment| segment.text.len())
        .sum::<usize>()
        + 2 * segments.len().saturating_sub(1);

    // The dynamic tail, in fixed order: packages -> project context ->
    // skills inventory -> MCP servers -> environment -> session role ->
    // additional guidance -> appended prompt. A chat-memory session moves
    // the project context (the user's instructions files) to the very end:
    // its memory layer points the model at "the user's instructions at the
    // end of this prompt".
    let tools: Vec<&str> = options
        .selected_tools
        .clone()
        .unwrap_or_else(|| vec!["ipython"]);
    let has_ipython = tools.contains(&"ipython");
    let has_file_access = has_ipython || tools.contains(&"bash");

    segments.push(PromptSegment::dynamic_segment(
        "packages",
        "kernel bootstrap defaults",
        packages_section(),
    ));

    let context = context_files_section(&options.context_files);
    let context_segment = (!context.is_empty())
        .then(|| PromptSegment::dynamic_segment("project-context", "AGENTS.md discovery", context));
    let (context_in_order, context_last) = match harness_memory {
        crate::refinement::HarnessMemory::Harness => (context_segment, None),
        crate::refinement::HarnessMemory::Chat => (None, context_segment),
    };
    segments.extend(context_in_order);

    let visible_skills: Vec<&Skill> = options
        .skills
        .iter()
        .filter(|skill| !skill.disable_model_invocation)
        .collect();
    if has_file_access && !visible_skills.is_empty() {
        let inventory = format_skills_for_prompt(&options.skills).trim().to_string();
        segments.push(PromptSegment::dynamic_segment(
            "skills-inventory",
            "skill discovery",
            inventory,
        ));
    }

    if has_ipython {
        let mcp = format_generic_mcp_guidance(&options.generic_mcp_servers);
        if !mcp.is_empty() {
            segments.push(PromptSegment::dynamic_segment(
                "mcp-servers",
                "generic MCP settings",
                mcp,
            ));
        }
    }

    segments.push(PromptSegment::dynamic_segment(
        "environment",
        "session configuration",
        environment_section(options),
    ));

    let role = session_role_section(options, has_ipython);
    if !role.is_empty() {
        segments.push(PromptSegment::dynamic_segment(
            "session-role",
            "RLM recursion state",
            role,
        ));
    }

    let guidelines = options
        .prompt_guidelines
        .as_deref()
        .map(format_prompt_guidelines)
        .unwrap_or_default();
    if !guidelines.is_empty() {
        segments.push(PromptSegment::dynamic_segment(
            "additional-guidance",
            "prompt guidelines",
            format!("# Additional Guidance\n\n{guidelines}"),
        ));
    }

    let appended: Vec<&SourcedPrompt> = options
        .append_system_prompt
        .iter()
        .filter(|extra| !extra.text.is_empty())
        .collect();
    if !appended.is_empty() {
        segments.push(PromptSegment::dynamic_segment(
            "appended-prompt",
            appended
                .iter()
                .map(|extra| extra.origin.to_string())
                .collect::<Vec<_>>()
                .join(", "),
            appended
                .iter()
                .map(|extra| extra.text.as_str())
                .collect::<Vec<_>>()
                .join("\n\n"),
        ));
    }
    segments.extend(context_last);

    let assembled = segments
        .iter()
        .map(|segment| segment.text.as_str())
        .collect::<Vec<_>>()
        .join("\n\n");
    SystemPromptBreakdown {
        segments,
        assembled,
        cached_prefix_len,
    }
}

fn packages_section() -> String {
    use crate::kernel::bootstrap::default_rlm_extra_import_labels;
    let mut lines = vec![format!(
        "Pre-installed Python packages: {}.",
        default_rlm_extra_import_labels().join(", ")
    )];
    lines.push(
        "Install additional packages with `uv pip install <pkg>` (this is a uv-managed venv with no pip module)."
            .to_string(),
    );
    lines.join("\n")
}

fn context_files_section(context_files: &[(String, String)]) -> String {
    if context_files.is_empty() {
        return String::new();
    }
    let mut lines = vec![
        "# Project Context".to_string(),
        String::new(),
        "Project-specific instructions and guidelines:".to_string(),
        String::new(),
    ];
    for (file_path, content) in context_files {
        lines.push(format!("## {file_path}\n\n{content}"));
    }
    lines.join("\n")
}

fn environment_section(options: &BuildSystemPromptOptions) -> String {
    let cwd = options.cwd.replace('\\', "/");
    let messages_path = options
        .messages_path
        .clone()
        .unwrap_or_else(|| "not persisted".to_string())
        .replace('\\', "/");
    // A chat-memory session keeps volatile content out of the cached prompt
    // (the date changes daily); `date(id)` gives the time of any message.
    let mut lines = Vec::new();
    if options.memory.is_none() {
        lines.push(format!("Current date: {}", today()));
    }
    lines.push(format!("Working directory: {cwd}"));
    // A chat-memory session names the chat log, the same in every session
    // (a per-session path would break the cached prefix across sessions).
    if options.memory.is_some() {
        lines.push(format!("Chat log: {messages_path}"));
    } else {
        lines.push(format!("Conversation log: {messages_path}"));
    }
    match options.vision_capable {
        Some(true) => lines.push(
            "Image input: this model can see images; `attach_image` loads them into context."
                .to_string(),
        ),
        Some(false) => lines.push(
            "Image input: this model cannot see images; `attach_image` errors for it.".to_string(),
        ),
        None => {}
    }
    lines.join("\n")
}

fn session_role_section(options: &BuildSystemPromptOptions, has_ipython: bool) -> String {
    let depth = options.rlm_depth.unwrap_or(0);
    let mut lines = vec![format!(
        "Recursive agent depth: {depth}{}",
        if depth == 0 { " (root)" } else { " (not root)" }
    )];
    if options.daemonless {
        lines.push(
            "Subagents and completion notifications are unavailable in this session (no daemon): rlm.spawn will error, and nothing wakes you after your turn ends, so await background commands before ending it. Plan to do all work yourself."
                .to_string(),
        );
    }
    if !has_ipython {
        lines.push(
            "This session has no Python REPL (`ipython` tool): the programmatic tools described above are unavailable here."
                .to_string(),
        );
    }
    if options.allow_recursion == Some(false) {
        lines.push("Subagent spawning is disabled in this session.".to_string());
    }
    if depth > 0 {
        lines.push(format!(
            "You are a child agent spawned by {}. Task prompts are labeled `[task from parent]`.",
            options.rlm_parent_agent.unwrap_or("your parent agent")
        ));
        if has_ipython {
            lines.push(
                "When a task calls for an answer, reply explicitly with `await agent_message.send(message, receiver_role=\"parent\")`. Not every message or task needs a reply; continue cleanup after sending and go idle normally.".to_string(),
            );
            lines.push(
                "For long-running work, report brief progress with `await rlm.progress_note('...')` (at most 512 characters, throttled to about one note per 10 seconds); the parent sees notes without needing a reply.".to_string(),
            );
        }
    }
    lines.join("\n")
}

pub(crate) fn today() -> String {
    // UTC date in YYYY-MM-DD form; the prompt is date context only.
    let days = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .map_or(0, |duration| duration.as_secs() / 86_400);
    // Civil-from-days algorithm (Howard Hinnant).
    let z = days as i64 + 719_468;
    let era = if z >= 0 { z } else { z - 146_096 } / 146_097;
    let doe = z - era * 146_097;
    let yoe = (doe - doe / 1460 + doe / 36_524 - doe / 146_096) / 365;
    let y = yoe + era * 400;
    let doy = doe - (365 * yoe + yoe / 4 - yoe / 100);
    let mp = (5 * doy + 2) / 153;
    let d = doy - (153 * mp + 2) / 5 + 1;
    let m = if mp < 10 { mp + 3 } else { mp - 9 };
    let y = if m <= 2 { y + 1 } else { y };
    format!("{y:04}-{m:02}-{d:02}")
}

fn format_prompt_guidelines(guidelines: &[String]) -> String {
    let mut seen = std::collections::HashSet::new();
    let mut list = Vec::new();
    for guideline in guidelines {
        let normalized = guideline.trim();
        if !normalized.is_empty() && seen.insert(normalized.to_string()) {
            list.push(format!("- {normalized}"));
        }
    }
    list.join("\n")
}

fn format_generic_mcp_guidance(servers: &[String]) -> String {
    let mut enabled: Vec<&String> = Vec::new();
    let mut seen = std::collections::HashSet::new();
    for server in servers {
        if seen.insert(server) {
            enabled.push(server);
        }
    }
    enabled.sort();
    if enabled.is_empty() {
        return String::new();
    }
    let mut lines = vec![
        "# Generic MCP Connections".to_string(),
        String::new(),
        "Generic MCP connections are accessed through the pre-imported Python `mcp` object in the Python REPL, not as top-level native tool namespaces or installed Python skills.".to_string(),
        format!(
            "Enabled generic MCP servers: {}.",
            enabled
                .iter()
                .map(|server| format!("`{server}`"))
                .collect::<Vec<_>>()
                .join(", ")
        ),
    ];
    for server in &enabled {
        lines.push(format!(
            "For `{server}`, first discover its tools with `await mcp.list_tools(\"{server}\")`, then call one with `await mcp.call_tool(\"{server}\", \"<tool>\", arguments)`."
        ));
    }
    lines.join("\n")
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::skills::{create_synthetic_source_info, SkillKind, SourceScope};
    use std::path::PathBuf;

    fn skill(name: &str, import: Option<&str>) -> Skill {
        Skill {
            name: name.to_string(),
            description: format!("Skill {name}"),
            file_path: PathBuf::from("/skills/SKILL.md"),
            base_dir: PathBuf::from("/skills"),
            source_info: create_synthetic_source_info("/skills", "user", SourceScope::User, None),
            disable_model_invocation: false,
            kind: if import.is_some() {
                SkillKind::Python
            } else {
                SkillKind::Markdown
            },
            python: import.map(|import_name| crate::skills::SkillPythonMetadata {
                import_name: import_name.to_string(),
                package_path: PathBuf::from("/skills"),
                pyproject_path: PathBuf::from("/skills/pyproject.toml"),
            }),
        }
    }

    fn base_options() -> BuildSystemPromptOptions<'static> {
        BuildSystemPromptOptions {
            cwd: "/w".to_string(),
            messages_path: Some("/log.jsonl".to_string()),
            skills: vec![
                skill("compact", Some("compact")),
                skill("refine", Some("refine")),
                skill("agent-message", Some("agent_message")),
            ],
            ..Default::default()
        }
    }

    #[test]
    fn default_prompt_is_layered_with_static_prefix_first() {
        let breakdown = system_prompt_breakdown(&base_options());
        let prompt = &breakdown.assembled;
        // Static layers lead, in order.
        assert!(prompt.starts_with("# eukhe harness"));
        assert_eq!(breakdown.segments[0].kind, SegmentKind::Static);
        assert_eq!(breakdown.segments[0].name, "core");
        let names: Vec<&str> = breakdown
            .segments
            .iter()
            .map(|segment| segment.name)
            .collect();
        assert_eq!(
            names[..4],
            ["core", "usage", "opinionated", "packages"],
            "core/usage/opinionated layers, then the dynamic tail"
        );
        // The cached prefix is exactly the static segments.
        assert_eq!(
            &prompt[..breakdown.cached_prefix_len],
            layers::static_prefix(crate::refinement::HarnessMemory::Harness)
        );
        // Dynamic values live strictly after the prefix.
        let tail = &prompt[breakdown.cached_prefix_len..];
        assert!(tail.contains("Working directory: /w"));
        assert!(tail.contains("Conversation log: /log.jsonl"));
        assert!(tail.contains("<available_skills>"));
        assert!(tail.contains("Recursive agent depth: 0 (root)"));
        assert!(tail.contains("Pre-installed Python packages: requests, httpx,"));
    }

    /// A chat-memory session's prompt (`OptChat` §3.3, §5): the memory layer
    /// first, then the harness layers rendered for chat memory, then the
    /// dynamic tail, and the user's instructions files last; no date, so
    /// every call of the session sends the same bytes.
    #[test]
    fn chat_memory_prompt_leads_with_memory_and_ends_with_the_user_instructions() {
        let mut options = base_options();
        options.memory = Some(crate::memory::MemoryRole::Root);
        options.context_files = vec![("AGENTS.md".to_string(), "Rule one.".to_string())];
        options.append_system_prompt = vec![SourcedPrompt {
            origin: PromptOrigin::Flag("--append-system-prompt"),
            text: "Appended.".to_string(),
        }];
        let breakdown = system_prompt_breakdown(&options);
        let names: Vec<&str> = breakdown
            .segments
            .iter()
            .map(|segment| segment.name)
            .collect();
        assert_eq!(
            names,
            [
                "memory",
                "core",
                "usage",
                "opinionated",
                "packages",
                "skills-inventory",
                "environment",
                "session-role",
                "appended-prompt",
                "project-context",
            ]
        );
        let prompt = &breakdown.assembled;
        assert!(prompt.starts_with(&crate::memory::memory_system_layer()));
        assert!(prompt.ends_with("## AGENTS.md\n\nRule one."));
        assert_eq!(
            &prompt[..breakdown.cached_prefix_len],
            format!(
                "{}\n\n{}",
                crate::memory::memory_system_layer(),
                layers::static_prefix(crate::refinement::HarnessMemory::Chat)
            )
        );
        assert!(!prompt.contains("Current date:"));
        assert_eq!(build_system_prompt(&options), *prompt);
    }

    #[test]
    fn dynamic_tail_isolates_the_cached_prefix() {
        let mut other = base_options();
        other.cwd = "/somewhere/else".to_string();
        other.messages_path = None;
        other.rlm_depth = Some(2);
        other.rlm_parent_agent = Some("the lead");
        other.generic_mcp_servers = vec!["slack".to_string()];
        other.context_files = vec![("AGENTS.md".to_string(), "Rule one.".to_string())];
        let left = system_prompt_breakdown(&base_options());
        let right = system_prompt_breakdown(&other);
        // Different sessions share one byte-identical cacheable prefix.
        assert_eq!(
            left.assembled[..left.cached_prefix_len],
            right.assembled[..right.cached_prefix_len]
        );
        assert_eq!(left.cached_prefix_len, right.cached_prefix_len);
        // And the tails differ in the session-specific values.
        assert!(right.assembled[right.cached_prefix_len..]
            .contains("Enabled generic MCP servers: `slack`"));
        assert!(right.assembled[right.cached_prefix_len..]
            .contains("You are a child agent spawned by the lead."));
    }

    #[test]
    fn custom_prompt_replaces_layers_keeps_tail() {
        let mut options = base_options();
        options.custom_prompt = Some(SourcedPrompt {
            origin: PromptOrigin::Flag("--system-prompt"),
            text: "Be terse.".to_string(),
        });
        options.model_prompt_extras = Some("Tier-2 guidance.");
        options.context_files = vec![("AGENTS.md".to_string(), "Rule one.".to_string())];
        let breakdown = system_prompt_breakdown(&options);
        let prompt = &breakdown.assembled;
        assert!(prompt.starts_with("Be terse."));
        assert_eq!(breakdown.segments[0].name, "custom");
        assert!(prompt.contains("## AGENTS.md\n\nRule one."));
        assert!(prompt.contains("Working directory: /w"));
        assert!(prompt.contains("Current date: "));
        // The layered defaults are gone.
        assert!(!prompt.contains("# eukhe harness"));
        assert!(!prompt.contains("Tier-2 guidance."));
    }

    /// The user prompt segments name their origin: the file path, or the
    /// flag that held the text.
    #[test]
    fn user_prompt_segments_name_their_origin() {
        let mut options = base_options();
        options.custom_prompt = Some(SourcedPrompt {
            origin: PromptOrigin::File(PathBuf::from("/p/.eukhe/SYSTEM.md")),
            text: "Be terse.".to_string(),
        });
        options.append_system_prompt = vec![
            SourcedPrompt {
                origin: PromptOrigin::Flag("--append-system-prompt"),
                text: "One.".to_string(),
            },
            SourcedPrompt {
                origin: PromptOrigin::File(PathBuf::from("/notes/extra.md")),
                text: "Two.".to_string(),
            },
        ];
        let breakdown = system_prompt_breakdown(&options);
        let user_segments: Vec<&PromptSegment> = breakdown
            .segments
            .iter()
            .filter(|segment| matches!(segment.name, "custom" | "appended-prompt"))
            .collect();
        assert_eq!(
            user_segments,
            [
                &PromptSegment {
                    name: "custom",
                    kind: SegmentKind::Static,
                    source: Cow::Borrowed("/p/.eukhe/SYSTEM.md"),
                    text: "Be terse.".to_string(),
                },
                &PromptSegment {
                    name: "appended-prompt",
                    kind: SegmentKind::Dynamic,
                    source: Cow::Borrowed("--append-system-prompt, /notes/extra.md"),
                    text: "One.\n\nTwo.".to_string(),
                },
            ]
        );
    }

    #[test]
    fn mcp_and_guidelines_are_tail_segments() {
        let mut options = base_options();
        options.generic_mcp_servers = vec!["t".to_string(), "t".to_string()];
        options.prompt_guidelines = Some(vec!["be careful".to_string(), "be careful".to_string()]);
        let breakdown = system_prompt_breakdown(&options);
        let names: Vec<&str> = breakdown
            .segments
            .iter()
            .map(|segment| segment.name)
            .collect();
        assert!(names.contains(&"mcp-servers"));
        assert!(names.contains(&"additional-guidance"));
        assert!(breakdown.assembled.contains("# Generic MCP Connections"));
        assert!(breakdown
            .assembled
            .contains("Enabled generic MCP servers: `t`."));
        assert!(breakdown
            .assembled
            .contains("# Additional Guidance\n\n- be careful"));
    }

    #[test]
    fn model_prompt_extras_form_the_last_static_segment() {
        let mut options = base_options();
        options.model_prompt_extras = Some("Tier-2 guidance.");
        let breakdown = system_prompt_breakdown(&options);
        let names: Vec<&str> = breakdown
            .segments
            .iter()
            .map(|segment| segment.name)
            .collect();
        assert_eq!(
            names[..5],
            ["core", "usage", "opinionated", "model-prompts", "packages"],
            "extras are the last static segment, directly before the dynamic tail"
        );
        assert!(breakdown.assembled[..breakdown.cached_prefix_len].ends_with("Tier-2 guidance."));
    }

    #[test]
    fn daemonless_sessions_are_told_subagents_and_wake_ups_are_unavailable() {
        let notice = "Subagents and completion notifications are unavailable in this session";
        let breakdown = system_prompt_breakdown(&base_options());
        assert!(!breakdown.assembled.contains(notice));
        let mut options = base_options();
        options.daemonless = true;
        let breakdown = system_prompt_breakdown(&options);
        let tail = &breakdown.assembled[breakdown.cached_prefix_len..];
        assert!(tail.contains(notice));
    }
}
