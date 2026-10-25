//! Command specs and help formatting, ported from `cli/command-registry.ts`.

use crate::config::APP_NAME;

/// A registered public command.
#[derive(Debug, Clone)]
pub struct CommandSpec {
    pub path: &'static [&'static str],
    pub usage: &'static str,
    pub summary: &'static str,
    pub description: Option<&'static str>,
    pub options: &'static [&'static str],
    pub examples: &'static [&'static str],
}

impl CommandSpec {
    const fn new(
        path: &'static [&'static str],
        usage: &'static str,
        summary: &'static str,
    ) -> Self {
        CommandSpec {
            path,
            usage,
            summary,
            description: None,
            options: &[],
            examples: &[],
        }
    }

    const fn description(mut self, description: &'static str) -> Self {
        self.description = Some(description);
        self
    }

    const fn options(mut self, options: &'static [&'static str]) -> Self {
        self.options = options;
        self
    }

    const fn examples(mut self, examples: &'static [&'static str]) -> Self {
        self.examples = examples;
        self
    }
}

/// All public command specs, in registry order.
pub const COMMAND_SPECS: &[CommandSpec] = &[
    CommandSpec::new(&["help"], "help [command]", "Show command help"),
    CommandSpec::new(&["agents"], "agents", "Search and open sessions"),
    CommandSpec::new(
        &["list"],
        "list [--all] [--json]",
        "List agents",
    )
    .options(&[
        "-a, --all  Include saved agents",
        "--json      Print JSON",
    ]),
    CommandSpec::new(
        &["sessions"],
        "sessions [--all] [--json]",
        "Show agent status, activity, and usage",
    )
    .options(&[
        "-a, --all  Include saved agents",
        "--json      Print JSON",
    ]),
    CommandSpec::new(
        &["attach"],
        "attach <agent>",
        "Attach the interactive UI to an agent",
    ),
    CommandSpec::new(&["stop"], "stop <agent> [--json]", "Stop an agent"),
    CommandSpec::new(
        &["rename"],
        "rename <agent> <name> [--json]",
        "Rename an agent",
    ),
    CommandSpec::new(
        &["state"],
        "state [<agent>] [--since <cursor>] [--follow] [--json]",
        "Show the state tree of an agent's session",
    )
    .description(
        "The state tree holds every record of the session: its conversations, entries, tasks, \
submissions, and documents. The first line is the cursor (the number of tree records); each \
node shows as its kind and its record id, indented under its parent. Without <agent>, the only \
active agent. With --follow, the command then prints each new batch of records as the session \
commits it, until Ctrl+C.",
    )
    .options(&[
        "--since <cursor>  Print the records after this cursor",
        "--follow          Keep printing the new records",
        "--json            Print JSON",
    ]),
    CommandSpec::new(
        &["state", "rewind-plan"],
        "state rewind-plan <cursor> [<agent>] [--json]",
        "Show what a rewind of the state tree to a cursor does",
    )
    .description(
        "Prints one line per node that the rewind touches: stop for a node that goes, start \
for a node that comes back, restore for a node that changes.",
    )
    .options(&["--json  Print JSON"]),
    CommandSpec::new(
        &["send"],
        "send [--from <agent>] <agent> <message>",
        "Send a message to an agent",
    )
    .options(&[
        "--from <agent>  Identify the sending agent",
        "--steer         Deliver as steering when the agent is busy",
        "--follow-up     Queue the message after the current turn",
        "--json          Print JSON",
    ]),
    CommandSpec::new(
        &["schedule"],
        "schedule <list|add|cancel>",
        "Manage prompts that run later or on a recurring schedule",
    ),
    CommandSpec::new(
        &["schedule", "list"],
        "schedule list [--all] [agent] [--json]",
        "List scheduled prompts",
    ),
    CommandSpec::new(
        &["schedule", "add"],
        "schedule add <agent> <schedule> -- <message>",
        "Schedule a prompt",
    )
    .description("The schedule may be a cron expression or a supported one-time schedule.")
    .examples(&["schedule add worker \"0 9 * * 1-5\" -- \"Check open work\""]),
    CommandSpec::new(
        &["schedule", "cancel"],
        "schedule cancel <job-id>",
        "Cancel a scheduled prompt",
    ),
    CommandSpec::new(
        &["status"],
        "status [--daemon-socket <path>] [--json]",
        "Show background service status",
    )
    .options(&[
        "--daemon-socket <path>  Only the daemon on this socket (default: EUKHE_DAEMON_SOCKET)",
        "--json                  Print JSON",
    ]),
    CommandSpec::new(
        &["doctor"],
        "doctor [--fix] [--daemon-socket <path>] [--json]",
        "Inspect and safely clean up background services",
    )
    .options(&[
        "--fix                   Remove stale sockets and stop idle orphaned services",
        "--daemon-socket <path>  Only the daemon on this socket (default: EUKHE_DAEMON_SOCKET)",
        "--json                  Print JSON",
    ]),
    CommandSpec::new(
        &["incident"],
        "incident [--since <time>] [--until <time>] [--session <id>]",
        "Reconstruct a daemon incident from its logs",
    )
    .description(
        "Summarizes the daemon logs for a time window into an operator timeline: supervisor and worker events, session anomalies, and recovery actions. Times without a timezone are read as UTC, matching the log; the default window is the last 24 hours.",
    )
    .options(&[
        "--since <time>  Window start (ISO date/time, date, or HH:MM today; default: 24h ago)",
        "--until <time>  Window end (default: now)",
        "--session <id>  Only events naming this session id, worker id, or session name (prefix match)",
    ])
    .examples(&[
        "incident --since \"2026-09-16T20:02\" --until \"2026-09-16T20:21\"",
        "incident --session 2339fb7da605",
    ]),
    CommandSpec::new(
        &["shutdown"],
        "shutdown [--force] [--daemon-socket <path>] [--json]",
        "Stop every agent and background service",
    )
    .description(
        "Without --force, an interactive confirmation is required. --force also kills unresponsive workers. A socket (--daemon-socket, EUKHE_DAEMON_SOCKET) or agent dir (EUKHE_CODING_AGENT_DIR) limits it to that daemon.",
    )
    .options(&[
        "--force                 Skip confirmation and kill unresponsive processes",
        "--daemon-socket <path>  Only the daemon on this socket (default: EUKHE_DAEMON_SOCKET)",
        "--json                  Print JSON",
    ]),
    CommandSpec::new(
        &["mcp"],
        "mcp <add|list|get|remove>",
        "Manage user MCP servers",
    ),
    CommandSpec::new(
        &["mcp", "add"],
        "mcp add <name> --url <url> [--bearer-token-env-var <env>|--oauth] [--force]",
        "Add an HTTP or stdio MCP server",
    )
    .description("For stdio, use: mcp add <name> [--cwd <dir>] [--env CHILD=SOURCE] -- <command> [args...]"),
    CommandSpec::new(&["mcp", "list"], "mcp list", "List user MCP servers"),
    CommandSpec::new(&["mcp", "get"], "mcp get <name>", "Show a user MCP server"),
    CommandSpec::new(&["mcp", "remove"], "mcp remove <name>", "Remove a user MCP server"),
    CommandSpec::new(
        &["package"],
        "package <install|remove|list|update>",
        "Manage capability packages",
    )
    .description("Packages can provide skills, prompts, and themes."),
    CommandSpec::new(
        &["package", "install"],
        "package install <source> [--local]",
        "Install a capability package",
    )
    .options(&["--local  Install into the current project instead of the user configuration"]),
    CommandSpec::new(
        &["package", "remove"],
        "package remove <source> [--local]",
        "Remove a capability package",
    )
    .options(&["--local  Remove from the current project configuration"]),
    CommandSpec::new(
        &["package", "list"],
        "package list",
        "List installed capability packages",
    ),
    CommandSpec::new(
        &["package", "update"],
        "package update [source]",
        "Update capability packages",
    ),
    CommandSpec::new(
        &["update"],
        "update [--check]",
        "Show how to update eukhe (through its package manager)",
    )
    .options(&["--check  Print the running version beside the update route"])
    .description(
        "eukhe updates through its package manager: update the eukhe flake input (Nix), or \
         install a release from https://github.com/gildrb/eukhe/releases. `update` prints that \
         route and exits 1; `--check` prints the running version and exits 0."),
    CommandSpec::new(&["model"], "model list [search]", "Inspect available models"),
    CommandSpec::new(&["model", "list"], "model list [search]", "List available models"),
    CommandSpec::new(
        &["provider"],
        "provider <caps|models>",
        "Inspect what a provider's API offers besides chat",
    )
    .description(
        "Capabilities come from the quirks rulebook per provider, API, and base URL. Only \
`provider models` sends a request, and only to the provider named.",
    ),
    CommandSpec::new(
        &["provider", "caps"],
        "provider caps [<provider>] [--json]",
        "List each provider's capabilities and endpoints",
    )
    .description(
        "Prints one block per provider, API, and base URL among the provider's chat models \
(every provider with chat models when none is named): each capability with its \
`<dialect>: <endpoint>`, or `unsupported`. Sends no request.",
    )
    .options(&["--json  Print JSON"]),
    CommandSpec::new(
        &["provider", "models"],
        "provider models <provider> [--json]",
        "List the models the provider's API offers now",
    )
    .description(
        "Asks the provider's own model-listing endpoint through its first chat model that \
has `list_models`; a provider without one fails without sending a request.",
    )
    .options(&["--json  Print JSON"]),
    CommandSpec::new(
        &["session"],
        "session export <file> [output]",
        "Manage saved sessions",
    ),
    CommandSpec::new(
        &["session", "export"],
        "session export <file> [output]",
        "Export a saved session to HTML",
    ),
    CommandSpec::new(&["config"], "config", "Configure package resources"),
    CommandSpec::new(
        &["factory"],
        "factory <list|import|export>",
        "Share and run factory machines from the machine library",
    )
    .description(
        "Machines are MACHINE.md templates (frontmatter plus a fenced machine-spec block) \
resolved from the bundled library shipped inside the runtime, then from the personal \
library under the agent dir. Run one with `await rlm.factory.run(\"<name>\")` from a session.",
    ),
    CommandSpec::new(
        &["factory", "list"],
        "factory list [--json]",
        "List the machine library",
    )
    .description(
        "Lists the bundled machines and the personal machines with their descriptions; \
files that fail the parser skip with a warning.",
    )
    .options(&["--json  Print JSON"]),
    CommandSpec::new(
        &["factory", "import"],
        "factory import <path> [--json]",
        "Validate and import a MACHINE.md into the personal library",
    )
    .description(
        "The machine's spec passes the kernel's write-time validator; an invalid spec \
never persists and the exact errors print verbatim.",
    )
    .options(&["--json  Print JSON"]),
    CommandSpec::new(
        &["factory", "export"],
        "factory export <name> --out <path> [--json]",
        "Export a machine to a MACHINE.md file",
    )
    .description(
        "Resolves the library machine named <name> (bundled first, then the personal \
library) and copies its MACHINE.md to the output path; an existing target is \
refused, never overwritten.",
    )
    .options(&[
        "--out <path>  Destination MACHINE.md path",
        "--json        Print JSON",
    ])
    .examples(&["factory export review-sweep --out shared-review-sweep.MACHINE.md"]),
    CommandSpec::new(
        &["chat"],
        "chat <view|status|browse|import>",
        "Read, browse, or import into the chat memory",
    )
    .description(
        "The chat memory is the endless log of every message, the binary tree of one-line \
summaries over it, and the view each turn starts from. It lives under the agent dir.",
    ),
    CommandSpec::new(&["chat", "view"], "chat view", "Print the view the agent sees"),
    CommandSpec::new(
        &["chat", "status"],
        "chat status [--json]",
        "Show the chat's size and its compactor's progress",
    )
    .options(&["--json  Print JSON"]),
    CommandSpec::new(
        &["chat", "browse"],
        "chat browse [--out <path>]",
        "Write the whole memory as one HTML page",
    )
    .description(
        "The page shows the current view, every message, and each level of the tree, each \
entry with its range, time span, and size. The default output is browse.html in the chat dir.",
    )
    .options(&["--out <path>  Destination HTML path"]),
    CommandSpec::new(
        &["chat", "import"],
        "chat import sessions <path>...",
        "Import older sessions as chat messages",
    )
    .description(
        "sessions imports the user's messages and the final replies of saved root sessions \
(session .jsonl files or directories), oldest first, without tool noise or repeated pastes. \
The compactor then summarizes them like any other messages.",
    )
    .examples(&["chat import sessions ~/.eukhe/sessions"]),
    CommandSpec::new(
        &["gateway"],
        "gateway [--daemon-socket <path>]",
        "Chat with the current session from Signal",
    )
    .description(
        "Runs signal-cli and relays Signal messages into the newest session (the one the CLI \
uses), then sends the replies back. Set gateway.signal.account in the global settings first. \
Runs until Ctrl+C. See docs/gateway.md.",
    )
    .options(&["--daemon-socket <path>  Use a specific daemon socket"]),
    CommandSpec::new(
        &["dashboard"],
        "dashboard [--port <port>] [--no-open] [--allow-host <name>]... [--rotate-token] [--daemon-socket <path>]",
        "Open the web dashboard: chat with and control the current session, browse its memory",
    )
    .description(
        "Serves a mobile-friendly web dashboard on 127.0.0.1 and opens it in the browser. It \
chats with the newest session (the one the CLI and the gateway use, or one you pick), controls it \
(model, thinking, queue, compaction, approvals, saved sessions), and shows the chat memory as a \
tree of dated lines you can open down to each message. It listens on loopback only. The URL it \
prints holds a pairing token after `#token=`: a browser must present it, and nothing runs for a \
socket without the current token. The token stays the same across restarts (it is in the agent \
dir, mode 0600) until --rotate-token replaces it. It answers only to loopback host names and to \
the names you add with --allow-host (for example the name `tailscale serve` gives your machine), \
and its socket accepts only pages it served itself. Runs until Ctrl+C. See docs/dashboard.md.",
    )
    .options(&[
        "--port <port>           Listen on this port (default: a free port)",
        "--no-open               Print the URL without opening the browser",
        "--allow-host <name>     Also answer to this host name (repeatable), e.g. a tailscale serve name",
        "--rotate-token          Replace the pairing token: every earlier link stops working",
        "--daemon-socket <path>  Use a specific daemon socket",
    ]),
    CommandSpec::new(
        &["prompt"],
        "prompt [--model <selector>] [--cwd <dir>] [--json]",
        "Print the assembled system prompt with its layer breakdown",
    )
    .description(
        "Assembles the effective system prompt the way a fresh root session does \
and prints the per-layer breakdown (cached static layers, then the dynamic tail) followed by the full prompt text.",
    )
    .options(&[
        "--model <selector>  Preview the per-model additions (model-prompts.toml) for a selector",
        "--cwd <dir>         Assemble for this working directory (default: current)",
        "--json              Print segments and prompt as JSON",
    ]),
    CommandSpec::new(
        &["tiny-models"],
        "tiny-models [list|download <id|all>]",
        "List or download the local tiny models",
    )
    .description(
        "Lists the pinned local models (text, speech to text, text to speech) with their size \
and install state; download fetches a model's pinned files from Hugging Face into the agent \
dir and checks each against its sha256. Nothing downloads on its own: this command is the only \
way a local model gets installed.",
    )
    .examples(&["tiny-models", "tiny-models download lfm2.5-230m"]),
    CommandSpec::new(
        &["kernel"],
        "kernel install [--check]",
        "Install the Python kernel once, or check it",
    )
    .description(
        "Installs the environment of the Python kernel (the ipython tool): a Python from uv and \
the hash-locked kernel packages (eukhe-runtime/requirements-kernel.txt), each checked against its \
hash before install. Nothing downloads on its own: this command is the only way the kernel gets \
installed. A session uses the installed kernel and never downloads; without it, the ipython tool \
names this command and the other tools work. A second run keeps an installed kernel. --check \
shows the state and makes no network request.",
    )
    .examples(&["kernel install", "kernel install --check"]),
    CommandSpec::new(
        &["translate"],
        "translate <lang> <text...>",
        "Translate text with the translate role's model",
    )
    .description(
        "Uses the first available model of the translate role (modelRoles.translate, then \
retry.fallbackChains.translate; unset: the installed local text models, then the default \
provider model) and prints only the translation. <lang> is a language code (fr) or name.",
    )
    .examples(&["translate pt good morning"]),
    CommandSpec::new(
        &["say"],
        "say <text...> [--out <file.wav>] [--voice <id>]",
        "Speak text with the local speech model",
    )
    .description(
        "Uses the speech role's local model (kokoro). Without --out it plays through the \
first of pw-play, paplay, or aplay; the voice defaults to tts.localVoice.",
    )
    .options(&[
        "--out <file.wav>  Write the speech to a WAV file instead of playing it",
        "--voice <id>      The voice (af_heart, bf_emma, ...)",
    ]),
    CommandSpec::new(
        &["transcribe"],
        "transcribe <file.wav> [--language <code>]",
        "Transcribe a WAV file with the local dictation model",
    )
    .description("Uses the dictation role's local model (whisper) and prints the text.")
    .options(&["--language <code>  The spoken language (default: detected)"]),
];

/// Command names that once existed and now print removal guidance.
pub const REMOVED_COMMAND_NAMES: &[&str] =
    &["app", "daemon", "install", "manage", "remove", "uninstall"];

/// The top-level public command names.
pub fn public_command_names() -> Vec<&'static str> {
    COMMAND_SPECS
        .iter()
        .filter(|spec| spec.path.len() == 1)
        .map(|spec| spec.path[0])
        .collect()
}

struct OptionGroup {
    heading: &'static str,
    options: &'static [(&'static str, &'static str)],
}

const TOP_LEVEL_OPTION_GROUPS: &[OptionGroup] = &[
    OptionGroup {
        heading: "Run options",
        options: &[
            ("-p, --print", "Print a response and exit"),
            (
                "--mode <text|json|rpc|acp|daemon>",
                "Select the output mode (default: text)",
            ),
            ("--cwd <dir>", "Use a specific working directory"),
            ("--offline", "Disable startup network operations"),
            ("--verbose", "Force verbose startup"),
            ("--daemon-socket <path>", "Use a specific daemon socket"),
        ],
    },
    OptionGroup {
        heading: "Model options",
        options: &[
            ("--provider <name>", "Select a model provider"),
            ("--model <id>", "Select a model"),
            ("--api-key <key>", "Use an API key for this run"),
            (
                "--models <patterns>",
                "Set comma-separated models for cycling",
            ),
            (
                "--thinking <level>",
                "Set reasoning: off, minimal, low, medium, high, xhigh, max",
            ),
        ],
    },
    OptionGroup {
        heading: "Session options",
        options: &[
            ("-c, --continue", "Continue the previous session"),
            (
                "-r, --resume [path|id]",
                "Open the agents view, or resume a saved session",
            ),
            (
                "--fork <path|id>",
                "Fork a saved session into a new session",
            ),
            ("--session-dir <dir>", "Use a custom session directory"),
            ("--no-session", "Do not save the session"),
            (
                "--goal <objective>",
                "Seed a persistent goal for a new root session",
            ),
            (
                "--goal-token-budget <n>",
                "Set a positive token budget for --goal",
            ),
        ],
    },
    OptionGroup {
        heading: "Resource options",
        options: &[
            ("--skill <path>", "Load a skill (repeatable)"),
            ("-ns, --no-skills", "Disable skill discovery"),
            (
                "--prompt-template <path>",
                "Load a prompt template (repeatable)",
            ),
            (
                "-np, --no-prompt-templates",
                "Disable prompt template discovery",
            ),
            ("--theme <path>", "Load a theme (repeatable)"),
            ("--no-themes", "Disable theme discovery"),
            (
                "-nc, --no-context-files",
                "Disable AGENTS.md and CLAUDE.md discovery",
            ),
        ],
    },
    OptionGroup {
        heading: "Prompt options",
        options: &[
            (
                "--system-prompt <text>",
                "Replace the default system prompt",
            ),
            (
                "--system-prompt-file <path>",
                "Replace the default system prompt with this file",
            ),
            (
                "--append-system-prompt <text>",
                "Append to the system prompt (repeatable)",
            ),
            (
                "--append-system-prompt-file <path>",
                "Append this file to the system prompt (repeatable)",
            ),
            ("--", "Treat all following arguments as messages"),
        ],
    },
    OptionGroup {
        heading: "Autonomous options",
        options: &[
            (
                "--autonomous",
                "Continue until gates pass or a limit is reached",
            ),
            (
                "--autonomous-gate <command>",
                "Run a completion gate (repeatable)",
            ),
            (
                "--autonomous-gate-retries <n>",
                "Set positive retries per failed gate (default: 3)",
            ),
            (
                "--autonomous-gate-timeout-ms <n>",
                "Set positive per-gate timeout in ms (default: 300000)",
            ),
            (
                "--autonomous-max-continuations <n>",
                "Set positive follow-up limit (default: 3)",
            ),
            (
                "--autonomous-max-turns <n>",
                "Set positive assistant-turn limit (default: 12)",
            ),
            (
                "--autonomous-max-tokens <n>",
                "Set positive token limit (default: 80000)",
            ),
            (
                "--autonomous-timeout-ms <n>",
                "Set positive wall-clock limit in ms (default: 1800000)",
            ),
        ],
    },
    OptionGroup {
        heading: "Help",
        options: &[
            ("-v, --version", "Show version and exit"),
            ("-h, --help", "Show this help"),
        ],
    },
];

/// Look up a command spec by its exact path.
pub fn get_command_spec(path: &[&str]) -> Option<&'static CommandSpec> {
    COMMAND_SPECS.iter().find(|spec| {
        spec.path.len() == path.len() && spec.path.iter().zip(path).all(|(a, b)| a == b)
    })
}

/// The direct child command specs of a path.
pub fn get_child_command_specs(path: &[&str]) -> Vec<&'static CommandSpec> {
    COMMAND_SPECS
        .iter()
        .filter(|spec| {
            spec.path.len() == path.len() + 1
                && path
                    .iter()
                    .enumerate()
                    .all(|(index, segment)| spec.path[index] == *segment)
        })
        .collect()
}

/// True when a `help <path>` request resolves to help rather than a message.
pub fn is_help_command_request(path: &[&str]) -> bool {
    if path.is_empty() || get_command_spec(path).is_some() {
        return true;
    }
    if REMOVED_COMMAND_NAMES.contains(&path[0]) {
        return true;
    }
    if get_command_spec(&path[..1]).is_some() {
        return true;
    }
    let parent = &path[..path.len() - 1];
    let candidates: Vec<&str> = get_child_command_specs(parent)
        .into_iter()
        .map(|spec| spec.path[spec.path.len() - 1])
        .collect();
    eukhe_bend::rules::slash::suggestion(path[path.len() - 1], &candidates).is_some()
}

fn pad_end(value: &str, width: usize) -> String {
    let len = value.chars().count();
    if len >= width {
        value.to_string()
    } else {
        format!("{value}{}", " ".repeat(width - len))
    }
}

/// The full `--help` output, mirroring `formatTopLevelHelp`.
pub fn format_top_level_help() -> String {
    let commands: Vec<&CommandSpec> = COMMAND_SPECS
        .iter()
        .filter(|spec| spec.path.len() == 1)
        .collect();
    let command_width = commands
        .iter()
        .map(|spec| spec.path[0].len())
        .max()
        .unwrap_or(0);
    let options = TOP_LEVEL_OPTION_GROUPS
        .iter()
        .map(|group| {
            let width = group
                .options
                .iter()
                .map(|(option, _)| option.chars().count())
                .max()
                .unwrap_or(0);
            let lines: Vec<String> = group
                .options
                .iter()
                .map(|(option, summary)| format!("  {}  {}", pad_end(option, width), summary))
                .collect();
            format!("{}:\n{}", group.heading, lines.join("\n"))
        })
        .collect::<Vec<_>>()
        .join("\n\n");
    let command_lines: Vec<String> = commands
        .iter()
        .map(|spec| {
            format!(
                "  {}  {}",
                pad_end(spec.path[0], command_width),
                spec.summary
            )
        })
        .collect();
    format!(
        "{APP_NAME} - AI coding assistant with a Python REPL tool\n\
         \n\
         Usage:\n\
         \x20 {APP_NAME} [options] [@files...] [message...]\n\
         \x20 {APP_NAME} <command> [args...]\n\
         \n\
         Options:\n\
         {options}\n\
         \n\
         Commands:\n\
         {}\n\
         \n\
         Run \"{APP_NAME} help <command>\" for command details.",
        command_lines.join("\n")
    )
}

/// Per-command help output, mirroring `formatCommandHelp`.
pub fn format_command_help(path: &[&str]) -> Option<String> {
    let spec = get_command_spec(path)?;
    let children = get_child_command_specs(path);
    let mut sections = vec![
        format!("Usage:\n  {APP_NAME} {}", spec.usage),
        String::new(),
        format!("{}.", spec.summary),
    ];
    if let Some(description) = spec.description {
        sections.push(String::new());
        sections.push(description.to_string());
    }
    if !children.is_empty() {
        let width = children
            .iter()
            .map(|child| child.path[child.path.len() - 1].len())
            .max()
            .unwrap_or(0);
        sections.push(String::new());
        sections.push("Commands:".to_string());
        for child in children {
            sections.push(format!(
                "  {}  {}",
                pad_end(child.path[child.path.len() - 1], width),
                child.summary
            ));
        }
    }
    if !spec.options.is_empty() {
        sections.push(String::new());
        sections.push("Options:".to_string());
        for option in spec.options {
            sections.push(format!("  {option}"));
        }
    }
    if !spec.examples.is_empty() {
        sections.push(String::new());
        sections.push("Examples:".to_string());
        for example in spec.examples {
            sections.push(format!("  {APP_NAME} {example}"));
        }
    }
    Some(sections.join("\n"))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn help_command_request() {
        assert!(is_help_command_request(&["schedule", "bogus"]));
        assert!(!is_help_command_request(&["bogus"]));
        assert!(is_help_command_request(&[]));
        assert!(is_help_command_request(&["daemon"]));
    }
}
