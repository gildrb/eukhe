//! The phone commands: their vocabulary, how a message parses into one,
//! and the answer a command-shaped message gets when it names none.
//! Signal has no command menu, so a lone `/` lists the commands, a prefix
//! lists the commands it starts, and a near miss names the closest.

use eukhe_types::slash_commands::find_slash_command_suggestion;

/// A phone command (case-insensitive name, exact argument count).
pub(crate) enum PhoneCommand {
    Help,
    Sessions,
    /// `/use N`, with `N` as written.
    Use(String),
    Latest,
    New,
    Stop,
    Status,
    Memory,
}

/// What one text message means to the gateway.
pub(crate) enum Parsed {
    Command(PhoneCommand),
    /// A command-shaped message that runs nothing: the gateway answers it
    /// (the command list, a usage line, or a suggestion) and the agent
    /// never sees it.
    Answer(String),
    /// Text for the agent.
    Prompt,
}

struct Spec {
    name: &'static str,
    usage: &'static str,
    description: &'static str,
}

const COMMANDS: [Spec; 8] = [
    Spec {
        name: "help",
        usage: "/help",
        description: "Show the commands.",
    },
    Spec {
        name: "sessions",
        usage: "/sessions",
        description: "Show the newest sessions.",
    },
    Spec {
        name: "use",
        usage: "/use N",
        description: "Send messages to session N.",
    },
    Spec {
        name: "latest",
        usage: "/latest",
        description: "Send messages to the newest session.",
    },
    Spec {
        name: "new",
        usage: "/new",
        description: "Start a new session.",
    },
    Spec {
        name: "stop",
        usage: "/stop",
        description: "Stop the current turn.",
    },
    Spec {
        name: "status",
        usage: "/status",
        description: "Show the session state.",
    },
    Spec {
        name: "memory",
        usage: "/memory",
        description: "Show the chat memory state.",
    },
];

/// Parse one text message (without images).
///
/// A first word of `/` plus letters, digits, `-` or `_` is command-shaped;
/// any other text (a path such as `/tmp/x`, a sentence) goes to the agent.
/// A command-shaped message that names a command with the wrong arguments
/// gets its usage; an unknown name alone gets suggestions; an unknown name
/// followed by more words goes to the agent.
pub(crate) fn parse(text: &str) -> Parsed {
    let words: Vec<&str> = text.split_whitespace().collect();
    let Some((first, args)) = words.split_first() else {
        return Parsed::Prompt;
    };
    let Some(name) = first.strip_prefix('/') else {
        return Parsed::Prompt;
    };
    if !name
        .chars()
        .all(|c| c.is_ascii_alphanumeric() || c == '-' || c == '_')
    {
        return Parsed::Prompt;
    }
    let name = name.to_ascii_lowercase();
    let command = match (name.as_str(), args) {
        ("help", []) => PhoneCommand::Help,
        ("sessions", []) => PhoneCommand::Sessions,
        ("use", [number]) => PhoneCommand::Use((*number).to_string()),
        ("latest", []) => PhoneCommand::Latest,
        ("new", []) => PhoneCommand::New,
        ("stop", []) => PhoneCommand::Stop,
        ("status", []) => PhoneCommand::Status,
        ("memory", []) => PhoneCommand::Memory,
        _ => {
            return match COMMANDS.iter().find(|spec| spec.name == name) {
                Some(spec) => Parsed::Answer(format!("Usage: {}", line(spec))),
                None if args.is_empty() => Parsed::Answer(suggest(&name)),
                None => Parsed::Prompt,
            }
        }
    };
    Parsed::Command(command)
}

/// The `/help` text.
pub(crate) fn help() -> String {
    let mut lines = vec!["Commands:".to_string()];
    lines.extend(COMMANDS.iter().map(line));
    lines.push("Other text goes to the agent.".to_string());
    lines.join("\n")
}

fn line(spec: &Spec) -> String {
    format!("{} - {}", spec.usage, spec.description)
}

/// The answer to `/<name>` alone when `name` is no command: the commands
/// it starts, else the closest command, else the command list.
fn suggest(name: &str) -> String {
    if name.is_empty() {
        return help();
    }
    let starting: Vec<&Spec> = COMMANDS
        .iter()
        .filter(|spec| spec.name.starts_with(name))
        .collect();
    if !starting.is_empty() {
        let mut lines: Vec<String> = starting.into_iter().map(line).collect();
        lines.push("Send one of these. Send / for all commands.".to_string());
        return lines.join("\n");
    }
    let names: Vec<&str> = COMMANDS.iter().map(|spec| spec.name).collect();
    match find_slash_command_suggestion(name, &names) {
        Some(closest) => format!(
            "No command /{name}. Did you mean /{closest}?\nNot sent to the agent. Send / for all commands."
        ),
        None => format!("No command /{name}. Not sent to the agent.\n{}", help()),
    }
}
