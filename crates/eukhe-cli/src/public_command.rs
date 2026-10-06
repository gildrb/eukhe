//! Public command routing, ported from `cli/public-command.ts`.

use crate::daemon_discovery;
use std::collections::HashSet;

use crate::args::{parse_args, INTERNAL_RUNTIME_COMMAND_MARKER};

use crate::command_registry::{
    find_command_suggestion, format_command_help, format_top_level_help, get_child_command_specs,
    get_command_spec, is_help_command_request, public_command_names, REMOVED_COMMAND_NAMES,
};
use crate::config::APP_NAME;
use crate::global_flags::{extract_help_command_path, rotate_global_flags_before_command};
use crate::mcp_command::run_mcp_management_command;
use crate::package_command::handle_package_command;

/// Why `update` installs nothing: eukhe updates through the package manager
/// that installed it.
const EXTERNAL_UPDATES: &str = "eukhe updates through its package manager: update the eukhe flake input (Nix), or install a release from https://github.com/gildrb/eukhe/releases";

/// The outcome of routing the argv through the public command layer.
#[derive(Debug, Clone)]
pub struct PublicCommandResult {
    pub handled: bool,
    pub args: Vec<String>,
    pub explicit_agents_view: bool,
    pub attach_agent: Option<String>,
    /// The process exit code to use once handled.
    pub exit_code: Option<i32>,
}

const HANDLED: fn() -> PublicCommandResult = || PublicCommandResult {
    handled: true,
    args: vec![],
    explicit_agents_view: false,
    attach_agent: None,
    exit_code: None,
};

fn continue_with(args: Vec<String>) -> PublicCommandResult {
    PublicCommandResult {
        handled: false,
        args,
        explicit_agents_view: false,
        attach_agent: None,
        exit_code: None,
    }
}

/// The error message used when a routed command needs a runtime subsystem that
/// is not linked into this build yet.
fn fail(message: impl AsRef<str>, hint: Option<String>) -> PublicCommandResult {
    eprintln!("Error: {}", message.as_ref());
    if let Some(hint) = hint {
        eprintln!("{hint}");
    }
    PublicCommandResult {
        handled: true,
        args: vec![],
        explicit_agents_view: false,
        attach_agent: None,
        exit_code: Some(1),
    }
}

fn handled() -> PublicCommandResult {
    HANDLED()
}

/// A handled invocation whose driver already printed everything, with its own
/// process exit code (shutdown failures exit 1).
fn handled_with_exit(exit_code: i32) -> PublicCommandResult {
    PublicCommandResult {
        handled: true,
        args: vec![],
        explicit_agents_view: false,
        attach_agent: None,
        exit_code: Some(exit_code),
    }
}

/// A handled invocation whose `fail()` branch already printed an error: the
/// exit code is 1, matching `process.exitCode = 1` in the TS `fail` helper.
fn handled_failed() -> PublicCommandResult {
    PublicCommandResult {
        handled: true,
        args: vec![],
        explicit_agents_view: false,
        attach_agent: None,
        exit_code: Some(1),
    }
}

/// Route the argv through the public command layer, mirroring
/// `handlePublicCommand`. All errors are printed directly; the result reports
/// whether the invocation was fully handled and with which exit code.
pub fn handle_public_command(args: &[String]) -> PublicCommandResult {
    let public: HashSet<&str> = public_command_names().into_iter().collect();
    let removed: HashSet<&str> = REMOVED_COMMAND_NAMES.iter().copied().collect();
    let args = rotate_global_flags_before_command(args, &public, &removed);

    if args.first().map(String::as_str) == Some("help") {
        if let Some(help_path) = extract_help_command_path(&args, 1) {
            let help_path_ref: Vec<&str> = help_path.iter().map(String::as_str).collect();
            if is_help_command_request(&help_path_ref) {
                return print_requested_help(&help_path);
            }
        }
    }

    let Some(command) = args.first() else {
        return continue_with(args);
    };
    let command = command.as_str();

    if removed.contains(command) {
        return reject_removed_command(&args);
    }
    if !public.contains(command) {
        return continue_with(args.clone());
    }

    let separator_index = args.iter().position(|a| a == "--");
    let help_index = args.iter().enumerate().position(|(index, arg)| {
        index > 0
            && (separator_index.is_none() || index < separator_index.unwrap())
            && (arg == "--help" || arg == "-h")
    });
    if let Some(help_index) = help_index {
        return print_requested_help(&get_command_path(&args[..help_index]));
    }

    let rest: Vec<String> = args[1..].to_vec();
    match command {
        "agents" => PublicCommandResult {
            handled: false,
            args: rest,
            explicit_agents_view: true,
            attach_agent: None,
            exit_code: None,
        },
        "list" => run_internal_agent_command("list", &rest),
        "sessions" => run_internal_agent_command("sessions", &rest),
        "attach" => run_attach(&rest),
        "stop" => {
            if !require_operand_count(&rest, 1, Some(1), "stop") {
                return handled_failed();
            }
            run_internal_agent_command("kill", &rest)
        }
        "rename" => {
            if !require_operand_count(&rest, 2, None, "rename") {
                return handled_failed();
            }
            run_internal_agent_command("rename", &rest)
        }
        "send" => run_internal_agent_command("send", &rest),
        "schedule" => run_nested_agent_command("schedule", "cron", &rest),
        "status" => run_status(&rest),
        "doctor" => run_doctor(&rest),
        "telemetry" => run_telemetry(&rest),
        "incident" => run_incident_command(&rest),
        "shutdown" => run_shutdown(&rest),
        "package" => run_package(&rest),
        "mcp" => run_mcp(&rest),
        "update" => run_update(&rest),
        "model" => rewrite_nested_command("model", "list", "--list-models", &rest),
        "session" => rewrite_nested_command("session", "export", "--export", &rest),
        "prompt" => handled_with_exit(crate::prompt_command::run_prompt_command(&rest)),
        "factory" => handled_with_exit(crate::factory_command::run_factory_command(&rest)),
        "chat" => handled_with_exit(crate::chat_command::run_chat_command(&rest)),
        "config" => {
            if !rest.is_empty() {
                return fail(format!("Usage: {APP_NAME} config"), None);
            }
            continue_with(args.clone())
        }
        _ => continue_with(args.clone()),
    }
}

fn print_requested_help(path: &[String]) -> PublicCommandResult {
    if path.is_empty() {
        println!("{}", format_top_level_help());
        return handled();
    }
    if REMOVED_COMMAND_NAMES.contains(&path[0].as_str()) {
        return reject_removed_command(path);
    }
    let path_ref: Vec<&str> = path.iter().map(String::as_str).collect();
    if let Some(help) = format_command_help(&path_ref) {
        println!("{help}");
        return handled();
    }
    let parent: Vec<&str> = path[..path.len() - 1].iter().map(String::as_str).collect();
    let candidates: Vec<&str> = get_child_command_specs(&parent)
        .into_iter()
        .map(|spec| spec.path[spec.path.len() - 1])
        .collect();
    let suggestion = find_command_suggestion(&path[path.len() - 1], &candidates);
    let mut message = format!("Unknown command: {}", path.join(" "));
    let hint = suggestion.map(|suggestion| {
        let mut full = parent.clone();
        full.push(suggestion);
        format!("Did you mean \"{APP_NAME} help {}\"?", full.join(" "))
    });
    if suggestion.is_none() {
        // The exact TS message includes no hint when there is no suggestion.
        message = format!("Unknown command: {}", path.join(" "));
    }
    fail(message, hint)
}

fn get_command_path(args: &[String]) -> Vec<String> {
    let mut path: Vec<String> = Vec::new();
    for arg in args {
        let mut candidate: Vec<&str> = path.iter().map(String::as_str).collect();
        candidate.push(arg);
        if get_command_spec(&candidate).is_none() {
            break;
        }
        path.push(arg.clone());
    }
    path
}

fn reject_removed_command(args: &[String]) -> PublicCommandResult {
    let command = args.first().map(String::as_str).unwrap_or_default();
    let subcommand = args.get(1).map(String::as_str);
    let replacement = match (command, subcommand) {
        ("daemon", _) => Some("Run \"eukhe help\" to see the agent commands.".to_string()),
        ("app", Some("update")) => Some("Use \"eukhe update\".".to_string()),
        ("install", _) => Some("Use \"eukhe package install\".".to_string()),
        ("remove" | "uninstall", _) => Some("Use \"eukhe package remove\".".to_string()),
        ("manage", _) => Some("Use \"eukhe agents\".".to_string()),
        _ => None,
    };
    let joined: Vec<&str> = args.iter().take(2).map(String::as_str).collect();
    fail(
        format!("Unknown command: {}", joined.join(" ")),
        replacement,
    )
}

/// The internal daemon client command behind a public command: `list` stays
/// `list`, `stop` becomes `kill`, and nested `schedule` becomes `cron`, like
/// `runInternalAgentCommand`/`runNestedAgentCommand` in public-command.ts.
fn run_internal_agent_command(command: &str, args: &[String]) -> PublicCommandResult {
    match crate::daemon_command::run_daemon_command(command, args) {
        Ok(()) => handled(),
        Err(error) => fail(error.to_string(), None),
    }
}

fn run_nested_agent_command(
    parent: &str,
    internal_command: &str,
    args: &[String],
) -> PublicCommandResult {
    let subcommand = args.first().map(String::as_str);
    let children: Vec<&str> = get_child_command_specs(&[parent])
        .into_iter()
        .map(|spec| spec.path[spec.path.len() - 1])
        .collect();
    let Some(subcommand) = subcommand else {
        return fail(
            format!("Missing {parent} command."),
            Some(format!("Run \"{APP_NAME} help {parent}\" for usage.")),
        );
    };
    if !children.contains(&subcommand) {
        let suggestion = find_command_suggestion(subcommand, &children);
        return fail(
            format!("Unknown {parent} command: {subcommand}"),
            Some(suggestion.map_or_else(
                || format!("Run \"{APP_NAME} help {parent}\" for usage."),
                |s| format!("Did you mean \"{APP_NAME} {parent} {s}\"?"),
            )),
        );
    }
    if parent == "schedule" && !validate_schedule_args(args) {
        return handled_failed();
    }
    run_internal_agent_command(internal_command, args)
}

fn validate_schedule_args(args: &[String]) -> bool {
    let subcommand = args[0].as_str();
    if subcommand == "list" {
        let mut agent_count = 0;
        for arg in &args[1..] {
            if arg == "--all" || arg == "-a" || arg == "--json" {
                continue;
            }
            if arg.starts_with('-') {
                fail("Usage: eukhe schedule list [--all] [agent] [--json]", None);
                return false;
            }
            agent_count += 1;
            if agent_count > 1 {
                fail("Usage: eukhe schedule list [--all] [agent] [--json]", None);
                return false;
            }
        }
        return true;
    }
    if subcommand == "cancel" {
        let operands: Vec<&String> = args[1..].iter().filter(|arg| *arg != "--json").collect();
        if operands.len() == 1 && !operands[0].starts_with('-') {
            return true;
        }
        fail("Usage: eukhe schedule cancel <job-id>", None);
        return false;
    }
    true
}

fn parse_boolean_options(
    args: &[String],
    allowed: &[&str],
    command: &str,
) -> Option<HashSet<String>> {
    let mut options = HashSet::new();
    for arg in args {
        if !allowed.contains(&arg.as_str()) {
            fail(
                format!("Unknown option for {command}: {arg}"),
                Some(format!("Run \"{APP_NAME} help {command}\" for usage.")),
            );
            return None;
        }
        options.insert(arg.clone());
    }
    Some(options)
}

/// The options of a daemon-discovery command (`status`, `doctor`,
/// `shutdown`): its boolean flags plus the `--daemon-socket <path>` the
/// invocation targets (flag, then `EUKHE_DAEMON_SOCKET`, then the
/// default - the same precedence every mode uses to start its daemon).
struct DiscoveryOptions {
    flags: HashSet<String>,
    daemon_socket: Option<String>,
}

impl DiscoveryOptions {
    fn state_root(&self) -> daemon_discovery::DaemonStateRoot {
        daemon_discovery::current_state_root(self.daemon_socket.as_deref())
    }
}

fn parse_discovery_options(
    args: &[String],
    allowed: &[&str],
    command: &str,
) -> Option<DiscoveryOptions> {
    let mut flags = Vec::new();
    let mut daemon_socket = None;
    let mut index = 0;
    while index < args.len() {
        let arg = &args[index];
        if arg == "--daemon-socket" || arg == "--socket" {
            let Some(value) = args.get(index + 1) else {
                fail(format!("{arg} requires a value"), None);
                return None;
            };
            daemon_socket = Some(value.clone());
            index += 2;
            continue;
        }
        flags.push(arg.clone());
        index += 1;
    }
    let flags = parse_boolean_options(&flags, allowed, command)?;
    Some(DiscoveryOptions {
        flags,
        daemon_socket,
    })
}

fn run_status(args: &[String]) -> PublicCommandResult {
    let Some(options) = parse_discovery_options(args, &["--json"], "status") else {
        return handled_failed();
    };
    daemon_discovery::run_ps(options.flags.contains("--json"), &options.state_root());
    handled()
}

fn run_doctor(args: &[String]) -> PublicCommandResult {
    let Some(options) = parse_discovery_options(args, &["--fix", "--json"], "doctor") else {
        return handled_failed();
    };
    // `doctor` inspects; `doctor --fix` reaps clearly-safe services (TS
    // runDoctor: runReap with force=false, else runPs).
    let json = options.flags.contains("--json");
    if options.flags.contains("--fix") {
        daemon_discovery::run_reap(json, &options.state_root());
    } else {
        daemon_discovery::run_ps(json, &options.state_root());
    }
    handled()
}

/// `eukhe telemetry [status|on|off]`: the same report and settings
/// switch as the `/telemetry` slash command, for the current directory's
/// settings scope.
fn run_telemetry(args: &[String]) -> PublicCommandResult {
    let usage = || fail(format!("Usage: {APP_NAME} telemetry [status|on|off]"), None);
    if args.len() > 1 {
        return usage();
    }
    let cwd = std::env::current_dir().unwrap_or_default();
    let agent_dir = crate::config::get_agent_dir();
    let mut settings = eukhe_core::settings::SettingsManager::create(&cwd, &agent_dir);
    let report = match args.first().map(String::as_str) {
        None | Some("status") => {
            Ok(eukhe_core::session_engine::telemetry::telemetry_status_text(&settings, &agent_dir))
        }
        Some(choice @ ("on" | "off")) => {
            eukhe_core::session_engine::telemetry::set_telemetry_enabled_text(
                &mut settings,
                &agent_dir,
                choice == "on",
            )
        }
        Some(_) => return usage(),
    };
    match report {
        Ok(report) => {
            println!("{report}");
            handled()
        }
        Err(error) => fail(format!("{error:#}"), None),
    }
}

/// `eukhe incident` (TS `runIncidentCommand`): parse the options,
/// resolve the window once, and print the timeline.
fn run_incident_command(args: &[String]) -> PublicCommandResult {
    let options = match crate::incident::parse_incident_options(args) {
        Ok(options) => options,
        Err(error) => {
            return fail(
                error.to_string(),
                Some(format!("Run \"{APP_NAME} help incident\" for usage.")),
            )
        }
    };
    // Resolve once: re-resolving later can cross UTC midnight and render a
    // different window than the one that was validated.
    let now_ms = crate::util_time::now_ms() as i64;
    let window = match crate::incident::resolve_incident_window(&options, now_ms) {
        Ok(window) => window,
        Err(error) => {
            return fail(
                error.to_string(),
                Some(format!("Run \"{APP_NAME} help incident\" for usage.")),
            )
        }
    };
    if let Err(error) = crate::incident::run_incident(&options, Some(window)) {
        return fail(
            error.to_string(),
            Some(format!("Run \"{APP_NAME} help incident\" for usage.")),
        );
    }
    handled()
}

fn run_shutdown(args: &[String]) -> PublicCommandResult {
    let Some(options) = parse_discovery_options(args, &["--force", "--json"], "shutdown") else {
        return handled_failed();
    };
    let force = options.flags.contains("--force");
    let json = options.flags.contains("--json");
    // The confirmation decision (including the non-TTY failure, which TS
    // only raises once there are daemons to stop) lives with the discovery
    // driver, which knows the daemon count.
    let exit_code = daemon_discovery::run_shutdown_all(json, force, &options.state_root());
    handled_with_exit(exit_code)
}

fn run_mcp(args: &[String]) -> PublicCommandResult {
    match run_mcp_management_command(args) {
        Ok(message) => {
            println!("{message}");
            handled()
        }
        Err(error) => fail(error.to_string(), None),
    }
}

fn run_package(args: &[String]) -> PublicCommandResult {
    let Some(subcommand) = args.first().map(String::as_str) else {
        return fail(
            "Missing package command.",
            Some("Run \"eukhe help package\" for usage.".to_string()),
        );
    };
    if subcommand == "uninstall" {
        return fail(
            "Unknown package command: uninstall",
            Some("Use \"eukhe package remove\".".to_string()),
        );
    }
    let children: Vec<&str> = get_child_command_specs(&["package"])
        .into_iter()
        .map(|spec| spec.path[spec.path.len() - 1])
        .collect();
    if !children.contains(&subcommand) {
        let suggestion = find_command_suggestion(subcommand, &children);
        return fail(
            format!("Unknown package command: {subcommand}"),
            Some(suggestion.map_or_else(
                || "Run \"eukhe help package\" for usage.".to_string(),
                |s| format!("Did you mean \"{APP_NAME} package {s}\"?"),
            )),
        );
    }
    let rest = &args[1..];
    if subcommand == "list" && !rest.is_empty() {
        return fail(format!("Usage: {APP_NAME} package list"), None);
    }
    if subcommand == "update"
        && rest
            .first()
            .is_some_and(|source| source == "self" || source == APP_NAME)
    {
        return fail(
            format!("Run \"{APP_NAME} update\" to see how to update {APP_NAME}."),
            None,
        );
    }
    let mut package_args: Vec<String> = vec![subcommand.to_string()];
    package_args.extend(rest.iter().cloned());
    let result = handle_package_command(&package_args);
    PublicCommandResult {
        handled: true,
        args: vec![],
        explicit_agents_view: false,
        attach_agent: None,
        exit_code: result.exit_code,
    }
}

/// `eukhe update`: eukhe never replaces itself, so the command names the
/// package-manager route and fails; `--check` (alias `--version`) reports
/// the running version beside the same route.
fn run_update(args: &[String]) -> PublicCommandResult {
    let Some(options) = parse_boolean_options(args, &["--check", "--version"], "update") else {
        return handled_failed();
    };
    if options.is_empty() {
        return fail(EXTERNAL_UPDATES, None);
    }
    println!("Running:  {}", crate::config::version());
    println!("{EXTERNAL_UPDATES}");
    handled()
}

fn run_attach(rest: &[String]) -> PublicCommandResult {
    let Some(agent) = rest.first().filter(|agent| !agent.starts_with('-')) else {
        return fail(format!("Usage: {APP_NAME} attach <agent>"), None);
    };
    let options = &rest[1..];
    if has_positional_arguments(options) {
        return fail(format!("Usage: {APP_NAME} attach <agent>"), None);
    }
    if has_conflicting_attach_option(options) {
        return fail(
            "attach cannot be combined with --resume, --continue, or --fork.",
            None,
        );
    }
    let agent = agent.as_str();
    let mut args: Vec<String> = vec!["--resume".to_string(), agent.to_string()];
    args.extend(options.iter().cloned());
    PublicCommandResult {
        handled: false,
        args,
        explicit_agents_view: false,
        attach_agent: Some(agent.to_string()),
        exit_code: None,
    }
}

fn has_positional_arguments(args: &[String]) -> bool {
    let parsed = parse_args(args);
    !parsed.messages.is_empty() || !parsed.file_args.is_empty()
}

fn has_conflicting_attach_option(args: &[String]) -> bool {
    args.iter().any(|arg| {
        arg == "--resume"
            || arg == "-r"
            || arg.starts_with("--resume=")
            || arg == "--continue"
            || arg == "-c"
            || arg == "--fork"
    })
}

fn rewrite_nested_command(
    parent: &str,
    subcommand: &str,
    flag: &str,
    args: &[String],
) -> PublicCommandResult {
    if args.first().map(String::as_str) != Some(subcommand) {
        let candidate = args.first().map(String::as_str);
        return match candidate {
            Some(candidate) => {
                let suggestion = find_command_suggestion(candidate, &[subcommand]);
                fail(
                    format!("Unknown {parent} command: {candidate}"),
                    Some(suggestion.map_or_else(
                        || format!("Run \"{APP_NAME} help {parent}\" for usage."),
                        |s| format!("Did you mean \"{APP_NAME} {parent} {s}\"?"),
                    )),
                )
            }
            None => fail(
                format!("Missing {parent} command."),
                Some(format!("Run \"{APP_NAME} help {parent}\" for usage.")),
            ),
        };
    }
    let usage = get_command_spec(&[parent, subcommand]).map_or_else(
        || format!("{APP_NAME} {parent} {subcommand}"),
        |spec| format!("{APP_NAME} {}", spec.usage),
    );
    let Some((operands, options)) = split_operands_and_options(&args[1..]) else {
        return fail(format!("Usage: {usage}"), None);
    };
    let valid_count = if parent == "model" {
        operands.len() <= 1
    } else {
        !operands.is_empty() && operands.len() <= 2
    };
    if !valid_count {
        return fail(format!("Usage: {usage}"), None);
    }
    let mut args: Vec<String> = vec![
        INTERNAL_RUNTIME_COMMAND_MARKER.to_string(),
        flag.to_string(),
    ];
    args.extend(operands);
    args.extend(options);
    continue_with(args)
}

fn split_operands_and_options(args: &[String]) -> Option<(Vec<String>, Vec<String>)> {
    let options_start = args.iter().position(|arg| arg.starts_with('-'));
    match options_start {
        None => Some((args.to_vec(), vec![])),
        Some(start) => {
            let options = &args[start..];
            if has_positional_arguments(options) {
                return None;
            }
            Some((args[..start].to_vec(), options.to_vec()))
        }
    }
}

fn require_operand_count(
    args: &[String],
    minimum: usize,
    maximum: Option<usize>,
    command: &str,
) -> bool {
    let mut operands: Vec<&str> = Vec::new();
    let mut index = 0;
    while index < args.len() {
        let arg = args[index].as_str();
        if arg == "--json" {
            index += 1;
            continue;
        }
        if arg == "--socket" || arg == "--daemon-socket" {
            index += 2;
            continue;
        }
        if arg.starts_with('-') {
            fail(
                format!(
                    "Usage: {APP_NAME} {}",
                    get_command_spec(&[command]).map_or(command, |s| s.usage)
                ),
                None,
            );
            return false;
        }
        operands.push(arg);
        index += 1;
    }
    if operands.len() >= minimum && maximum.is_none_or(|max| operands.len() <= max) {
        return true;
    }
    fail(
        format!(
            "Usage: {APP_NAME} {}",
            get_command_spec(&[command]).map_or(command, |s| s.usage)
        ),
        None,
    );
    false
}

/// The incident command's dispatch contract (the TS public-command.test.ts
/// incident suite): parsed options and a once-resolved window reach
/// `run_incident`; usage errors fail with exit code 1 and the help hint.
#[cfg(test)]
mod incident_dispatch_tests {
    use super::*;

    fn args(values: &[&str]) -> Vec<String> {
        values
            .iter()
            .map(std::string::ToString::to_string)
            .collect()
    }

    #[test]
    fn routes_the_incident_command_with_parsed_window_options() {
        // The routed dispatch parses the options, resolves the window
        // once, and runs the command (over whatever logs exist under the
        // agent dir -- the fixture-backed coverage lives in the incident
        // module's own tests); a routed run never fails with a usage
        // error.
        let result = handle_public_command(&args(&[
            "incident",
            "--since",
            "20:02",
            "--until=21:00",
            "--session",
            "abc",
        ]));
        assert!(result.handled);
        assert_eq!(result.exit_code, None);
        assert!(result.args.is_empty());
    }

    #[test]
    fn rejects_unknown_incident_options_with_usage_guidance() {
        let result = handle_public_command(&args(&["incident", "--json"]));
        assert!(result.handled);
        assert_eq!(result.exit_code, Some(1));
    }

    #[test]
    fn rejects_an_unordered_incident_window_with_usage_guidance() {
        let result = handle_public_command(&args(&[
            "incident",
            "--since",
            "2026-09-10T20:30",
            "--until",
            "2026-09-10T20:00",
        ]));
        assert!(result.handled);
        assert_eq!(result.exit_code, Some(1));
    }

    #[test]
    fn rejects_a_bad_incident_time_with_usage_guidance() {
        let result = handle_public_command(&args(&["incident", "--since", "yesterday"]));
        assert!(result.handled);
        assert_eq!(result.exit_code, Some(1));
    }

    #[test]
    fn shows_incident_in_the_top_level_command_list() {
        assert!(format_top_level_help().contains("incident"));
    }

    #[test]
    fn the_incident_help_matches_the_ts_spec() {
        let help = format_command_help(&["incident"]).expect("the incident spec");
        assert!(
            help.contains("Reconstruct a daemon incident from its logs"),
            "{help}"
        );
        assert!(
            help.contains("--since <time>  Window start (ISO date/time, date, or HH:MM today; default: 24h ago)"),
            "{help}"
        );
        assert!(
            help.contains("Times without a timezone are read as UTC"),
            "{help}"
        );
    }
}
