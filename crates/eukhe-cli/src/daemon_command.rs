//! The daemon-backed command runner behind the public commands `list`,
//! `sessions`, `stop`, `rename`, `state`, `send`, and `schedule`: argument parsing,
//! request shaping, and output rendering. Ported from
//! `cli/daemon-command.ts` (the `handleDaemonCommand` surface reachable
//! from public routing).
//!
//! `schedule` maps to the internal `cron` command and `stop` to `kill`, exactly
//! like `runInternalAgentCommand`/`runNestedAgentCommand` in public-command.ts.

use std::collections::HashMap;
use std::path::{Path, PathBuf};

use anyhow::{anyhow, bail, Context, Result};
use eukhe_tui::daemon_client::{
    is_connect_failure, is_daemon_timeout, is_foreign_daemon, DaemonClient, DaemonClientEvent,
    DEFAULT_REQUEST_TIMEOUT_MS,
};
use eukhe_types::daemon::{
    DaemonCommand, DaemonProtocolInfo, DaemonResponse, StateRewindPlanReply, StateTreeEffect,
    StateTreeNode, StateTreeOp, StateTreeRecord, StateTreeReply, StateTreeSnapshot, StopOutcome,
    DAEMON_PROTOCOL_VERSION,
};
use serde_json::{json, Value};
use tokio::sync::mpsc::UnboundedReceiver;

use crate::daemon_session_list::{
    format_session_list_table, get_session_summaries, live_session_summary,
    matches_session_id_suffix,
};

/// Parsed arguments for one daemon client command.
#[derive(Debug)]
struct ParsedDaemonCommand {
    socket_path: PathBuf,
    json: bool,
    positionals: Vec<String>,
    /// `--help`/`-h` becomes the internal no-op `help` command, exactly like
    /// the TS `runDaemonClientCommand` fallthrough. The public router
    /// intercepts help requests before this layer.
    help: bool,
}

/// Run one internal daemon command. Errors are printed by the public command
/// router exactly like the `handleDaemonCommand` catch in the TS CLI.
pub(crate) fn run_daemon_command(command: &str, args: &[String]) -> Result<()> {
    let parsed = parse_daemon_command(command, args)?;
    if parsed.help {
        return Ok(());
    }
    let mut client = Daemon::connect(&parsed.socket_path)?;
    match command {
        "list" => run_list(&mut client, &parsed.positionals, parsed.json),
        "sessions" => run_sessions(&mut client, &parsed.positionals, parsed.json),
        "kill" => run_kill(&mut client, &parsed.positionals, parsed.json),
        "rename" => run_rename(&mut client, &parsed.positionals, parsed.json),
        "state" => run_state(&mut client, &parsed.positionals, parsed.json),
        "send" => run_send(&mut client, &parsed.positionals, parsed.json),
        "cron" => run_cron(&mut client, &parsed.positionals, parsed.json),
        other => bail!("Unknown daemon command: {other}"),
    }
}

/// The CLI's hello budget: TS `waitForHello` waits 3s; 15s lets daemons busy
/// loading large sessions still greet.
pub(crate) const HELLO_TIMEOUT_MS: u64 = 15_000;

/// A daemon connection for the synchronous commands: requests block on the
/// connection's own current-thread runtime.
struct Daemon {
    runtime: tokio::runtime::Runtime,
    client: DaemonClient,
    events: UnboundedReceiver<DaemonClientEvent>,
}

impl Daemon {
    fn connect(socket_path: &Path) -> Result<Self> {
        let runtime = tokio::runtime::Builder::new_current_thread()
            .enable_all()
            .build()?;
        let (client, events) = runtime
            .block_on(DaemonClient::connect_probe(socket_path, HELLO_TIMEOUT_MS))
            .map_err(|error| connect_error(error, socket_path))?;
        Ok(Self {
            runtime,
            client,
            events,
        })
    }

    fn request(&mut self, command: DaemonCommand) -> Result<DaemonResponse> {
        self.runtime.block_on(request(
            &self.client,
            &mut self.events,
            command,
            DEFAULT_REQUEST_TIMEOUT_MS,
        ))
    }
}

/// A [`DaemonClient::connect_probe`] failure in the CLI's words: Node's
/// `connect` text for an unreachable socket, and the daemon log path on
/// every endpoint failure.
pub(crate) fn connect_error(error: anyhow::Error, socket_path: &Path) -> anyhow::Error {
    if is_daemon_timeout(&error) {
        return anyhow!(
            "{error} Daemon log: {}.",
            daemon_log_path(socket_path).display()
        );
    }
    if is_connect_failure(&error) {
        let detail = error
            .chain()
            .find_map(|cause| cause.downcast_ref::<std::io::Error>())
            .map_or_else(
                || error.root_cause().to_string(),
                |io_error| node_connect_error(io_error, socket_path),
            );
        return anyhow!(
            "Failed to connect to the Eukhe daemon: {detail}. {}",
            endpoint_details(socket_path)
        );
    }
    if is_foreign_daemon(&error) {
        return error;
    }
    closed_error(None, socket_path)
}

/// One request in the CLI's words: daemons older than this protocol are
/// refused before sending, and timeouts and closes name the command, the
/// daemon's closing reason, and the daemon log.
pub(crate) async fn request(
    client: &DaemonClient,
    events: &mut UnboundedReceiver<DaemonClientEvent>,
    command: DaemonCommand,
    timeout_ms: u64,
) -> Result<DaemonResponse> {
    let command_type = eukhe_daemon::protocol::command_type_name(&command).to_string();
    let protocol: DaemonProtocolInfo = client
        .hello()
        .get("protocol")
        .cloned()
        .and_then(|value| serde_json::from_value(value).ok())
        .ok_or_else(|| anyhow!("invalid daemon hello"))?;
    if protocol.version < DAEMON_PROTOCOL_VERSION {
        bail!("The running Eukhe daemon does not support {command_type}.");
    }
    let socket_path = client.socket_path();
    client
        .request_with_timeout(command, timeout_ms)
        .await
        .map_err(|error| {
            if is_daemon_timeout(&error) {
                anyhow!(
                    "Timed out after {timeout_ms}ms waiting for the Eukhe daemon response to \"{command_type}\". {}",
                    endpoint_details(socket_path)
                )
            } else if *client.reader_dead().borrow() {
                let mut reason = None;
                while let Ok(event) = events.try_recv() {
                    if let DaemonClientEvent::DaemonClosing { reason: closing } = event {
                        reason = Some(closing);
                    }
                }
                closed_error(reason.as_deref(), socket_path)
            } else {
                error
            }
        })
}

fn closed_error(reason: Option<&str>, socket_path: &Path) -> anyhow::Error {
    let reason = reason
        .map(|reason| format!(" Reason: {reason}."))
        .unwrap_or_default();
    anyhow!(
        "Connection to the Eukhe daemon closed.{reason} {}",
        endpoint_details(socket_path)
    )
}

fn daemon_log_path(socket_path: &Path) -> PathBuf {
    eukhe_daemon::paths::daemon_log_path(socket_path, &crate::config::get_agent_dir())
}

/// `Socket: <path>. Daemon log: <log path>.` (TS `daemonEndpointDetails`).
fn endpoint_details(socket_path: &Path) -> String {
    format!(
        "Socket: {}. Daemon log: {}.",
        socket_path.display(),
        daemon_log_path(socket_path).display()
    )
}

/// Node's `connect` error text for the same failure (`connect ENOENT
/// <path>` and friends).
fn node_connect_error(error: &std::io::Error, socket_path: &Path) -> String {
    let path = socket_path.display();
    match error.kind() {
        std::io::ErrorKind::NotFound => format!("connect ENOENT {path}"),
        std::io::ErrorKind::ConnectionRefused => format!("connect ECONNREFUSED {path}"),
        std::io::ErrorKind::PermissionDenied => format!("connect EACCES {path}"),
        _ => error.to_string(),
    }
}

/// Port of `parseDaemonClientCommand`: option scanning with `--` passthrough
/// semantics (`send`/`cron` keep the separator as an operand, the others
/// consume it). The command name is fixed by the public router.
fn parse_daemon_command(command: &str, args: &[String]) -> Result<ParsedDaemonCommand> {
    let mut socket_path = default_socket_path();
    let mut json = false;
    let mut positionals: Vec<String> = Vec::new();
    let mut passthrough = false;
    let mut index = 0;
    while index < args.len() {
        let arg = args[index].as_str();
        index += 1;
        if passthrough {
            positionals.push(arg.to_string());
            continue;
        }
        // send/cron parse `--` themselves as an end-of-flags separator.
        if arg == "--" {
            if command == "cron" || command == "send" {
                positionals.push(arg.to_string());
            }
            passthrough = true;
            continue;
        }
        // `--help`/`-h` before the command becomes the internal `help`
        // command, which prints nothing; the public router intercepts help
        // requests before this layer, so the branch only preserves parity.
        if arg == "--help" || arg == "-h" {
            return Ok(ParsedDaemonCommand {
                socket_path,
                json,
                positionals,
                help: true,
            });
        }
        if arg == "--socket" || arg == "--daemon-socket" {
            let value = args
                .get(index)
                .ok_or_else(|| anyhow!("{arg} requires a value"))?;
            index += 1;
            socket_path = normalize_socket_path(value);
            continue;
        }
        if arg == "--json" {
            json = true;
            continue;
        }
        positionals.push(arg.to_string());
    }
    Ok(ParsedDaemonCommand {
        socket_path,
        json,
        positionals,
        help: false,
    })
}

fn default_socket_path() -> PathBuf {
    crate::config::resolve_daemon_socket_path(None)
}

/// `normalizeSocketPath`: lexically resolve against the current directory.
fn normalize_socket_path(value: &str) -> PathBuf {
    let path = Path::new(value);
    if path.is_absolute() {
        path.to_path_buf()
    } else {
        std::env::current_dir()
            .unwrap_or_else(|_| PathBuf::from("."))
            .join(path)
    }
}

/// `requireSuccess`: surface the daemon's error text.
fn require_success(response: DaemonResponse) -> Result<Option<Value>> {
    if !response.success {
        return Err(anyhow!(response.error.unwrap_or_default()));
    }
    Ok(response.data)
}

fn print_json(value: &Value) {
    match serde_json::to_string_pretty(value) {
        Ok(text) => println!("{text}"),
        Err(error) => eprintln!("Error: {error}"),
    }
}

/// `requireActiveSessionId`: the first operand.
fn require_active_session_id(args: &[String]) -> Result<String> {
    args.first()
        .cloned()
        .ok_or_else(|| anyhow!("Missing agent id or name"))
}

// ---------------------------------------------------------------------------
// list
// ---------------------------------------------------------------------------

fn run_list(client: &mut Daemon, args: &[String], json: bool) -> Result<()> {
    let mut all = false;
    for arg in args {
        if arg == "-a" || arg == "--all" {
            all = true;
            continue;
        }
        bail!("Unknown list option: {arg}");
    }
    let response = client.request(list_command(all))?;
    let data = require_success(response)?.unwrap_or(Value::Null);
    if json {
        print_json(&data);
        return Ok(());
    }
    let Some(sessions) = get_session_summaries(&data) else {
        print_json(&data);
        return Ok(());
    };
    if sessions.is_empty() {
        println!(
            "{}",
            if all {
                "No agents."
            } else {
                "No active agents."
            }
        );
        return Ok(());
    }
    println!("{}", format_session_list_table(&sessions));
    Ok(())
}

fn list_command(all: bool) -> DaemonCommand {
    DaemonCommand::List {
        id: None,
        all: Some(all),
        cwd: None,
        session_dir: None,
        include_client_owned: None,
        rest: serde_json::Map::new(),
    }
}

// ---------------------------------------------------------------------------
// sessions
// ---------------------------------------------------------------------------

/// The same list RPC as `eukhe list`, rendered as the
/// one-line-per-agent operator table (TS `runSessions`).
fn run_sessions(client: &mut Daemon, args: &[String], json: bool) -> Result<()> {
    let mut all = false;
    for arg in args {
        if arg == "-a" || arg == "--all" {
            all = true;
            continue;
        }
        bail!("Unknown sessions option: {arg}");
    }
    let response = client.request(list_command(all))?;
    let data = require_success(response)?.unwrap_or(Value::Null);
    if json {
        print_json(&data);
        return Ok(());
    }
    let Some(sessions) = crate::daemon_session_list::validated_session_values(&data) else {
        print_json(&data);
        return Ok(());
    };
    if sessions.is_empty() {
        println!(
            "{}",
            if all {
                "No agents."
            } else {
                "No active agents."
            }
        );
        return Ok(());
    }
    println!(
        "{}",
        crate::sessions_table_format::format_sessions_table(
            &sessions,
            crate::daemon_session_list::now_ms()
        )
    );
    Ok(())
}

/// `resolveLiveSessionSelector`: match a name/id/session-id selector against
/// the live session list, with unambiguous hex-suffix fallback.
fn resolve_live_session_selector(client: &mut Daemon, selector: &str) -> Result<String> {
    let response = client.request(list_command(false))?;
    let data = require_success(response)?;
    let sessions = data
        .as_ref()
        .and_then(|data| data.get("sessions"))
        .and_then(Value::as_array)
        .ok_or_else(|| anyhow!("Daemon returned an invalid list response"))?;
    let mut exact: Vec<String> = Vec::new();
    let mut suffix: Vec<String> = Vec::new();
    for session in sessions {
        let Some(active_session_id) = session.get("activeSessionId").and_then(Value::as_str) else {
            continue;
        };
        let session_id = session.get("sessionId").and_then(Value::as_str);
        let session_name = session.get("sessionName").and_then(Value::as_str);
        if active_session_id == selector
            || session_id == Some(selector)
            || session_name == Some(selector)
        {
            exact.push(active_session_id.to_string());
            continue;
        }
        if matches_session_id_suffix(active_session_id, selector)
            || session_id.is_some_and(|id| matches_session_id_suffix(id, selector))
        {
            suffix.push(active_session_id.to_string());
        }
    }
    let matches = if exact.is_empty() { suffix } else { exact };
    match matches.len() {
        1 => Ok(matches[0].clone()),
        0 => Err(anyhow!("Unknown active session: {selector}")),
        _ => Err(anyhow!("Ambiguous active session \"{selector}\"")),
    }
}

// ---------------------------------------------------------------------------
// kill (stop)
// ---------------------------------------------------------------------------

fn run_kill(client: &mut Daemon, args: &[String], json: bool) -> Result<()> {
    let active_session_id = require_active_session_id(args)?;
    let response = client.request(DaemonCommand::Kill {
        id: None,
        active_session_id,
        rest: serde_json::Map::new(),
    })?;
    let outcome = response
        .data
        .as_ref()
        .and_then(|data| data.get("stopOutcome"))
        .cloned();
    let (false, Some(outcome)) = (json, outcome) else {
        return print_response_data(&response, json);
    };
    require_success(response)?;
    let outcome: StopOutcome =
        serde_json::from_value(outcome).context("malformed stopOutcome in the kill response")?;
    match outcome {
        StopOutcome::Settled => println!("ok"),
        StopOutcome::ForcedEffectsUnknown => println!(
            "ok (killed after the stop grace; the effects of its in-flight work are unknown)"
        ),
        StopOutcome::Survived => {
            bail!("the session worker outlived the stop; the next daemon start finishes the stop")
        }
    }
    Ok(())
}

/// `printResponseData`: pretty-print the response data (the whole response as
/// JSON when there is none and `--json` was asked), else `ok`.
fn print_response_data(response: &eukhe_types::daemon::DaemonResponse, json: bool) -> Result<()> {
    let data = require_success(response.clone())?;
    if json || data.is_some() {
        let value = data.unwrap_or_else(|| response_value(response));
        print_json(&value);
        return Ok(());
    }
    println!("ok");
    Ok(())
}

/// The response as the TS wire shape (`data ?? response` prints the frame the
/// daemon sent, including the `type` tag the typed struct does not carry).
fn response_value(response: &eukhe_types::daemon::DaemonResponse) -> Value {
    let mut value = json!({
        "type": "response",
        "command": response.command,
        "success": response.success,
    });
    let object = value.as_object_mut().expect("response object");
    if let Some(id) = &response.id {
        object.insert("id".to_string(), json!(id));
    }
    if let Some(data) = &response.data {
        object.insert("data".to_string(), data.clone());
    }
    if let Some(error) = &response.error {
        object.insert("error".to_string(), json!(error));
    }
    value
}

// ---------------------------------------------------------------------------
// rename
// ---------------------------------------------------------------------------

fn run_rename(client: &mut Daemon, args: &[String], json: bool) -> Result<()> {
    let active_session_id = require_active_session_id(args)?;
    let name = args[1..].join(" ").trim().to_string();
    if name.is_empty() {
        bail!("Usage: eukhe rename <agent> <name>");
    }
    let response = client.request(DaemonCommand::Rename {
        id: None,
        active_session_id,
        name: name.clone(),
        renamed_by: None,
        rest: serde_json::Map::new(),
    })?;
    let data = require_success(response)?.unwrap_or(Value::Null);
    if json {
        print_json(&data);
        return Ok(());
    }
    match live_session_summary(&data) {
        Some(summary) => {
            let summary_name = summary.get("sessionName").and_then(Value::as_str);
            println!(
                "Renamed {} to {}",
                summary
                    .get("activeSessionId")
                    .and_then(Value::as_str)
                    .unwrap_or_default(),
                summary_name.unwrap_or(&name)
            );
        }
        None => print_json(&data),
    }
    Ok(())
}

// ---------------------------------------------------------------------------
// state
// ---------------------------------------------------------------------------

/// `state [<agent>] [--since <cursor>] [--follow]` and `state rewind-plan
/// <cursor> [<agent>]`: the session state tree of one live agent.
fn run_state(client: &mut Daemon, args: &[String], json: bool) -> Result<()> {
    let (rewind_target, operands) = match args.split_first() {
        Some((first, rest)) if first == "rewind-plan" => {
            let (cursor, rest) = rest
                .split_first()
                .ok_or_else(|| anyhow!("Usage: eukhe state rewind-plan <cursor> [<agent>]"))?;
            let cursor: u64 = cursor
                .parse()
                .with_context(|| format!("invalid cursor: {cursor}"))?;
            (Some(cursor), rest)
        }
        Some(_) | None => (None, args),
    };
    let mut since: Option<u64> = None;
    let mut follow = false;
    let mut selector: Option<&str> = None;
    let mut index = 0;
    while index < operands.len() {
        let operand = operands[index].as_str();
        index += 1;
        if operand == "--since" && rewind_target.is_none() {
            let value = operands
                .get(index)
                .ok_or_else(|| anyhow!("--since requires a cursor"))?;
            index += 1;
            since = Some(
                value
                    .parse()
                    .with_context(|| format!("invalid cursor: {value}"))?,
            );
            continue;
        }
        if operand == "--follow" && rewind_target.is_none() {
            follow = true;
            continue;
        }
        if selector.is_some() || operand.starts_with("--") {
            bail!("Unknown state operand: {operand}");
        }
        selector = Some(operand);
    }
    let active_session_id = match selector {
        Some(selector) => resolve_live_session_selector(client, selector)?,
        None => only_live_session(client)?,
    };
    let command = match (rewind_target, follow) {
        (Some(cursor), _) => DaemonCommand::GetStateRewindPlan {
            id: None,
            active_session_id: active_session_id.clone(),
            cursor,
            rest: serde_json::Map::new(),
        },
        (None, true) => DaemonCommand::SubscribeStateTree {
            id: None,
            active_session_id: active_session_id.clone(),
            since,
            rest: serde_json::Map::new(),
        },
        (None, false) => DaemonCommand::GetStateTree {
            id: None,
            active_session_id: active_session_id.clone(),
            since,
            rest: serde_json::Map::new(),
        },
    };
    let data = require_success(client.request(command)?)?.unwrap_or(Value::Null);
    if rewind_target.is_some() {
        if json {
            print_json(&data);
            return Ok(());
        }
        let plan: StateRewindPlanReply =
            serde_json::from_value(data).context("malformed state rewind plan")?;
        let mut lines = vec![format!("rewind {} -> {}", plan.cursor, plan.target)];
        for effect in plan.effects {
            let (verb, node) = match effect {
                StateTreeEffect::Start(node) => ("start", node),
                StateTreeEffect::Stop(node) => ("stop", node),
                StateTreeEffect::Restore(node) => ("restore", node),
            };
            lines.push(format!("{verb} {} {}", node.kind.name(), node.key));
        }
        println!("{}", lines.join("\n"));
        return Ok(());
    }
    if json {
        print_json(&data);
    }
    let reply: StateTreeReply = serde_json::from_value(data).context("malformed state tree")?;
    let cursor = match &reply {
        StateTreeReply::Snapshot(snapshot) => snapshot.cursor,
        StateTreeReply::Records(records) => records.cursor,
    };
    if !json {
        let lines = match &reply {
            StateTreeReply::Snapshot(snapshot) => state_snapshot_lines(snapshot),
            StateTreeReply::Records(records) => {
                state_records_lines(records.from, records.cursor, &records.records)
            }
        };
        println!("{}", lines.join("\n"));
    }
    if follow {
        follow_state_tree(client, &active_session_id, cursor, json)?;
    }
    Ok(())
}

/// Print each `state_tree_update` of the subscribed session, from the
/// cursor `have`: a frame the reply already covered is skipped, and an
/// overlapping one prints only its records after `have`. Runs until the
/// connection closes.
fn follow_state_tree(
    client: &mut Daemon,
    active_session_id: &str,
    mut have: u64,
    json: bool,
) -> Result<()> {
    loop {
        let Some(event) = client.runtime.block_on(client.events.recv()) else {
            return Err(closed_error(None, client.client.socket_path()));
        };
        match event {
            DaemonClientEvent::StateTreeUpdate {
                active_session_id: session,
                update,
            } => {
                if session != active_session_id || update.cursor <= have {
                    continue;
                }
                if update.from > have {
                    bail!(
                        "missed the state tree records {have}..{}; run the command again",
                        update.from
                    );
                }
                let skip = usize::try_from(have - update.from)?;
                let records = update.records.get(skip..).unwrap_or_default();
                if json {
                    print_json(
                        &json!({ "from": have, "cursor": update.cursor, "records": records }),
                    );
                } else {
                    println!(
                        "{}",
                        state_records_lines(have, update.cursor, records).join("\n")
                    );
                }
                have = update.cursor;
            }
            DaemonClientEvent::DaemonClosing { reason } => {
                return Err(closed_error(Some(&reason), client.client.socket_path()));
            }
            DaemonClientEvent::SessionClosed {
                active_session_id: session,
                reason,
            } => {
                if session == active_session_id {
                    bail!("The agent session closed ({reason}).");
                }
            }
            DaemonClientEvent::SessionEvent { .. }
            | DaemonClientEvent::UndecodableSessionEvent { .. }
            | DaemonClientEvent::DirectLinkLost { .. }
            | DaemonClientEvent::SessionListItem { .. }
            | DaemonClientEvent::SessionListProgress { .. }
            | DaemonClientEvent::SideQuestionEvent { .. }
            | DaemonClientEvent::ShellApproval { .. }
            | DaemonClientEvent::ShellApprovalSettled { .. }
            | DaemonClientEvent::RosterUpdate { .. }
            | DaemonClientEvent::HeartbeatsChanged
            | DaemonClientEvent::SessionBinding { .. } => {}
        }
    }
}

/// Records as `eukhe state --since` prints them: `cursor <to> (from
/// <from>)`, then one line per change.
fn state_records_lines(from: u64, to: u64, records: &[StateTreeRecord]) -> Vec<String> {
    let mut lines = vec![format!("cursor {to} (from {from})")];
    for record in records {
        match record {
            StateTreeRecord::Do(op) => lines.push(state_op_line(op)),
            StateTreeRecord::Rewind(ops) => {
                lines.push("rewind".to_string());
                lines.extend(ops.iter().map(|op| format!("  {}", state_op_line(op))));
            }
        }
    }
    lines
}

/// The snapshot as `eukhe state` prints it: the cursor, then each node as
/// `<kind> <key>`, indented two spaces per level under its parent.
fn state_snapshot_lines(snapshot: &StateTreeSnapshot) -> Vec<String> {
    let mut lines = vec![format!("cursor {}", snapshot.cursor)];
    // Parents come before their children in id order, so one pass knows
    // the depth of every parent. A top node hangs under the root (`0`).
    let mut depths: HashMap<u64, usize> = HashMap::new();
    let mut children: HashMap<u64, Vec<&StateTreeNode>> = HashMap::new();
    for node in &snapshot.nodes {
        let depth = depths.get(&node.parent).map_or(0, |depth| depth + 1);
        depths.insert(node.id, depth);
        children.entry(node.parent).or_default().push(node);
    }
    let mut stack: Vec<&StateTreeNode> = children
        .get(&0)
        .map(|top| top.iter().rev().copied().collect())
        .unwrap_or_default();
    while let Some(node) = stack.pop() {
        let depth = depths.get(&node.id).copied().unwrap_or_default();
        lines.push(format!(
            "{}{} {}",
            "  ".repeat(depth),
            node.kind.name(),
            node.key
        ));
        if let Some(below) = children.get(&node.id) {
            stack.extend(below.iter().rev().copied());
        }
    }
    lines
}

/// One state tree change: `put <kind> <key> #<id> under #<parent>` or
/// `del #<id>`.
fn state_op_line(op: &StateTreeOp) -> String {
    match op {
        StateTreeOp::Put(node) => format!(
            "put {} {} #{} under #{}",
            node.kind.name(),
            node.key,
            node.id,
            node.parent
        ),
        StateTreeOp::Del { id } => format!("del #{id}"),
    }
}

/// The one live agent, for a command without an agent operand.
fn only_live_session(client: &mut Daemon) -> Result<String> {
    let data = require_success(client.request(list_command(false))?)?;
    let ids: Vec<&str> = data
        .as_ref()
        .and_then(|data| data.get("sessions"))
        .and_then(Value::as_array)
        .ok_or_else(|| anyhow!("Daemon returned an invalid list response"))?
        .iter()
        .filter_map(|session| session.get("activeSessionId").and_then(Value::as_str))
        .collect();
    match ids.as_slice() {
        [id] => Ok((*id).to_string()),
        [] => Err(anyhow!("No active agents.")),
        _ => Err(anyhow!(
            "Several active agents; name one (see \"eukhe list\")."
        )),
    }
}

// ---------------------------------------------------------------------------
// send
// ---------------------------------------------------------------------------

struct ParsedSendArgs {
    target_active_session_id: String,
    from_active_session_id: Option<String>,
    message: String,
}

fn run_send(client: &mut Daemon, args: &[String], json: bool) -> Result<()> {
    let parsed = parse_send_args(args)?;
    let response = client.request(DaemonCommand::SendMessage {
        id: None,
        target_active_session_id: parsed.target_active_session_id,
        message: parsed.message,
        from_active_session_id: parsed.from_active_session_id,
        agent_origin: None,
        delivery_mode: None,
        rest: serde_json::Map::new(),
    })?;
    let data = require_success(response)?.unwrap_or(Value::Null);
    if json {
        print_json(&data);
        return Ok(());
    }
    // `isAgentMessageReceipt`: a target block with a routable active id.
    let receipt_target = data
        .get("target")
        .filter(|target| {
            target
                .get("activeSessionId")
                .and_then(Value::as_str)
                .is_some()
        })
        .and_then(|target| {
            target
                .get("sessionName")
                .and_then(Value::as_str)
                .or_else(|| target.get("activeSessionId").and_then(Value::as_str))
        })
        .map(str::to_string);
    let Some(target) = receipt_target else {
        println!("ok");
        return Ok(());
    };
    let queued = data.get("deliveryStatus").and_then(Value::as_str) == Some("queued");
    println!(
        "{}",
        if queued {
            format!("Queued for {target}")
        } else {
            format!("Sent to {target}")
        }
    );
    Ok(())
}

fn parse_send_args(args: &[String]) -> Result<ParsedSendArgs> {
    let mut from_active_session_id: Option<String> = None;
    let mut target_active_session_id: Option<String> = None;
    let mut explicit_message: Option<String> = None;
    let mut message_parts: Vec<String> = Vec::new();
    let mut parse_options = true;
    let mut index = 0;
    while index < args.len() {
        let arg = args[index].as_str();
        index += 1;
        if parse_options && arg == "--" {
            parse_options = false;
            continue;
        }
        if parse_options && arg == "--from" {
            let value = args
                .get(index)
                .ok_or_else(|| anyhow!("--from requires a session id or name"))?;
            index += 1;
            from_active_session_id = Some(value.clone());
            continue;
        }
        if parse_options && arg == "--message" {
            if target_active_session_id.is_none() {
                bail!("--message must appear after the target session");
            }
            let value = args
                .get(index)
                .ok_or_else(|| anyhow!("--message requires message text"))?;
            index += 1;
            explicit_message = Some(value.clone());
            parse_options = false;
            continue;
        }
        if parse_options && arg.starts_with("--") {
            bail!("Unknown option for send: {arg} (use -- before message text starting with --)");
        }
        if target_active_session_id.is_none() {
            target_active_session_id = Some(arg.to_string());
            continue;
        }
        message_parts.push(arg.to_string());
    }
    if explicit_message.is_some() && !message_parts.is_empty() {
        bail!("Usage: eukhe send [--from <agent>] <agent> [--message <message>|<message>]");
    }
    let message = explicit_message
        .unwrap_or_else(|| message_parts.join(" "))
        .trim()
        .to_string();
    if target_active_session_id.is_none() || message.is_empty() {
        bail!("Usage: eukhe send [--from <agent>] <agent> [--message <message>|<message>]");
    }
    Ok(ParsedSendArgs {
        target_active_session_id: target_active_session_id.expect("checked above"),
        from_active_session_id,
        message,
    })
}

// ---------------------------------------------------------------------------
// cron (schedule)
// ---------------------------------------------------------------------------

fn run_cron(client: &mut Daemon, args: &[String], json: bool) -> Result<()> {
    let subcommand = args.first().map_or("list", String::as_str);
    match subcommand {
        "list" => run_cron_list(client, args, json),
        "add" | "schedule" => run_cron_add(client, args, json),
        "cancel" | "delete" | "remove" => run_cron_cancel(client, args, json),
        other => bail!("Unknown schedule command: {other}"),
    }
}

fn run_cron_list(client: &mut Daemon, args: &[String], json: bool) -> Result<()> {
    let include_inactive = args.iter().skip(1).any(|arg| arg == "--all" || arg == "-a");
    let selector = args
        .iter()
        .skip(1)
        .find(|arg| !arg.starts_with('-') && arg.as_str() != "list");
    let active_session_id = match selector {
        Some(selector) => Some(resolve_live_session_selector(client, selector)?),
        None => None,
    };
    let response = client.request(DaemonCommand::CronList {
        id: None,
        active_session_id,
        include_inactive: Some(include_inactive),
        rest: serde_json::Map::new(),
    })?;
    let data = require_success(response)?.unwrap_or(Value::Null);
    if json {
        print_json(&data);
        return Ok(());
    }
    let Some(jobs) = data.get("jobs").and_then(Value::as_array) else {
        print_json(&data);
        return Ok(());
    };
    if jobs.is_empty() {
        println!("No scheduled prompts.");
        return Ok(());
    }
    for job in jobs {
        println!("{}", format_agent_cron_job(job));
    }
    Ok(())
}

fn run_cron_add(client: &mut Daemon, args: &[String], json: bool) -> Result<()> {
    let usage = "Usage: eukhe schedule add <agent> <schedule> -- <message>";
    let separator = args
        .iter()
        .position(|arg| arg == "--")
        .ok_or_else(|| anyhow!("{usage}"))?;
    let Some(active_session_id) = args.get(1) else {
        bail!("{usage}");
    };
    if separator < 2 {
        bail!("{usage}");
    }
    let schedule = args[2..separator].join(" ").trim().to_string();
    let message = args[separator + 1..].join(" ").trim().to_string();
    if schedule.is_empty() || message.is_empty() {
        bail!("{usage}");
    }
    let response = client.request(DaemonCommand::CronAdd {
        id: None,
        active_session_id: active_session_id.clone(),
        schedule,
        prompt: message,
        promote_owned_session: None,
        rest: serde_json::Map::new(),
    })?;
    let data = require_success(response)?.unwrap_or(Value::Null);
    if json {
        print_json(&data);
        return Ok(());
    }
    match cron_job_id_and_next_run(&data) {
        Some((id, next_run)) => println!("Scheduled {id} next={next_run}"),
        None => println!("Scheduled prompt."),
    }
    Ok(())
}

fn run_cron_cancel(client: &mut Daemon, args: &[String], json: bool) -> Result<()> {
    let Some(job_id) = args.get(1) else {
        bail!("Usage: eukhe schedule cancel <job-id>");
    };
    let response = client.request(DaemonCommand::CronCancel {
        id: None,
        active_session_id: None,
        job_id: job_id.clone(),
        rest: serde_json::Map::new(),
    })?;
    let data = require_success(response)?.unwrap_or(Value::Null);
    if json {
        print_json(&data);
        return Ok(());
    }
    match cron_job_id_and_next_run(&data) {
        Some((id, _)) => println!("Cancelled {id}"),
        None => println!("Cancelled cron job."),
    }
    Ok(())
}

/// `getCronJob`: the job id and next run when the response carries a job.
fn cron_job_id_and_next_run(data: &Value) -> Option<(String, String)> {
    let job = data.get("job")?;
    let id = job.get("id").and_then(Value::as_str)?.to_string();
    let next_run = job
        .get("nextRunAt")
        .and_then(Value::as_str)
        .map_or_else(|| "-".to_string(), str::to_string);
    Some((id, next_run))
}

/// `formatAgentCronJob`: the one-line schedule list entry.
fn format_agent_cron_job(job: &Value) -> String {
    let id = job.get("id").and_then(Value::as_str).unwrap_or_default();
    let status = job
        .get("status")
        .and_then(Value::as_str)
        .unwrap_or_default();
    let label = job
        .get("label")
        .and_then(Value::as_str)
        .map(|label| format!(" label=\"{label}\""))
        .unwrap_or_default();
    let next = cron_datetime(job.get("nextRunAt"));
    let last = cron_datetime(job.get("lastRunAt"));
    let skipped = job
        .get("lastSkippedAt")
        .map(|value| format!(" skipped={}", cron_datetime(Some(value))))
        .unwrap_or_default();
    let run_count = job
        .get("runCount")
        .and_then(Value::as_f64)
        .unwrap_or_default();
    let expression = job
        .get("schedule")
        .and_then(|schedule| schedule.get("expression"))
        .and_then(Value::as_str)
        .unwrap_or_default();
    let prompt: String = job
        .get("prompt")
        .and_then(Value::as_str)
        .unwrap_or_default()
        .split_whitespace()
        .collect::<Vec<_>>()
        .join(" ");
    let preview: String = prompt.chars().take(80).collect();
    let error = job
        .get("lastError")
        .and_then(Value::as_str)
        .map(|error| format!(" error={error}"))
        .unwrap_or_default();
    format!(
        "{id} {status}{label} next={next} last={last}{skipped} runs={run_count} schedule=\"{expression}\" prompt=\"{preview}\"{error}"
    )
}

/// `toLocaleString()` for a cron timestamp: en-US long-form-ish date with a
/// 12-hour clock, e.g. `9/16/2026, 6:36:59 PM`. Rendered in UTC; a daemon
/// machine running a non-UTC system timezone shifts the wall-clock part.
fn cron_datetime(value: Option<&Value>) -> String {
    let Some(value) = value.and_then(Value::as_str) else {
        return "-".to_string();
    };
    let Some(ms) = crate::daemon_session_list::parse_iso_ms(value) else {
        return "-".to_string();
    };
    let seconds_of_day = (ms / 1000) % 86_400;
    let hour24 = seconds_of_day / 3600;
    let minute = (seconds_of_day % 3600) / 60;
    let second = seconds_of_day % 60;
    let (hour12, meridiem) = match hour24 % 12 {
        0 => (12, if hour24 < 12 { "AM" } else { "PM" }),
        other => (other, if hour24 < 12 { "AM" } else { "PM" }),
    };
    let days = (ms / 1000) / 86_400;
    let (year, month, day) = civil_from_days(days);
    format!("{month}/{day}/{year}, {hour12}:{minute:02}:{second:02} {meridiem}")
}

/// Civil date from days since the epoch (Howard Hinnant's algorithm).
fn civil_from_days(days: u64) -> (i64, u32, u32) {
    let z = days as i64 + 719_468;
    let era = z.div_euclid(146_097);
    let doe = z.rem_euclid(146_097);
    let yoe = (doe - doe / 1460 + doe / 36524 - doe / 146_096) / 365;
    let y = yoe + era * 400;
    let doy = doe - (365 * yoe + yoe / 4 - yoe / 100);
    let mp = (5 * doy + 2) / 153;
    let day = (doy - (153 * mp + 2) / 5 + 1) as u32;
    let month = if mp < 10 { mp + 3 } else { mp - 9 } as u32;
    (if month <= 2 { y + 1 } else { y }, month, day)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn args(list: &[&str]) -> Vec<String> {
        list.iter().map(std::string::ToString::to_string).collect()
    }

    #[test]
    fn parse_consumes_socket_json_and_separator() {
        let parsed =
            parse_daemon_command("list", &args(&["--json", "--socket", "/s", "-a"])).unwrap();
        assert_eq!(parsed.socket_path, PathBuf::from("/s"));
        assert!(parsed.json);
        assert_eq!(parsed.positionals, args(&["-a"]));

        let missing = parse_daemon_command("list", &args(&["--daemon-socket"])).unwrap_err();
        assert_eq!(missing.to_string(), "--daemon-socket requires a value");
    }

    #[test]
    fn separator_passes_through_only_for_send_and_cron() {
        let send = parse_daemon_command("send", &args(&["target", "--", "hi", "there"])).unwrap();
        assert_eq!(send.positionals, args(&["target", "--", "hi", "there"]));
        let list = parse_daemon_command("list", &args(&["--", "-a"])).unwrap();
        assert_eq!(list.positionals, args(&["-a"]));
    }

    #[test]
    fn state_snapshot_lines_indent_each_node_under_its_parent() {
        use eukhe_types::daemon::StateTreeKind;
        let node = |id, parent, kind, key: &str| StateTreeNode {
            id,
            parent,
            kind,
            key: key.to_string(),
            value: Value::Null,
        };
        let snapshot = StateTreeSnapshot {
            cursor: 7,
            seq: Some(4),
            nodes: vec![
                node(1, 0, StateTreeKind::Conversation, "1"),
                node(2, 0, StateTreeKind::Document, "9"),
                node(3, 1, StateTreeKind::Task, "12"),
                node(4, 3, StateTreeKind::Document, "13"),
                node(5, 1, StateTreeKind::Entry, "14"),
            ],
        };
        assert_eq!(
            state_snapshot_lines(&snapshot),
            [
                "cursor 7",
                "conversation 1",
                "  task 12",
                "    document 13",
                "  entry 14",
                "document 9",
            ]
        );
    }

    #[test]
    fn send_args_match_ts_usage_rules() {
        let parsed = parse_send_args(&args(&["--from", "me", "target", "hello", "there"])).unwrap();
        assert_eq!(parsed.target_active_session_id, "target");
        assert_eq!(parsed.from_active_session_id.as_deref(), Some("me"));
        assert_eq!(parsed.message, "hello there");

        let flag = parse_send_args(&args(&["target", "--message", "queued"])).unwrap();
        assert_eq!(flag.message, "queued");

        let explicit_and_positional =
            parse_send_args(&args(&["target", "--message", "queued", "extra"]));
        assert!(explicit_and_positional.is_err());

        let unknown = parse_send_args(&args(&["target", "--bogus"]));
        assert!(unknown.is_err());

        let no_target = parse_send_args(&args(&["--message", "text"]));
        assert!(no_target.is_err());
    }

    #[test]
    fn cron_job_line_matches_captured_ts_golden() {
        let job = json!({
            "id": "0451e5a9-951c-457b-ae76-ea3142ea5d25",
            "status": "active",
            "nextRunAt": "2026-09-16T18:36:59.287Z",
            "runCount": 0,
            "schedule": { "expression": "every 5 minutes" },
            "prompt": "do   the thing",
        });
        assert_eq!(
            format_agent_cron_job(&job),
            "0451e5a9-951c-457b-ae76-ea3142ea5d25 active next=9/16/2026, 6:36:59 PM last=- runs=0 schedule=\"every 5 minutes\" prompt=\"do the thing\""
        );
    }

    #[test]
    fn connect_error_matches_node_text() {
        let dir = tempfile::TempDir::new().unwrap();
        let socket = dir.path().join("missing.sock");
        let error = Daemon::connect(&socket).err().unwrap();
        assert_eq!(
            error.to_string(),
            format!(
                "Failed to connect to the Eukhe daemon: connect ENOENT {}. {}",
                socket.display(),
                endpoint_details(&socket)
            )
        );
    }

    #[test]
    fn socket_close_reports_daemon_closing_reason() {
        use std::io::{BufRead, Write};
        let dir = tempfile::TempDir::new().unwrap();
        let socket = dir.path().join("daemon.sock");
        let listener = std::os::unix::net::UnixListener::bind(&socket).unwrap();
        let server = std::thread::spawn(move || {
            let (mut stream, _) = listener.accept().unwrap();
            stream
                .write_all(b"{\"type\":\"daemon_hello\",\"protocol\":{\"name\":\"eukhe.daemon\",\"version\":7}}\n{\"type\":\"daemon_closing\",\"reason\":\"shutdown\"}\n")
                .unwrap();
            // Drain the request so the close is a clean EOF, not a reset.
            let mut request = String::new();
            std::io::BufReader::new(stream)
                .read_line(&mut request)
                .unwrap();
        });
        let mut daemon = Daemon::connect(&socket).unwrap();
        let error = daemon.request(list_command(false)).unwrap_err();
        assert_eq!(
            error.to_string(),
            format!(
                "Connection to the Eukhe daemon closed. Reason: shutdown. {}",
                endpoint_details(&socket)
            )
        );
        server.join().unwrap();
    }
}
