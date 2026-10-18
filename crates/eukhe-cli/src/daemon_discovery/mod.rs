//! Daemon discovery: find every product daemon in this state root and probe
//! it for identity and session count (TS `cli/daemon-ps.ts`).
//!
//! Discovery merges two sources by socket path: the OS census of listening
//! unix sockets owned by a product process (the only reliable socket->pid
//! mapping when daemons run on arbitrary `--daemon-socket` paths), and a sweep
//! of the default socket dir, which also catches orphaned socket files left
//! by daemons that are no longer running. Worker sockets (tracked by the
//! supervisor's worker descriptors) add their supervisor's socket to the set
//! so a supervisor whose own listener vanished is still reachable for
//! `shutdown --force`.
//!
//! Scope: one *state root*, narrowed by what the invocation names. A
//! command scoped to a socket (`--daemon-socket`, else `EUKHE_DAEMON_SOCKET`)
//! discovers and acts on the daemon on that socket only; one scoped to an
//! agent dir (`EUKHE_CODING_AGENT_DIR`) on the daemons whose sockets sit
//! inside that agent dir only. Only an unscoped invocation sweeps this
//! user's default scope: the per-user default socket dir, the default agent
//! dir, and the default socket. A daemon outside the scope is another
//! root's business (an isolated test daemon, or the user's own daemon seen
//! from an isolated invocation); stopping it from here would kill unrelated
//! live sessions. Reaching any other daemon takes naming its socket. (TS
//! keeps custom socket paths in scope through its supervisor-ownership
//! registry; that registry is not ported.)
//!
//! Containment: every scan, probe, and stop is scoped to an explicit
//! [`DaemonStateRoot`] handed in by the caller -- the CLI passes the
//! env-resolved current root, tests pass only fixture directories they
//! created. A daemon outside the root an invocation was given is invisible
//! to it, always. Unit tests additionally refuse the never-touch dirs (see
//! `NEVER_TOUCH_SOCKET_DIRS`); integration tests pin their whole state root
//! (agent dir, TMPDIR, daemon socket) inside fixtures instead.
//!
//! Pids come from the listener census (by process name) and, for a socket
//! whose holder the census missed (a renamed or older build), from the
//! socket's own holder ([`owner`]), verified as this user's eukhe-family
//! supervisor before anything may signal it.

use std::collections::BTreeSet;
use std::path::{Path, PathBuf};

use eukhe_tui::daemon_client::{is_connect_failure, DaemonClient};
use eukhe_types::daemon::DaemonCommand;
use serde::{Deserialize, Serialize};
use serde_json::Value;

use crate::config;

mod format;
mod kill;
pub(crate) mod owner;
pub(crate) mod plan;
pub(crate) mod scan;
pub(crate) mod stop;

pub(crate) use format::format_daemon_list_table;
pub(crate) use stop::{run_ps, run_reap, run_shutdown_all};

/// One discovered daemon process: an owning pid and the socket it listens on.
#[derive(Debug, Clone)]
pub(crate) struct DiscoveredDaemonProcess {
    pub pid: u32,
    pub socket_path: PathBuf,
    pub uptime_seconds: Option<u64>,
}

/// Which daemons an invocation discovers and acts on (see the module docs).
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum DiscoveryScope {
    /// Nothing named: this user's default scope -- every socket in the
    /// per-user default socket dir, anywhere inside the (default) agent dir,
    /// and the default socket.
    Default { socket_dir: PathBuf },
    /// `--daemon-socket` or `EUKHE_DAEMON_SOCKET`: the root's socket only.
    Socket,
    /// `EUKHE_CODING_AGENT_DIR` without a named socket: sockets inside the
    /// root's agent dir only.
    AgentDir,
}

/// The state root an invocation reads: the agent dir, the daemon socket this
/// invocation targets, and the scope its env and flags name (TS
/// `DaemonStateRoot`). All follow HOME/TMPDIR/agent-dir/daemon-socket
/// overrides, so an isolated root resolves to isolated paths.
#[derive(Debug, Clone)]
pub(crate) struct DaemonStateRoot {
    pub agent_dir: PathBuf,
    /// The invocation's own daemon socket: `--daemon-socket`, then
    /// `EUKHE_DAEMON_SOCKET`, then the per-user default - the socket every
    /// mode starts its daemon on, so it may sit outside the socket dir.
    pub default_socket_path: PathBuf,
    pub scope: DiscoveryScope,
}

impl DaemonStateRoot {
    /// True when `socket_path` is in this root's scope: the root's own
    /// socket under a socket scope, a socket inside the agent dir under an
    /// agent-dir scope, and either of those or a socket in the default
    /// socket dir under the default scope (TS `createDaemonStateRootMatcher`
    /// minus the not-yet-ported ownership registry rule). Containment
    /// (never-touch paths, the chat lock) is [`state_root_matches`]'s.
    pub(crate) fn scope_contains(&self, socket_path: &Path) -> bool {
        match &self.scope {
            DiscoveryScope::Socket => socket_path == self.default_socket_path,
            DiscoveryScope::AgentDir => inside(socket_path.parent(), &self.agent_dir),
            DiscoveryScope::Default { socket_dir } => {
                socket_path == self.default_socket_path
                    || socket_path.parent() == Some(socket_dir)
                    || inside(socket_path.parent(), &self.agent_dir)
            }
        }
    }
}

/// Directories the lib's unit tests must never touch: the developer box's
/// live product-default socket dirs (`<tmp>/eukhe-<uid>` for uid 1000 and
/// root) and mission sockets. A unit test whose root leaks onto the ambient
/// environment still cannot enumerate, probe, unlink, or stop them. Test
/// builds only: in the shipped binary `/tmp/eukhe-1000` is the real default
/// socket dir, and hiding it would make `status`/`doctor`/`shutdown` blind
/// to the user's own daemon.
#[cfg(test)]
pub(crate) const NEVER_TOUCH_SOCKET_DIRS: &[&str] = &[
    "/tmp/eukhe-1000",
    "/tmp/mission-tmp/eukhe-1000",
    "/tmp/mission-daemon",
    "/tmp/eukhe-0",
    "/tmp/mission-tmp/eukhe-0",
];

/// True when `path` is or sits inside a never-touch directory (unit-test
/// builds only; always false in the product).
pub(crate) fn is_never_touch(path: &Path) -> bool {
    #[cfg(test)]
    {
        NEVER_TOUCH_SOCKET_DIRS
            .iter()
            .any(|dir| path.starts_with(Path::new(dir)))
    }
    #[cfg(not(test))]
    {
        let _ = path;
        false
    }
}

/// Discovered-daemon classification (TS `DaemonStatus`).
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub(crate) enum DaemonStatus {
    Current,
    Stale,
    Unreachable,
    OrphanFile,
}

/// How a discovered daemon's pid was established (TS `pidSource`).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "lowercase")]
pub(crate) enum PidSource {
    Listener,
    Hello,
}

/// One discovered daemon, probed (TS `DaemonInfo`; field order is the TS JSON
/// shape, options omitted exactly like the TS spread/conditionals).
#[derive(Debug, Clone, Serialize)]
#[serde(rename_all = "camelCase")]
pub(crate) struct DaemonInfo {
    pub socket_path: PathBuf,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub pid: Option<u32>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub uptime_seconds: Option<u64>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub version: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub protocol_version: Option<u64>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub schema_id: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub build_id: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub executable_path: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub pid_source: Option<PidSource>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub session_count: Option<u64>,
    pub status: DaemonStatus,
    pub is_default: bool,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub has_tracked_workers: Option<bool>,
}

/// The current invocation's state root (TS `currentDaemonStateRoot`), for
/// the `--daemon-socket` value the command was given: a named socket (flag
/// or env) scopes it to that socket, else a named agent dir to that agent
/// dir; only an invocation naming neither gets the default scope.
pub(crate) fn current_state_root(daemon_socket: Option<&str>) -> DaemonStateRoot {
    let env_names = |key: &str| std::env::var_os(key).is_some_and(|value| !value.is_empty());
    let scope = if daemon_socket.is_some() || env_names(config::ENV_DAEMON_SOCKET) {
        DiscoveryScope::Socket
    } else if env_names(config::ENV_AGENT_DIR) {
        DiscoveryScope::AgentDir
    } else {
        DiscoveryScope::Default {
            socket_dir: eukhe_daemon::platform::socket_dir(),
        }
    };
    DaemonStateRoot {
        agent_dir: config::get_agent_dir(),
        default_socket_path: config::resolve_daemon_socket_path(daemon_socket),
        scope,
    }
}

/// A socket belongs to the root when it is in the root's scope and not
/// contained away (never-touch paths, the chat memory's lock socket).
fn state_root_matches(root: &DaemonStateRoot, socket_path: &Path) -> bool {
    if is_never_touch(socket_path) {
        return false;
    }
    // The chat memory's lock socket is not a daemon: its owner (usually the
    // supervisor itself) answers only chat requests.
    if socket_path == eukhe_core::memory::chat_dir(&root.agent_dir).join("lock") {
        return false;
    }
    root.scope_contains(socket_path)
}

/// True when `directory` is `parent` or sits below it (TS `isInside`).
fn inside(directory: Option<&Path>, parent: &Path) -> bool {
    let Some(directory) = directory else {
        return false;
    };
    match directory.strip_prefix(parent) {
        Ok(rest) => !rest.as_os_str().is_empty() || directory == parent,
        Err(_) => false,
    }
}

/// Worker sockets: `worker-*.sock` files (TS `isWorkerSocketPath`) -- the
/// supervisor's own socket is never a worker socket. A worker socket sits
/// beside its own supervisor's socket, wherever that is, so the name alone
/// identifies it; every caller applies the state-root scope separately.
pub(crate) fn is_worker_socket_path(socket_path: &Path) -> bool {
    let Some(name) = socket_path.file_name().and_then(|name| name.to_str()) else {
        return false;
    };
    name.starts_with("worker-")
        && std::path::Path::new(name)
            .extension()
            .is_some_and(|ext| ext == "sock")
}

/// Listening daemons in this state root (TS `scanListeningDaemons`). The OS
/// census is filtered to the root inside the scan, before any probe or
/// uptime lookup touches a pid: a scan run from one root can never see --
/// let alone stop -- a daemon in another root.
pub(crate) fn scan_listening_daemons(root: &DaemonStateRoot) -> Vec<DiscoveredDaemonProcess> {
    scan::scan_all_listening_daemons(config::PROCESS_NAME, root)
}

/// True when the pid still listens on exactly this socket (TS
/// `isDaemonProcessListening`): a fresh scan against the same root, so a
/// re-probe sees the same listener set the discovery did, or the socket's
/// verified holder (a renamed build the name census misses).
pub(crate) fn is_daemon_process_listening(
    pid: u32,
    socket_path: &Path,
    root: &DaemonStateRoot,
) -> bool {
    scan_listening_daemons(root)
        .iter()
        .any(|daemon| daemon.pid == pid && daemon.socket_path == socket_path)
        || matches!(
            owner::socket_holder(socket_path),
            Some(owner::SocketHolder::Daemon(holder)) if holder.pid == pid
        )
}

/// Socket files in the given socket dir (TS `scanSocketDir`): live daemons
/// and orphaned files alike. Never-touch paths are filtered out here too,
/// so even a root handed in on purpose cannot sweep them.
fn scan_socket_dir(socket_dir: &Path) -> Vec<PathBuf> {
    let Ok(entries) = std::fs::read_dir(socket_dir) else {
        return Vec::new();
    };
    let mut sockets = Vec::new();
    for entry in entries.flatten() {
        let path = entry.path();
        if is_socket_file(&path) && !is_never_touch(&path) {
            sockets.push(path);
        }
    }
    sockets
}

/// True when the path is a unix socket file.
fn is_socket_file(path: &Path) -> bool {
    use std::os::unix::fs::FileTypeExt;
    std::fs::symlink_metadata(path).is_ok_and(|meta| meta.file_type().is_socket())
}

/// One tracked worker from a supervisor descriptor (TS `TrackedWorker`).
#[derive(Debug, Clone)]
pub(crate) struct TrackedWorker {
    pub descriptor_path: PathBuf,
    pub supervisor_socket_path: PathBuf,
    pub worker_socket_path: PathBuf,
    pub pid: u32,
    pub process_start_id: Option<String>,
    pub recovery_journal_path: PathBuf,
}

/// Every tracked worker recorded in this agent dir (TS `findAllTrackedWorkers`):
/// `daemon-workers/*/<worker>.json` descriptors. The `supervisor-config` file
/// carries no `.json` extension and is skipped by construction.
pub(crate) fn find_all_tracked_workers(agent_dir: &Path) -> Vec<TrackedWorker> {
    let root = agent_dir.join("daemon-workers");
    let Ok(entries) = std::fs::read_dir(&root) else {
        return Vec::new();
    };
    let mut workers = Vec::new();
    for directory in entries.flatten() {
        if !directory.file_type().is_ok_and(|kind| kind.is_dir()) {
            continue;
        }
        let Ok(files) = std::fs::read_dir(directory.path()) else {
            continue;
        };
        for file in files.flatten() {
            if file.file_name().to_string_lossy().ends_with(".json") {
                if let Some(worker) = read_tracked_worker(&file.path()) {
                    workers.push(worker);
                }
            }
        }
    }
    workers
}

/// Parse one descriptor file; invalid or concurrently removed descriptors
/// are not safe shutdown targets and are skipped (TS `isTrackedWorkerDescriptor`).
fn read_tracked_worker(path: &Path) -> Option<TrackedWorker> {
    let content = std::fs::read_to_string(path).ok()?;
    let descriptor: serde_json::Value = serde_json::from_str(&content).ok()?;
    let pid = descriptor.get("pid")?.as_u64()?;
    if pid == 0 {
        return None;
    }
    let worker_id = descriptor.get("workerId")?.as_str()?;
    if worker_id.is_empty() {
        return None;
    }
    Some(TrackedWorker {
        descriptor_path: path.to_path_buf(),
        supervisor_socket_path: PathBuf::from(descriptor.get("supervisorSocketPath")?.as_str()?),
        worker_socket_path: PathBuf::from(descriptor.get("socketPath")?.as_str()?),
        pid: pid as u32,
        process_start_id: descriptor
            .get("processStartId")
            .and_then(serde_json::Value::as_str)
            .map(str::to_string),
        recovery_journal_path: PathBuf::from(descriptor.get("recoveryJournalPath")?.as_str()?),
    })
}

/// What a probe learned about one daemon (TS `ProbeResult`).
#[derive(Debug, Default)]
pub(crate) struct ProbeResult {
    version: Option<String>,
    protocol_version: Option<u64>,
    /// The hello's `protocol.name`: another product's (a pre-rename build's)
    /// daemon is never current, whatever its version numbers say.
    protocol_name: Option<String>,
    schema_id: Option<String>,
    build_id: Option<String>,
    executable_path: Option<String>,
    session_count: Option<u64>,
    supervisor_pid: Option<u32>,
    supervisor_process_start_id: Option<String>,
    reachable: bool,
}

/// Probe one socket: connect, read the hello (1500ms), and ask for the
/// session count over `list` (30s). A socket that accepts but does not greet
/// is reachable with nothing known; only a failed connect is unreachable
/// (TS `probeDaemon`). Foreign protocols are probed like our own.
pub(crate) fn probe_daemon(socket_path: &Path) -> ProbeResult {
    if is_never_touch(socket_path) {
        // Containment: never even connect to a forbidden path, whatever the
        // caller's root says.
        return ProbeResult::default();
    }
    let Ok(runtime) = tokio::runtime::Builder::new_current_thread()
        .enable_all()
        .build()
    else {
        return ProbeResult::default();
    };
    runtime.block_on(async {
        let (client, mut events) =
            match DaemonClient::connect_probe(socket_path, HELLO_TIMEOUT_MS).await {
                Ok(connection) => connection,
                Err(error) => {
                    return ProbeResult {
                        reachable: !is_connect_failure(&error),
                        ..ProbeResult::default()
                    }
                }
            };
        let hello = client.hello();
        let text = |value: Option<&Value>| value.and_then(Value::as_str).map(str::to_string);
        let protocol = hello.get("protocol");
        let runtime_info = hello.get("runtime");
        let mut probe = ProbeResult {
            version: text(hello.get("appVersion")),
            protocol_version: protocol
                .and_then(|protocol| protocol.get("version"))
                .and_then(Value::as_u64),
            protocol_name: text(protocol.and_then(|protocol| protocol.get("name"))),
            schema_id: text(hello.get("schemaId")),
            build_id: text(runtime_info.and_then(|runtime| runtime.get("buildId"))),
            executable_path: ["launcherPath", "entrypointPath", "executablePath"]
                .iter()
                .find_map(|key| text(runtime_info.and_then(|runtime| runtime.get(*key)))),
            session_count: None,
            supervisor_pid: hello
                .get("supervisorPid")
                .and_then(Value::as_u64)
                .and_then(|pid| u32::try_from(pid).ok()),
            supervisor_process_start_id: text(hello.get("supervisorProcessStartId")),
            reachable: true,
        };
        let list = DaemonCommand::List {
            id: None,
            all: None,
            cwd: None,
            session_dir: None,
            include_client_owned: None,
            rest: serde_json::Map::default(),
        };
        if let Ok(response) =
            crate::daemon_command::request(&client, &mut events, list, LIST_TIMEOUT_MS).await
        {
            if response.success {
                probe.session_count = response
                    .data
                    .as_ref()
                    .and_then(|data| data.get("sessions"))
                    .and_then(Value::as_array)
                    .and_then(|sessions| u64::try_from(sessions.len()).ok());
            }
        }
        probe
    })
}

/// Probe deadlines (TS `probeDaemon`).
const HELLO_TIMEOUT_MS: u64 = 1_500;
const LIST_TIMEOUT_MS: u64 = 30_000;

/// Reachable daemons are `current` only when the protocol, schema, and app
/// version all match this build (TS `classifyReachable`), and so does the
/// build identity: a supervisor of another build of the same version (an
/// older commit, or a pre-identity build whose `runtime.buildId` is the
/// bare version) is stale. A hello without `runtime.buildId` has nothing
/// to compare and is judged by the version alone.
fn classify_reachable(probe: &ProbeResult) -> DaemonStatus {
    if probe.protocol_name.as_deref() == Some(eukhe_types::daemon::DAEMON_PROTOCOL_NAME)
        && probe.protocol_version == Some(eukhe_types::daemon::DAEMON_PROTOCOL_VERSION)
        && probe.schema_id.as_deref() == Some(eukhe_types::daemon::DAEMON_SCHEMA_ID)
        && probe.version.as_deref() == Some(config::version())
        && probe
            .build_id
            .as_deref()
            .is_none_or(|build_id| build_id == eukhe_build_info::DAEMON_BUILD_ID)
    {
        DaemonStatus::Current
    } else {
        DaemonStatus::Stale
    }
}

/// The hello's supervisor pid, but only when it is alive and its process
/// identity still matches the one the daemon reported (TS
/// `verifyHelloSupervisorPid`; the start-id gate defeats pid reuse).
pub(crate) fn verify_hello_supervisor_pid(
    pid: Option<u32>,
    expected_process_start_id: Option<&str>,
) -> Option<u32> {
    let pid = pid?;
    if pid == 0 {
        return None;
    }
    match eukhe_types::platform::process::is_process_alive(pid) {
        Ok(true) => {}
        // EPERM-equivalent: the process exists but is not ours to signal.
        Ok(false) | Err(_) => return None,
    }
    if let Some(expected) = expected_process_start_id {
        if eukhe_types::platform::process::process_start_id(pid).as_deref() != Some(expected) {
            return None;
        }
    }
    Some(pid)
}

/// Discover every daemon in this state root and probe each (TS
/// `discoverDaemons`). The root is explicit: the CLI passes the env-resolved
/// current root, tests pass their own fixture dirs. A daemon outside the
/// root is never discovered, probed, or stopped.
pub(crate) fn discover_daemons(root: &DaemonStateRoot) -> Vec<DaemonInfo> {
    let mut process_by_socket = std::collections::HashMap::new();
    for daemon in scan_listening_daemons(root) {
        if is_worker_socket_path(&daemon.socket_path) {
            continue;
        }
        process_by_socket.insert(daemon.socket_path.clone(), daemon);
    }
    let tracked = find_all_tracked_workers(&root.agent_dir);
    let worker_sockets: BTreeSet<PathBuf> = tracked
        .iter()
        .map(|worker| worker.supervisor_socket_path.clone())
        .collect();
    // Only the default scope sweeps the per-user socket dir: a scoped
    // invocation never even lists it.
    let swept = match &root.scope {
        DiscoveryScope::Default { socket_dir } => scan_socket_dir(socket_dir),
        DiscoveryScope::Socket | DiscoveryScope::AgentDir => Vec::new(),
    };
    let mut sockets: BTreeSet<PathBuf> = process_by_socket
        .keys()
        .cloned()
        .chain(
            swept
                .into_iter()
                .filter(|path| !is_worker_socket_path(path)),
        )
        .chain(worker_sockets.iter().cloned())
        // The invocation's own socket is always a candidate: a custom
        // `--daemon-socket`/`EUKHE_DAEMON_SOCKET` path outside the socket
        // dir is otherwise found only by the listener census (never as an
        // orphan file, and not at all where the census tools are missing).
        .chain(is_socket_file(&root.default_socket_path).then(|| root.default_socket_path.clone()))
        .collect();
    sockets.retain(|path| state_root_matches(root, path));

    let mut infos: Vec<DaemonInfo> = sockets
        .into_iter()
        .map(|socket_path| {
            let proc = process_by_socket.get(&socket_path);
            let probe = probe_daemon(&socket_path);
            // The listener census matches by process name; a renamed or
            // older build holding the socket is found by the socket itself.
            let listener_pid =
                proc.map(|daemon| daemon.pid).or_else(|| {
                    match owner::socket_holder(&socket_path) {
                        Some(owner::SocketHolder::Daemon(holder)) => Some(holder.pid),
                        Some(owner::SocketHolder::Other { .. }) | None => None,
                    }
                });
            let pid = listener_pid.or_else(|| {
                verify_hello_supervisor_pid(
                    probe.supervisor_pid,
                    probe.supervisor_process_start_id.as_deref(),
                )
            });
            let has_tracked_workers = worker_sockets.contains(&socket_path);
            let status = if probe.reachable {
                classify_reachable(&probe)
            } else if listener_pid.is_some() || has_tracked_workers {
                DaemonStatus::Unreachable
            } else {
                DaemonStatus::OrphanFile
            };
            DaemonInfo {
                pid_source: pid.map(|_| {
                    if listener_pid.is_some() {
                        PidSource::Listener
                    } else {
                        PidSource::Hello
                    }
                }),
                is_default: socket_path == root.default_socket_path,
                socket_path,
                pid,
                uptime_seconds: proc.and_then(|daemon| daemon.uptime_seconds),
                version: probe.version,
                protocol_version: probe.protocol_version,
                schema_id: probe.schema_id,
                build_id: probe.build_id,
                executable_path: probe.executable_path,
                session_count: probe.session_count,
                status,
                has_tracked_workers: has_tracked_workers.then_some(true),
            }
        })
        .collect();
    sort_daemons(&mut infos);
    infos
}

/// Default first, then by status severity, then by socket path (TS
/// `sortDaemons`).
pub(crate) fn sort_daemons(infos: &mut [DaemonInfo]) {
    infos.sort_by(|left, right| {
        right
            .is_default
            .cmp(&left.is_default)
            .then(left.status.cmp(&right.status))
            .then(left.socket_path.cmp(&right.socket_path))
    });
}

/// The quiet-period decision for the shutdown residual sweep (TS
/// `evaluateShutdownQuietPeriod`): a sweep completes once no listener has
/// been seen for a full quiet period.
pub(crate) fn evaluate_shutdown_quiet_period(now_ms: u128, quiet_since_ms: Option<u128>) -> bool {
    quiet_since_ms
        .is_some_and(|quiet_since| now_ms.saturating_sub(quiet_since) >= SHUTDOWN_QUIET_PERIOD_MS)
}

/// How long the residual sweep must see no listener before it succeeds (TS
/// `SHUTDOWN_QUIET_PERIOD_MS`).
const SHUTDOWN_QUIET_PERIOD_MS: u128 = 1_000;

#[cfg(test)]
mod tests {
    use super::*;

    /// A synthetic default-scope state root inside a fixture directory:
    /// unit tests never touch the ambient environment's real agent dir or
    /// socket dir. Its socket dir is [`fixture_socket_dir`].
    fn fixture_root(dir: &Path) -> DaemonStateRoot {
        DaemonStateRoot {
            agent_dir: dir.join("agent"),
            default_socket_path: fixture_socket_dir(dir).join("daemon.sock"),
            scope: DiscoveryScope::Default {
                socket_dir: fixture_socket_dir(dir),
            },
        }
    }

    /// The fixture's default socket dir, beside (not inside) its agent dir
    /// like the product's `<tmp>/eukhe-<uid>` beside `~/.eukhe`.
    fn fixture_socket_dir(dir: &Path) -> PathBuf {
        dir.join("sockets")
    }

    /// Accept-and-drop listener on `path`: a probe finds it reachable
    /// without the hello wait (so it reads stale), and its socket file is a
    /// live listener for the whole test.
    fn listen(path: &Path) {
        let listener = std::os::unix::net::UnixListener::bind(path).expect("bind");
        std::thread::spawn(move || {
            for stream in listener.incoming() {
                drop(stream);
            }
        });
    }

    #[test]
    fn worker_sockets_are_named_worker_sock_wherever_they_sit() {
        let dir = Path::new("/fixture/agent/sockets");
        assert!(is_worker_socket_path(&dir.join("worker-abc-123.sock")));
        assert!(is_worker_socket_path(Path::new(
            "/fixture/custom/worker-abc-123.sock"
        )));
        assert!(!is_worker_socket_path(&dir.join("daemon.sock")));
        assert!(!is_worker_socket_path(
            &dir.join("worker-abc-123.sock.lock")
        ));
    }

    #[test]
    fn state_root_matches_scoped_paths_only() {
        let fixture = Path::new("/fixture");
        let default = fixture_root(fixture);
        let custom = PathBuf::from("/fixture/custom/daemon.sock");
        let candidates = [
            default.default_socket_path.clone(),
            fixture_socket_dir(fixture).join("other.sock"),
            default.agent_dir.join("nested/daemon.sock"),
            custom.clone(),
            PathBuf::from("/tmp/other-root/daemon.sock"),
        ];
        let socket_scoped = DaemonStateRoot {
            default_socket_path: custom,
            scope: DiscoveryScope::Socket,
            ..default.clone()
        };
        let agent_dir_scoped = DaemonStateRoot {
            scope: DiscoveryScope::AgentDir,
            ..default.clone()
        };
        let matches = |root: &DaemonStateRoot| -> Vec<bool> {
            candidates
                .iter()
                .map(|path| state_root_matches(root, path))
                .collect()
        };
        assert_eq!(
            [
                matches(&default),
                matches(&socket_scoped),
                matches(&agent_dir_scoped)
            ],
            [
                vec![true, true, true, false, false],
                vec![false, false, false, true, false],
                vec![false, false, true, false, false],
            ]
        );
    }

    #[test]
    fn never_touch_paths_are_excluded_even_when_the_root_points_at_them() {
        for dir in NEVER_TOUCH_SOCKET_DIRS {
            let dir = Path::new(dir);
            let root = DaemonStateRoot {
                agent_dir: dir.to_path_buf(),
                default_socket_path: dir.join("daemon.sock"),
                scope: DiscoveryScope::Default {
                    socket_dir: dir.to_path_buf(),
                },
            };
            assert!(
                !state_root_matches(&root, &root.default_socket_path),
                "containment must beat root matching for {dir:?}"
            );
            assert!(!state_root_matches(&root, &dir.join("worker-x.sock")));
        }
        assert!(is_never_touch(Path::new("/tmp/mission-daemon")));
        assert!(is_never_touch(Path::new("/tmp/mission-daemon/daemon.sock")));
        assert!(is_never_touch(Path::new("/tmp/eukhe-1000")));
        assert!(!is_never_touch(Path::new("/tmp")));
        assert!(!is_never_touch(Path::new("/tmp/other/daemon.sock")));
    }

    #[test]
    fn a_scan_rooted_on_a_never_touch_dir_surfaces_no_listeners() {
        // The ambient mission daemon's workers listen under these dirs and
        // are owned by real `eukhe` processes: root matching alone
        // would find them, the containment guard must not. The loop covers
        // every guarded dir -- the uid-1000 mission paths on a devbox and
        // their uid-0 twins on a root-user Linux box.
        for dir in NEVER_TOUCH_SOCKET_DIRS {
            let dir = *dir;
            let root = DaemonStateRoot {
                agent_dir: PathBuf::from(dir),
                default_socket_path: PathBuf::from(dir).join("daemon.sock"),
                scope: DiscoveryScope::Default {
                    socket_dir: PathBuf::from(dir),
                },
            };
            assert!(
                scan_listening_daemons(&root).is_empty(),
                "scan rooted at {dir} must not surface listeners"
            );
        }
    }

    #[test]
    fn a_probe_never_connects_to_a_never_touch_path() {
        // When the guard works, this never opens a connection. A regression
        // (guard removed) would probe the live mission daemon once and fail
        // the assertion -- never kill it.
        let probe = probe_daemon(Path::new("/tmp/mission-daemon/daemon.sock"));
        assert!(!probe.reachable);
    }

    #[test]
    fn discovery_reports_orphan_files_inside_the_given_root_only() {
        let tmp = tempfile::tempdir().expect("tempdir");
        let root = fixture_root(tmp.path());
        let socket_dir = fixture_socket_dir(tmp.path());
        std::fs::create_dir_all(&socket_dir).expect("socket dir");
        // Bind and drop: the listener's socket file stays behind (std does
        // not unlink it), an orphan file in the fixture root.
        drop(
            std::os::unix::net::UnixListener::bind(socket_dir.join("leftover.sock")).expect("bind"),
        );
        let infos = discover_daemons(&root);
        assert_eq!(infos.len(), 1);
        assert_eq!(infos[0].socket_path, socket_dir.join("leftover.sock"));
        assert_eq!(infos[0].status, DaemonStatus::OrphanFile);
        // Not the root's default path: leftover.sock, not daemon.sock.
        assert!(!infos[0].is_default);
    }

    /// The invocation's scope follows what it names: a socket (flag, then
    /// env) scopes it to that socket whatever else is set, an agent dir to
    /// that agent dir, and only an invocation naming neither gets the
    /// default scope with the per-user socket dir.
    #[test]
    fn the_invocation_scope_follows_the_named_socket_then_agent_dir() {
        let tmp = tempfile::tempdir().expect("tempdir");
        let socket = tmp.path().join("env-daemon.sock");
        let agent_dir = tmp.path().join("agent");
        let scopes = {
            let _env = config::env_lock();
            let saved: Vec<(&str, Option<std::ffi::OsString>)> =
                [config::ENV_DAEMON_SOCKET, config::ENV_AGENT_DIR]
                    .into_iter()
                    .map(|key| (key, std::env::var_os(key)))
                    .collect();
            std::env::remove_var(config::ENV_DAEMON_SOCKET);
            std::env::remove_var(config::ENV_AGENT_DIR);
            let unscoped = current_state_root(None).scope;
            let flag = current_state_root(socket.to_str()).scope;
            std::env::set_var(config::ENV_AGENT_DIR, &agent_dir);
            let agent_dir_env = current_state_root(None).scope;
            std::env::set_var(config::ENV_DAEMON_SOCKET, &socket);
            let both_env = current_state_root(None).scope;
            for (key, value) in saved {
                match value {
                    Some(value) => std::env::set_var(key, value),
                    None => std::env::remove_var(key),
                }
            }
            [unscoped, flag, agent_dir_env, both_env]
        };
        assert_eq!(
            scopes,
            [
                DiscoveryScope::Default {
                    socket_dir: eukhe_daemon::platform::socket_dir(),
                },
                DiscoveryScope::Socket,
                DiscoveryScope::AgentDir,
                DiscoveryScope::Socket,
            ]
        );
    }

    /// The regression: an invocation scoped to its own socket or agent dir
    /// also swept the per-user default socket dir, so an isolated
    /// `shutdown --force` stopped the user's default daemon. Live
    /// listeners on the default socket and on a custom socket: the socket
    /// scope finds its own only, the agent-dir scope neither (a daemon
    /// inside the agent dir is found by the listener census, which these
    /// non-product listeners are not part of), and the default scope never
    /// the custom socket it was not given.
    #[test]
    fn each_scope_discovers_its_own_daemons_only() {
        let tmp = tempfile::tempdir().expect("tempdir");
        let default = fixture_root(tmp.path());
        std::fs::create_dir_all(fixture_socket_dir(tmp.path())).expect("socket dir");
        let custom = tmp.path().join("custom-daemon.sock");
        for socket in [&default.default_socket_path, &custom] {
            listen(socket);
        }
        let socket_scoped = DaemonStateRoot {
            default_socket_path: custom.clone(),
            scope: DiscoveryScope::Socket,
            ..default.clone()
        };
        let agent_dir_scoped = DaemonStateRoot {
            scope: DiscoveryScope::AgentDir,
            ..default.clone()
        };
        let found = |root: &DaemonStateRoot| -> Vec<PathBuf> {
            discover_daemons(root)
                .into_iter()
                .map(|info| info.socket_path)
                .collect()
        };
        assert_eq!(
            [
                found(&socket_scoped),
                found(&agent_dir_scoped),
                found(&default)
            ],
            [
                vec![custom],
                Vec::new(),
                vec![default.default_socket_path.clone()],
            ]
        );
    }

    /// The regression: a daemon started on `EUKHE_DAEMON_SOCKET` (or
    /// `--daemon-socket`) outside the socket dir and the agent dir was out
    /// of the invocation's root, so `shutdown --force` reported "No
    /// background services found." while it ran. The invocation's socket
    /// (flag, then env) is its root's own socket, and discovery finds a
    /// daemon there wherever it sits.
    #[test]
    fn the_invocations_daemon_socket_is_discovered_outside_the_socket_dir() {
        let tmp = tempfile::tempdir().expect("tempdir");
        let env_socket = tmp.path().join("env-daemon.sock");
        let flag_socket = tmp.path().join("flag-daemon.sock");
        let (from_env, from_flag) = {
            let _env = config::env_lock();
            let saved = std::env::var_os(config::ENV_DAEMON_SOCKET);
            std::env::set_var(config::ENV_DAEMON_SOCKET, &env_socket);
            let roots = (
                current_state_root(None),
                current_state_root(flag_socket.to_str()),
            );
            match saved {
                Some(value) => std::env::set_var(config::ENV_DAEMON_SOCKET, value),
                None => std::env::remove_var(config::ENV_DAEMON_SOCKET),
            }
            roots
        };
        assert_eq!(from_env.default_socket_path, env_socket);
        assert_eq!(from_flag.default_socket_path, flag_socket);

        // Accepted connections drop at once: the probe is reachable
        // without the hello wait.
        listen(&env_socket);
        let root = DaemonStateRoot {
            agent_dir: tmp.path().join("agent"),
            default_socket_path: env_socket.clone(),
            scope: DiscoveryScope::Socket,
        };
        let found: Vec<(PathBuf, bool, DaemonStatus)> = discover_daemons(&root)
            .into_iter()
            .map(|info| (info.socket_path, info.is_default, info.status))
            .collect();
        assert_eq!(found, vec![(env_socket, true, DaemonStatus::Stale)]);
    }

    /// The regression: a daemon left running by an older build of the same
    /// version (its `runtime.buildId` the bare version, or another commit)
    /// read as current, so the client kept using the old engine. Only this
    /// build's identity, or a hello without one, is current.
    #[test]
    fn a_same_version_daemon_of_another_build_is_stale() {
        let probe = |build_id: Option<String>| ProbeResult {
            version: Some(config::version().to_string()),
            protocol_version: Some(eukhe_types::daemon::DAEMON_PROTOCOL_VERSION),
            protocol_name: Some(eukhe_types::daemon::DAEMON_PROTOCOL_NAME.to_string()),
            schema_id: Some(eukhe_types::daemon::DAEMON_SCHEMA_ID.to_string()),
            build_id,
            reachable: true,
            ..ProbeResult::default()
        };
        let statuses: Vec<DaemonStatus> = [
            Some(eukhe_build_info::DAEMON_BUILD_ID.to_string()),
            Some(format!("eukhe-daemon-rs-{}+d1ca7bf22000", config::VERSION)),
            Some(format!("{}.dirty", eukhe_build_info::DAEMON_BUILD_ID)),
            None,
        ]
        .into_iter()
        .map(|build_id| classify_reachable(&probe(build_id)))
        .collect();
        assert_eq!(
            statuses,
            vec![
                DaemonStatus::Current,
                DaemonStatus::Stale,
                DaemonStatus::Stale,
                DaemonStatus::Current,
            ]
        );
    }

    #[test]
    fn quiet_period_completes_after_the_threshold() {
        assert!(evaluate_shutdown_quiet_period(1_500, Some(500)));
        assert!(!evaluate_shutdown_quiet_period(1_200, Some(500)));
        assert!(!evaluate_shutdown_quiet_period(2_000, None));
    }
}
