//! The shapes of the daemon log lines the classifier reads. They run in
//! the compiled Bend core (`bend/incident_shapes.bend`, entry
//! `bend/ffi_shape.bend`; `laws/incident_shapes.bend`), not as Rust
//! regexes. This crate depends on nothing, so a crate that may call the
//! core (eukhe-cli, eukhe-tui) passes them in as an [`IncidentRules`], as
//! eukhe-theme takes its `ThemeRules`.

/// One shape of a daemon log line. Its discriminant is its global shape id
/// (the index of the shape in `bend/incident_shapes.bend` `table`); above
/// each, the regex it replaces.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
#[repr(u32)]
pub enum IncidentShape {
    /// `^(?:eukhe-)?worker-[0-9a-f]+-([0-9a-f]{12})(?:\.sock)?$`
    WorkerSocket = 0,
    /// `^Session worker ([0-9a-f]{12}) stderr: ?([\s\S]*)$`
    StderrForward = 1,
    /// `^Eukhe daemon supervisor \S+ listening on \S+$`
    SupervisorListening = 2,
    /// `^Eukhe daemon listening on \S+$`
    WorkerListening = 3,
    /// `^(?:uncaught exception|unhandled rejection): (.+)$`
    CrashLine = 4,
    /// `^(?:uncaught exception|unhandled rejection): `
    CrashPrefix = 5,
    /// `^shutting down \(exit (\d+)\); closing (\d+) active session\(s\)$`
    ShutdownExit = 6,
    /// `^received (\S+); shutting down$`
    SignalShutdown = 7,
    /// `^shutdown command received over socket; (\d+) active session\(s\) will be closed$`
    StopRequested = 8,
    /// `^Passivated idle child sessionId=(\S+) name=("[^"]*"|\S+) idleMinutes=(\d+)$`
    Passivated = 9,
    /// `^Daemon supervisor startup failed: (.+)$`
    StartupFailed = 10,
    /// `^Supervisor command (\S+) failed: (.+)$`
    SupervisorCommand = 11,
    /// `^daemon command "([^"]+)" failed: (.+)$`
    DaemonCommand = 12,
    /// `^(?:Failed|could not)(?: to)? catch up (?:snapshot )?client \S+(?: for (\S+))?: (.+)$`
    CatchUp = 13,
    /// `^Could not list heartbeats from a worker: (.+)$`
    HeartbeatsList = 14,
    /// `^Recovered worker (\S+) without replaying uncertain operations: (.+)$`
    Recovered = 15,
    /// `^Recovered worker (\S+)$`
    RecoveredPlain = 16,
    /// `^Could not adopt worker (\S+): (.+)$`
    AdoptFailed = 17,
    /// `^Could not recover worker (\S+): (.+)$`
    RecoverFailed = 18,
    /// `^Worker (\S+) failed after three recovery attempts$`
    FailedAfterRetries = 19,
    /// `^Worker (\S+) is unresponsive; parked failed after \d+ probe rounds$`
    Unresponsive = 20,
    /// `^Reclaimed stale registration for stopped worker (\S+)$`
    Reclaimed = 21,
    /// `^Migrated (\d+) scheduled jobs into session artifacts$`
    Migrated = 22,
    /// `^launched replacement supervisor on \S+$`
    Replacement = 23,
    /// `^Woke session worker for a due scheduled job: \S+$`
    Woke = 24,
    /// `^Evicted idle worker (\S+) root=\S* idleMinutes=(\d+) sessions=(\d+)$`
    EvictedIdle = 25,
    /// `^Evicted empty session worker (\S+) root=\S+ on last client detach$`
    EvictedEmpty = 26,
    /// `(?i)authentication failed`
    AuthFailed = 27,
    /// `Unknown active session: (\S+)`
    UnknownSession = 28,
    /// `^\s*at\s` (a stack frame continuation line)
    StackFrame = 29,
    /// `^\[([^\]]+)\]\s*(.*)$` (a per-daemon log line)
    DaemonLine = 30,
}

impl IncidentShape {
    /// The global shape id the compiled core names this shape by.
    #[must_use]
    pub const fn id(self) -> u32 {
        self as u32
    }
}

/// The first shape of a list that fits a text: its index in the list, and
/// the text each of its captures took, in the order its captures open
/// (`None`: the capture took no part in the fit, as an untaken regex group).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ShapeFit {
    pub index: usize,
    pub captures: Vec<Option<String>>,
}

impl ShapeFit {
    /// The text capture `k` took, numbered from 1 as regex groups.
    #[must_use]
    pub fn get(&self, k: usize) -> Option<&str> {
        self.captures.get(k.checked_sub(1)?)?.as_deref()
    }
}

/// The incident rules: the compiled core's, passed in by a crate that may
/// call it.
#[derive(Clone, Copy, Debug)]
pub struct IncidentRules {
    /// The first of the shapes that fits the text (each searched as its
    /// shape says: only from the text start, or at the leftmost place it
    /// fits), its index in the list and its captures; `None` when none
    /// fits. An implementation answers exactly what the shapes' laws
    /// state (`laws/incident_shapes.bend`, `laws/shape/`).
    pub first: fn(&str, &[IncidentShape]) -> Option<ShapeFit>,
}
