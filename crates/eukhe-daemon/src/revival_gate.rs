//! The boot-revival ownership gate: whether a dead worker's descriptor
//! may be relaunched at a supervisor boot. #2584's busy-evidence filter
//! answered "did the journal prove live work?"; this gate answers "is that
//! proof still a genuine interruption THIS boot must heal?" — a stopped
//! or already-condemned session must never come back as an active worker
//! through the daemon's own automatic paths (the zombie-resurrection
//! fix): a client reopen is the only legitimate way back.
//!
//! Four vetoes, in check order:
//!
//! 1. The give-up verdict. A descriptor the supervisor marked `failed`
//!    (the 6-consecutive-failure cap) carries durable intent: this
//!    supervisor already tried and gave up on reviving it. A later boot
//!    re-runs that verdict, never the relaunch — otherwise every boot
//!    re-storms the same dead slots (the 12:00→17:07 recurrence on the
//!    rust-agent box).
//! 2. The stop lifecycle's archived belt (#2592). A session whose durable
//!    state is `archived` was stopped on purpose; the belt is the stop's
//!    durable half. No automatic path may flip it back to `active` —
//!    revival would erase the stop and re-register a dead session as a
//!    live worker.
//! 3. A live session lease. The runtime lease is the one ownership record
//!    every daemon sharing the agent dir can read; a live holder (this
//!    daemon's own surviving process, or another daemon's worker — the
//!    two-daemons-one-store fleet) owns the session file. Spawning a
//!    rival worker over it would either fail on the lease (the 6-strike
//!    storm) or, without leases enabled, double-serve the file.
//! 4. Stale busy evidence. A `busy` recovery record is interrupted-work
//!    proof only while it is recent. A busy worker re-records it every
//!    [`crate::timeouts::BUSY_REFRESH_MS`], so its age counts from the
//!    last refresh, never from the start of a long run; a record older
//!    than the max age
//!    ([`crate::timeouts::Derived::revival_busy_evidence_max_age_ms`]) is
//!    residue of an era that already ended, and a timestamp dated beyond
//!    [`REVIVAL_CLOCK_SKEW_MS`] into the future is not freshness proof
//!    either (clock rollback must not zero the age) — uncertainty
//!    never revives. The law `revive_after_refresh` (`laws/revive.bend`, D1)
//!    proves that a boot within [`crate::timeouts::REVIVAL_BOOT_WINDOW_MS`]
//!    of a busy worker's crash revives it, however long its run took.
//!
//! The vetoes and their order are the compiled Bend model's
//! (`bend/ffi_revive.bend` over bend/revive.bend `veto`; laws
//! `revive_ffi_*`, `revive_veto_ages_as_model`): [`revival_veto`] gathers
//! the facts (the descriptor's lifecycle, the session file's belt, the
//! lease, the stamp, the clock) and acts on the answer.

use std::path::Path;

use eukhe_bend::wire::{Reader, WireError, Writer, NAT_MAX};
use eukhe_bend::Entry;
use eukhe_types::daemon::{DaemonWorkerDescriptor, DaemonWorkerLifecycle};

/// Freshness tolerates only this much wall-clock skew between the
/// journal's writer and the boot reading it (two daemons on one shared
/// agent dir can disagree slightly). A timestamp further in the
/// future is not freshness proof: a clock rollback or a far-future
/// stamp must not zero the age — uncertainty never revives.
pub(crate) const REVIVAL_CLOCK_SKEW_MS: u64 = 60 * 1000;

/// One veto against relaunching a dead descriptor, with the park's log
/// reason (the reason lives in the daemon log).
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum RevivalVeto {
    /// The supervisor already gave up on this worker (`lifecycle: failed`):
    /// the give-up verdict is durable — a later boot re-runs it, never the
    /// relaunch.
    GaveUp,
    /// The session's durable state is `archived`: the stop lifecycle's belt
    /// (#2592) is durable stop intent — no automatic path may flip it back
    /// active.
    SessionArchived,
    /// A live lease holds the session file: another worker process (this
    /// daemon's or another daemon's, on a shared agent dir) owns the
    /// session — one owning daemon, one owning worker.
    LiveLeaseHeld { pid: u32 },
    /// The newest `busy` record predates the freshness bound: the evidence
    /// of interrupted work is residue of an era that already ended, not a
    /// crash this boot must heal.
    StaleBusyEvidence { recorded_at: String },
    /// No `busy` record with a time stamp: nothing proves the interrupted
    /// work is fresh (the journal changed since the boot read it busy).
    NoBusyEvidence,
}

impl RevivalVeto {
    pub(crate) fn log_reason(&self) -> String {
        match self {
            RevivalVeto::GaveUp => {
                "was failed at the last give-up; not revived (reopens on the next client open)"
                    .to_string()
            }
            RevivalVeto::SessionArchived => {
                "its session is archived (stopped); not revived (reopens on the next client open)"
                    .to_string()
            }
            RevivalVeto::LiveLeaseHeld { pid } => format!(
                "a live worker (pid {pid}) holds its session lease; not revived (one owning daemon)"
            ),
            RevivalVeto::StaleBusyEvidence { recorded_at } => format!(
                "its busy evidence is stale (recorded {recorded_at}); not revived (reopens on the next client open)"
            ),
            RevivalVeto::NoBusyEvidence => {
                "no busy record proves fresh work; not revived (reopens on the next client open)"
                    .to_string()
            }
        }
    }
}

/// Whether a boot at `now_ms` may relaunch one dead descriptor.
/// `busy_recorded_at` is the newest `busy` record's timestamp when the
/// journal proves live work.
pub(crate) fn revival_veto(
    agent_dir: &Path,
    descriptor: &DaemonWorkerDescriptor,
    busy_recorded_at: Option<&str>,
    now_ms: u64,
) -> Option<RevivalVeto> {
    let session_file = descriptor.session_file.as_deref().map(Path::new);
    let facts = Facts {
        failed: matches!(descriptor.lifecycle, DaemonWorkerLifecycle::Failed),
        archived: session_file.is_some_and(session_is_archived),
        lease: session_file
            .and_then(|file| crate::lease::live_lease_owner(agent_dir, file))
            .map(|owner| owner.pid),
        // A stamp that does not parse, or one past the wire (beyond the
        // year 5138, so far past the clock and its skew), proves nothing.
        busy: match busy_recorded_at {
            None => Busy::NoRecord,
            Some(at) => crate::util::iso_to_unix_ms(at)
                .filter(|ms| *ms <= NAT_MAX)
                .map_or(Busy::Unread, Busy::Stamp),
        },
        // The wall clock stays below the wire's bound until the year 5138.
        now_ms: now_ms.min(NAT_MAX),
    };
    eukhe_bend::expect_core(Entry::Revive, veto_call(&facts, busy_recorded_at))
}

/// What a boot found about one dead descriptor.
struct Facts {
    failed: bool,
    archived: bool,
    /// The pid of a live worker holding the session lease.
    lease: Option<u32>,
    busy: Busy,
    now_ms: u64,
}

/// The newest busy record.
enum Busy {
    /// No record with a stamp.
    NoRecord,
    /// A stamp that cannot be read.
    Unread,
    /// Recorded at this time (ms).
    Stamp(u64),
}

fn veto_call(
    facts: &Facts,
    busy_recorded_at: Option<&str>,
) -> Result<Option<RevivalVeto>, eukhe_bend::Error> {
    let mut request = Writer::new();
    request.bool(facts.failed).bool(facts.archived);
    match facts.lease {
        None => request.none(),
        Some(pid) => request.some().nat(u64::from(pid)),
    };
    match facts.busy {
        Busy::NoRecord => request.tag(0),
        Busy::Unread => request.tag(1),
        Busy::Stamp(at) => request.tag(2).nat(at),
    };
    request
        .nat(facts.now_ms)
        .nat(crate::timeouts::derived().revival_busy_evidence_max_age_ms)
        .nat(REVIVAL_CLOCK_SKEW_MS);
    let reply = eukhe_bend::call(Entry::Revive, &request.finish()?)?;
    let mut reader = Reader::reply(&reply)?;
    let veto = match reader.tag_of(6, "a revival veto")? {
        0 => None,
        1 => Some(RevivalVeto::GaveUp),
        2 => Some(RevivalVeto::SessionArchived),
        3 => Some(RevivalVeto::LiveLeaseHeld { pid: reader.u32()? }),
        4 => Some(RevivalVeto::NoBusyEvidence),
        // `tag_of` answers a tag below 6: this is 5.
        _ => {
            let recorded_at = busy_recorded_at.ok_or(WireError::Malformed {
                at: 0,
                expected: "a stale veto only on a stamped busy record",
            })?;
            Some(RevivalVeto::StaleBusyEvidence {
                recorded_at: recorded_at.to_string(),
            })
        }
    };
    reader.end()?;
    Ok(veto)
}

/// The session file's durable state is the archived belt (#2592's stop
/// lifecycle): a state that cannot be read does not prove a stop, so it
/// does not veto (a missing or unreadable file leaves the belt unknown —
/// the create replay's own load decides there).
fn session_is_archived(session_file: &Path) -> bool {
    crate::session_store::read_session_info(session_file)
        .and_then(|info| info.state)
        .is_some_and(|state| state == "archived")
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::util::{iso_from_unix_ms, now_ms};
    use serde_json::Map;

    fn descriptor(session_file: Option<&Path>) -> DaemonWorkerDescriptor {
        DaemonWorkerDescriptor {
            version: 2,
            worker_id: "w1".to_string(),
            pid: 4_194_303,
            process_start_id: None,
            socket_path: "/nonexistent/w1.sock".to_string(),
            recovery_journal_path: String::new(),
            orphan_process_journal_path: None,
            supervisor_socket_path: "/tmp/s.sock".to_string(),
            authentication_token: "token".to_string(),
            worker_instance_id: None,
            root_active_session_id: "w1".to_string(),
            owner_client_id: None,
            root_session_id: None,
            session_file: session_file.map(|p| p.to_string_lossy().to_string()),
            session_dir: None,
            created_at: String::new(),
            updated_at: String::new(),
            lifecycle: DaemonWorkerLifecycle::Ready,
            create_command: eukhe_types::daemon::DurableDaemonCreateCommand {
                session_path: None,
                no_session: None,
                rest: Map::default(),
            },
            consecutive_failures: 0,
            stop_requested_at: None,
            archive_on_stop: None,
            last_failure_at: None,
            last_error: None,
            rest: Map::default(),
        }
    }

    fn session_file(state: Option<&str>) -> std::path::PathBuf {
        let dir = std::env::temp_dir().join(format!("pa-revival-gate-{}", uuid::Uuid::new_v4()));
        std::fs::create_dir_all(&dir).unwrap();
        let mut session = crate::session_store::SessionFile::create("/work", None, 0);
        session.append_message(&serde_json::json!({
            "role": "user", "content": "hi", "timestamp": 1u64
        }));
        if let Some(state) = state {
            let _ = session.append_session_state(state);
        }
        let path = dir.join(format!("{}.jsonl", session.session_id()));
        session.set_path(path.clone());
        session.rewrite().unwrap();
        path
    }

    fn agent_dir() -> std::path::PathBuf {
        let dir = std::env::temp_dir().join(format!("pa-revival-agent-{}", uuid::Uuid::new_v4()));
        std::fs::create_dir_all(&dir).unwrap();
        dir
    }

    #[test]
    fn fresh_busy_evidence_passes_the_gate() {
        let file = session_file(Some("active"));
        let recorded_at = iso_from_unix_ms(now_ms() - 1_000);
        let agent_dir = agent_dir();
        assert!(revival_veto(
            &agent_dir,
            &descriptor(Some(&file)),
            Some(&recorded_at),
            now_ms()
        )
        .is_none());
    }

    #[test]
    fn an_unparsable_evidence_timestamp_vetoes_the_revival() {
        let file = session_file(Some("active"));
        let agent_dir = agent_dir();
        let veto = revival_veto(
            &agent_dir,
            &descriptor(Some(&file)),
            Some("when?"),
            now_ms(),
        )
        .expect("uncertainty must not revive");
        assert!(matches!(veto, RevivalVeto::StaleBusyEvidence { .. }));
    }

    #[test]
    fn the_give_up_verdict_vetoes_even_fresh_busy_evidence() {
        let file = session_file(Some("active"));
        let recorded_at = iso_from_unix_ms(now_ms());
        let agent_dir = agent_dir();
        let mut descriptor = descriptor(Some(&file));
        descriptor.lifecycle = DaemonWorkerLifecycle::Failed;
        let veto = revival_veto(&agent_dir, &descriptor, Some(&recorded_at), now_ms())
            .expect("failed lifecycle must veto");
        assert!(matches!(veto, RevivalVeto::GaveUp));
    }

    #[test]
    fn the_archived_belt_vetoes_even_fresh_busy_evidence() {
        // The captured zombie shape: a stopped session (archived at
        // 15:57) whose journal still holds a busy record.
        let file = session_file(Some("archived"));
        let recorded_at = iso_from_unix_ms(now_ms());
        let agent_dir = agent_dir();
        let veto = revival_veto(
            &agent_dir,
            &descriptor(Some(&file)),
            Some(&recorded_at),
            now_ms(),
        )
        .expect("an archived session must not revive");
        assert!(matches!(veto, RevivalVeto::SessionArchived));
    }

    #[test]
    fn a_live_foreign_lease_vetoes_the_revival() {
        let file = session_file(Some("active"));
        let recorded_at = iso_from_unix_ms(now_ms());
        let agent_dir = agent_dir();
        // A live lease written the way another daemon's worker writes it
        // (this test process holds it): the file is owned elsewhere.
        std::env::set_var(crate::lease::SESSION_LEASES_ENABLED_ENV, "1");
        let lease = crate::lease::acquire_runtime_session_lease(&file, &agent_dir);
        std::env::remove_var(crate::lease::SESSION_LEASES_ENABLED_ENV);
        let _lease = lease.expect("the test process acquires the lease");
        let veto = revival_veto(
            &agent_dir,
            &descriptor(Some(&file)),
            Some(&recorded_at),
            now_ms(),
        )
        .expect("a live lease must veto");
        assert!(matches!(veto, RevivalVeto::LiveLeaseHeld { .. }));
    }

    #[test]
    fn a_released_lease_does_not_veto() {
        let file = session_file(Some("active"));
        let recorded_at = iso_from_unix_ms(now_ms());
        let agent_dir = agent_dir();
        // A lease whose owner is long dead is stale ownership, not a live
        // one: the gate must not park genuinely interrupted work behind a
        // dead holder's record.
        std::env::set_var(crate::lease::SESSION_LEASES_ENABLED_ENV, "1");
        let lease = crate::lease::acquire_runtime_session_lease(&file, &agent_dir);
        std::env::remove_var(crate::lease::SESSION_LEASES_ENABLED_ENV);
        drop(lease.expect("the test process acquires the lease"));
        assert!(revival_veto(
            &agent_dir,
            &descriptor(Some(&file)),
            Some(&recorded_at),
            now_ms()
        )
        .is_none());
    }

    /// A long run's busy evidence stays fresh: the refresh re-records it,
    /// so a boot after the max age (counted from the run's start) still
    /// revives the session. Without the refresh, the same record is stale.
    #[test]
    fn refreshed_busy_evidence_outlives_the_max_age() {
        let file = session_file(Some("active"));
        let agent_dir = agent_dir();
        let journal = agent_dir.join("w1.recovery.jsonl");
        let now = now_ms();
        let max_age = crate::timeouts::derived().revival_busy_evidence_max_age_ms;
        let started = iso_from_unix_ms(now - max_age - 60_000);
        let record = crate::journal::WorkerRecoveryRecord {
            active_session_id: "w1".to_string(),
            session_id: "s1".to_string(),
            session_file: Some(file.to_string_lossy().to_string()),
            busy: true,
            operation: "run_started".to_string(),
            recorded_at: started.clone(),
            failure: None,
        };
        crate::journal::append_record(&journal, &serde_json::to_value(&record).unwrap()).unwrap();
        let gate = |recorded_at: Option<String>| {
            revival_veto(
                &agent_dir,
                &descriptor(Some(&file)),
                recorded_at.as_deref(),
                now,
            )
        };
        let unrefreshed =
            gate(crate::journal::WorkerRecoveryJournal::latest_busy_recorded_at(&journal));
        assert_eq!(
            unrefreshed,
            Some(RevivalVeto::StaleBusyEvidence {
                recorded_at: started
            })
        );

        crate::journal::WorkerRecoveryJournal::open(&journal)
            .unwrap()
            .refresh_busy()
            .unwrap();

        let refreshed =
            gate(crate::journal::WorkerRecoveryJournal::latest_busy_recorded_at(&journal));
        assert_eq!(refreshed, None);
    }
}
