# Daemon laws: the supervisor and its workers

The shared rules (what a law secures, the adversary) are in [harness.md](harness.md).

### D1. Supervisor

The daemon is a supervisor. It starts one worker process for each active
session. The laws are in `laws/supervisor.bend`; `bend/proof_supervisor.bend`
proves them. The bridge test `crates/eukhe-daemon/src/supervision_bridge.rs`
runs the Rust code and each model on the same scenarios and requires the
same transcript.

| Rule | Rust | Model | Law |
|---|---|---|---|
| A worker that fails more than 5 times in the restart window (15 minutes, monotonic clock) is given up. The pause before a restart doubles with each failure in the window (250 ms to 30 s). | `supervisor/restart_budget.rs` `RestartBudget` | `bend/supervise.bend` | `restart_gives_up` |
| Each timeout is the sum of the timeouts it waits for: the stop grace covers the kernel teardown and the Harness close; the launcher waits for the whole drain of the supervisor; a parent's kill of a child covers the kill route and the drain of the child; a lost worker sees a relaunched supervisor before it exits; busy evidence outlives one refresh; a quiesced gate stays closed after the answer phase; the restart window holds the give-up count of crash-loop steps. | `timeouts.rs`, `eukhe-types` `daemon/timing.rs`, `eukhe-core` `kernel/shared.rs` | `bend/supervise.bend` `Tm` | `timeouts_ordered` |
| A busy worker records its busy evidence again every 5 minutes. A boot within 25 minutes of its crash revives it, however long its run took. | `revival_gate.rs` `busy_evidence_fresh`, the worker's busy refresh | `bend/revive.bend` | `revive_after_refresh` |
| A worker whose supervisor stays lost exits after the lost-exit window (two windows with work in flight). With work in flight it records the session busy and aborts nothing, so a later supervisor resumes the work. Without work it closes the session. | `supervisor_lost.rs` `exit_due`, `work_gate.rs` `orphan_exit` | `bend/orphan.bend` | `orphan_never_aborts_resumable` |
| An idle shutdown (the launcher's replacement of an older daemon) never aborts a run. The supervisor asks each worker to quiesce. An idle worker closes its run gate; a busy worker answers busy. The supervisor stops the workers only when every worker quiesced, else it opens the gates again and answers busy. The client never decides. | `work_gate.rs` `WorkGate`, `idle_shutdown_commits` | `bend/launcher.bend` | `idle_shutdown_never_aborts` |
| A supervisor adopts a live worker only when the worker reports the same build. Another worker stops as a lost worker does (its work stays resumable) and its session starts again on this build. | `supervisor/adoption.rs` `adoption_verdict` | `bend/launcher.bend` | `adopt_same_build` |
| A worker that starts a kernel over a namespace snapshot stores one restore notice in the session. Each attach (a reconnect, a worker restart) rebuilds the transcript from all stored messages. A view shows each restore notice one time: an attach does not show a notice that the view showed before. After an attach, the view showed one notice for each restore. | `eukhe-tui` `restore_notices.rs` `RestoreNotices` (its bridge test is in the same file) | `bend/notice.bend` | `notice_shown_once`, `notice_per_restore` |
| A client start keeps or replaces the daemon on its socket. Versions have an order: the semver order of releases; a `-dev` build or an older-scheme build (such as `0.9.9-main.46`) is below the releases of its series. Only an interactive start (the TUI, `eukhe chat`) replaces a daemon, and only a daemon of a lower version. A background client (the dashboard, the gateway, ACP, the relaunch of a lost daemon) never replaces a daemon. A client never replaces a newer daemon or another build of the same version; it tells the user. Thus the daemon never goes back to a lower version, and k builds cause k - 1 replacements at most. | `eukhe-tui` `daemon_build.rs` `replacement_verdict` (its bridge test is `daemon_build/bridge.rs`), used by `eukhe-cli` `interactive_mode/daemon.rs` | `bend/replace.bend` | `replace_never_downgrades`, `replacement_terminates`, `background_never_replaces` |

An attached client relaunches a lost supervisor of its own build within
one minute of the loss (`CLIENT_RELAUNCH_WITHIN_MS`) when no daemon
listens. It does not replace a daemon that another client started. The
relaunched supervisor adopts the live workers. A worker gives a lost
supervisor five minutes (`WORKER_LOST_EXIT_DEFAULT_MS`).

A client older than the daemon uses the daemon when the protocol
agrees, and says: "this eukhe (vX) is older than the running daemon
(vY): update or run `eukhe shutdown`". When the protocol does not agree,
the client stops with this message.

The launcher replaces a daemon only with `shutdown`
and `ifIdle`, and only when the daemon advertises the `idle_shutdown`
capability. A busy daemon, or a daemon without the capability, keeps
serving. The supervisor waits one `QUIESCE_ANSWER_MS` window for all
quiesce answers. A quiesced worker opens its run gate again after
`QUIESCE_HOLD_MS` when no stop and no release comes.

What the laws do not cover: the wall clock between two processes (the
journal's timestamps; `REVIVAL_CLOCK_SKEW_MS` bounds it), the operating
system's process signals, and the scheduling of the timers.
