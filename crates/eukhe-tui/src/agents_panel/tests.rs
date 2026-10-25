use std::time::Instant;

use serde_json::{json, Value};

use eukhe_types::workflow::{
    WorkflowPhase, WorkflowPhaseState, WorkflowRunSnapshot, WorkflowRunState, WorkflowSize,
};

use super::*;
use crate::activity::park_label;
use crate::theme::ColorMode;

/// The test clock: 2026-10-21T10:00:00Z.
const NOW: &str = "2026-10-21T10:00:00.000Z";

fn ms(iso: &str) -> u64 {
    wall_ms(iso).expect("an RFC 3339 time")
}

fn at(clock: &str) -> String {
    format!("2026-10-21T{clock}.000Z")
}

fn root() -> SessionIdentity {
    SessionIdentity::new(Some("s1".to_string()), Some("sess-1".to_string()), None)
}

/// A subagent row of the session `s1` (or of `parent`'s live id).
fn child(id: &str, name: &str, status: &str, parent: &str, extra: &Value) -> Value {
    let mut summary = json!({
        "sessionId": format!("{id}-sess"),
        "activeSessionId": format!("{id}-live"),
        "sessionName": name,
        "runtimeKind": "subagent",
        "rlmChildId": format!("sub-{id}"),
        "parentActiveSessionId": parent,
    });
    let mut entry = json!({ "agentId": id, "status": status });
    for (key, value) in extra.as_object().expect("object") {
        match key.strip_prefix("entry.") {
            Some(entry_key) => entry[entry_key] = value.clone(),
            None => summary[key] = value.clone(),
        }
    }
    entry["summary"] = summary;
    entry
}

/// A representative family: a worker running a tool (with its context
/// use, spend, and note), its nested child waiting on a retry, a quiet
/// worker, a parked worker, an idle worker (not shown), and a queued
/// child run.
fn roster() -> Vec<Value> {
    vec![
        json!({ "agentId": "s1", "status": "running",
                "summary": { "sessionId": "sess-1", "activeSessionId": "s1", "runtimeKind": "top-level" } }),
        child(
            "a",
            "worker-1",
            "running",
            "s1",
            &json!({
                "created": at("09:58:00"),
                "model": { "id": "elpis/qwen3.8-27b" },
                "thinkingLevel": "high",
                "isStreaming": true,
                "isRunningTools": true,
                "currentTool": { "name": "bash", "startedAt": at("09:59:50") },
                "contextUsage": { "tokens": 12_000, "contextWindow": 128_000, "percent": 9.375 },
                "usage": { "cost": 0.031 },
                "note": "list crates/eukhe-tui",
                "entry.lastHeardFromAt": at("09:59:58"),
            }),
        ),
        child(
            "b",
            "worker-2",
            "running",
            "a-live",
            &json!({
                "created": at("09:59:00"),
                "isStreaming": true,
                "retry": { "attempt": 2, "maxAttempts": 5, "retryAt": at("10:00:08"), "error": "overloaded" },
                "entry.lastHeardFromAt": at("09:59:59"),
            }),
        ),
        child(
            "c",
            "worker-3",
            "running",
            "s1",
            &json!({
                "created": at("09:57:00"),
                "isStreaming": true,
                "lastActivityAt": at("09:58:00"),
                "entry.lastHeardFromAt": at("09:58:30"),
            }),
        ),
        child(
            "d",
            "worker-4",
            "running",
            "s1",
            &json!({
                "created": at("09:00:00"),
                "quotaPark": { "resumeAt": at("12:00:00"), "provider": "anthropic" },
            }),
        ),
        child(
            "e",
            "worker-5",
            "idle",
            "s1",
            &json!({ "created": at("09:00:00") }),
        ),
        child(
            "f",
            "worker-6",
            "running",
            "s1",
            &json!({ "entry.queuedChild": true, "entry.statusLabel": "queued" }),
        ),
    ]
}

fn line(tree: &str, name: &str, status: &str, depth: usize, model: &str) -> RosterLine {
    RosterLine {
        tree: tree.to_string(),
        name: name.to_string(),
        status: status.to_string(),
        admission: None,
        depth,
        model: model.to_string(),
        note: None,
    }
}

fn sources(workers: &[SessionWorker]) -> PanelSources<'_> {
    PanelSources {
        bash: &[],
        workflows: &[],
        workers,
    }
}

fn built(anchor: Instant) -> AgentsPanel {
    AgentsPanel::build(&roster(), &root(), &sources(&[]), anchor, ms(NOW))
}

/// Main's worker stays listed while idle or paused, says so, and does
/// not count as running; a running worker is an ordinary working row.
#[test]
fn the_worker_row_shows_running_paused_or_idle() {
    let worker = |id: &str, state: WorkerRunState| SessionWorker {
        active_session_id: format!("{id}-live"),
        session_id: format!("{id}-sess"),
        name: "worker".to_string(),
        state,
    };
    let theme = crate::theme::Theme::builtin("eukhe", ColorMode::TrueColor);
    let title = |workers: &[SessionWorker]| {
        let panel = AgentsPanel::build(
            &roster(),
            &root(),
            &sources(workers),
            Instant::now(),
            ms(NOW),
        );
        let states: Vec<Option<WorkerRunState>> =
            panel.agents.iter().map(|row| row.worker).collect();
        let view = PanelView {
            mode: PinnedAgents::Full,
            stuck_after_secs: 0,
            focused: false,
            open_key: "Enter",
            expand_key: "Space",
            expand_reach: ExpandReach::Focused,
            frame: 0,
            now: Instant::now(),
            now_ms: ms(NOW),
        };
        let rows: Vec<String> = render_agents_panel(&panel, &view, &theme, 200)
            .iter()
            .map(|row| {
                row.iter()
                    .map(|span| span.content.as_str())
                    .collect::<String>()
            })
            .collect();
        (states, rows)
    };
    let (states, rows) = title(&[worker("e", WorkerRunState::Idle)]);
    assert_eq!(
        states,
        vec![None, None, None, None, Some(WorkerRunState::Idle), None]
    );
    assert!(rows[0].contains("5 running - 1 idle"), "{rows:?}");
    assert!(
        rows[5].contains("worker-5") && rows[5].contains("  idle"),
        "{rows:?}"
    );
    let (states, rows) = title(&[worker("c", WorkerRunState::Paused)]);
    assert_eq!(
        states,
        vec![None, None, Some(WorkerRunState::Paused), None, None]
    );
    assert!(rows[0].contains("4 running - 1 paused"), "{rows:?}");
    assert!(
        rows[3].contains("worker-3") && rows[3].contains("  paused"),
        "{rows:?}"
    );
    let (states, _) = title(&[worker("e", WorkerRunState::Stopped)]);
    assert_eq!(states, vec![None; 5]);
}

/// Every running family member maps to its row, nested in tree order:
/// the tool and its start, the retry wait, the context use, the spend,
/// the park, the queued child, and the last word heard; an idle member
/// has no row.
#[test]
fn running_agents_map_to_their_rows() {
    let anchor = Instant::now();
    let since = |clock: &str| instant_at(anchor, ms(NOW), ms(&at(clock)));
    let expected = vec![
        AgentRow {
            line: RosterLine {
                note: Some("list crates/eukhe-tui".to_string()),
                ..line("|- ", "worker-1", "running", 1, "qwen3.8-27b:high")
            },
            activity: AgentActivity::Working {
                phase: TurnPhase::RunningTool,
                since: since("09:58:00"),
            },
            tool: Some(ToolRun {
                name: "bash".to_string(),
                started_ms: Some(ms(&at("09:59:50"))),
            }),
            retry: None,
            context: Some(ContextUsage {
                tokens: 12_000,
                context_window: 128_000,
            }),
            cost: Some(0.031),
            heard_ms: Some(ms(&at("09:59:58"))),
            worker: None,
        },
        AgentRow {
            line: line("|  `- ", "worker-2", "running", 2, "-"),
            activity: AgentActivity::Working {
                phase: TurnPhase::Retrying,
                since: since("09:59:00"),
            },
            tool: None,
            retry: Some(RetryWait {
                attempt: 2,
                max_attempts: Some(5),
                retry_at: at("10:00:08"),
                error: "overloaded".to_string(),
            }),
            context: None,
            cost: None,
            heard_ms: Some(ms(&at("09:59:59"))),
            worker: None,
        },
        AgentRow {
            line: line("|- ", "worker-3", "running", 1, "-"),
            activity: AgentActivity::Working {
                phase: TurnPhase::Thinking,
                since: since("09:57:00"),
            },
            tool: None,
            retry: None,
            context: None,
            cost: None,
            heard_ms: Some(ms(&at("09:58:30"))),
            worker: None,
        },
        AgentRow {
            line: line("|- ", "worker-4", "running", 1, "-"),
            activity: AgentActivity::Parked(QuotaPark {
                resume_at: at("12:00:00"),
                provider: Some("anthropic".to_string()),
            }),
            tool: None,
            retry: None,
            context: None,
            cost: None,
            heard_ms: Some(ms(&at("09:00:00"))),
            worker: None,
        },
        AgentRow {
            line: line("`- ", "worker-6", "queued", 1, "-"),
            activity: AgentActivity::Working {
                phase: TurnPhase::Queued,
                since: anchor,
            },
            tool: None,
            retry: None,
            context: None,
            cost: None,
            heard_ms: None,
            worker: None,
        },
    ];
    assert_eq!(
        built(anchor),
        AgentsPanel {
            agents: expected,
            jobs: Vec::new(),
        }
    );
}

/// A rebuild over the same feeds equals the last build: a frame loop
/// that rebuilds on every iteration repaints only on a real change.
#[test]
fn a_rebuild_over_the_same_feeds_is_equal() {
    let anchor = Instant::now();
    assert_eq!(built(anchor), built(anchor));
}

/// Only a working agent past the threshold reads as quiet: a retry wait
/// and a park wait on purpose, an agent never heard from has no clock,
/// and `0` turns the signal off.
#[test]
fn quiet_agents_are_the_working_ones_past_the_threshold() {
    let panel = built(Instant::now());
    let quiet = |threshold: u64| -> Vec<Option<u64>> {
        panel
            .agents
            .iter()
            .map(|row| row.quiet_secs(threshold, ms(NOW)))
            .collect()
    };
    assert_eq!(
        [quiet(60), quiet(1), quiet(0)],
        [
            vec![None, None, Some(90), None, None],
            vec![Some(2), None, Some(90), None, None],
            vec![None, None, None, None, None],
        ]
    );
}

fn bash(id: &str, command: &str, status: &str, started_at: Option<&str>) -> BashActivity {
    BashActivity {
        id: id.to_string(),
        command: command.to_string(),
        pid: None,
        started_at: started_at.map(str::to_string),
        status: status.to_string(),
        exit_code: None,
        duration_ms: None,
    }
}

fn workflow(name: &str, state: WorkflowRunState) -> WorkflowRunSnapshot {
    WorkflowRunSnapshot {
        run_id: format!("run-{name}"),
        session_id: "sess-1".to_string(),
        name: name.to_string(),
        description: String::new(),
        size: WorkflowSize::Small,
        state,
        phases: vec![
            WorkflowPhase {
                title: "plan".to_string(),
                state: WorkflowPhaseState::Done,
            },
            WorkflowPhase {
                title: "list".to_string(),
                state: WorkflowPhaseState::Active,
            },
        ],
        agents: Vec::new(),
        spawned: 3,
        done: 1,
        failed: 1,
        max_agents: 5,
        concurrency: 3,
        logs: Vec::new(),
    }
}

/// Running shells and running workflow runs are jobs; finished ones are
/// not.
#[test]
fn running_shells_and_workflow_runs_are_jobs() {
    let shells = [
        bash("b1", "cargo build", "running", Some(&at("09:59:30"))),
        bash("b2", "ls", "exited", Some(&at("09:00:00"))),
    ];
    let runs = [
        workflow("crates", WorkflowRunState::Running),
        workflow("old", WorkflowRunState::Done),
    ];
    let panel = AgentsPanel::build(
        &[],
        &root(),
        &PanelSources {
            bash: &shells,
            workflows: &runs,
            workers: &[],
        },
        Instant::now(),
        ms(NOW),
    );
    assert_eq!(
        panel,
        AgentsPanel {
            agents: Vec::new(),
            jobs: vec![
                JobRow::Bash {
                    command: "cargo build".to_string(),
                    started_ms: Some(ms(&at("09:59:30"))),
                },
                JobRow::Workflow {
                    name: "crates".to_string(),
                    phase: Some("list".to_string()),
                    done: 1,
                    failed: 1,
                    spawned: 3,
                },
            ],
        }
    );
}

/// The block shows while anything runs and the setting leaves it on.
#[test]
fn the_block_shows_while_anything_runs() {
    let agents = built(Instant::now());
    let jobs = AgentsPanel {
        agents: Vec::new(),
        jobs: vec![JobRow::Bash {
            command: "ls".to_string(),
            started_ms: None,
        }],
    };
    let empty = AgentsPanel::default();
    let shown: Vec<[bool; 3]> = [&agents, &jobs, &empty]
        .iter()
        .map(|panel| {
            [
                PinnedAgents::Off,
                PinnedAgents::Collapsed,
                PinnedAgents::Full,
            ]
            .map(|mode| panel.shown(mode))
        })
        .collect();
    assert_eq!(
        shown,
        [
            [false, true, true],
            [false, true, true],
            [false, false, false]
        ]
    );
}

fn texts(panel: &AgentsPanel, mode: PinnedAgents, anchor: Instant) -> Vec<String> {
    texts_from(panel, mode, ExpandReach::AfterFocus("alt+a"), anchor)
}

fn texts_from(
    panel: &AgentsPanel,
    mode: PinnedAgents,
    expand_reach: ExpandReach<'_>,
    anchor: Instant,
) -> Vec<String> {
    let theme = Theme::builtin("eukhe", ColorMode::TrueColor);
    render_agents_panel(
        panel,
        &PanelView {
            mode,
            stuck_after_secs: DEFAULT_STUCK_AFTER_SECS,
            focused: false,
            open_key: "alt+a",
            expand_key: "space",
            expand_reach,
            frame: 0,
            now: anchor,
            now_ms: ms(NOW),
        },
        &theme,
        300,
    )
    .iter()
    .map(|line| line.iter().map(|span| span.content.as_str()).collect())
    .collect()
}

/// The rows say what each agent does: the phase and how long it runs,
/// its model and level, the tool and its time, the retry countdown, the
/// quiet time, the context use, the spend, the note; collapsed, the block
/// shows three rows and counts the rest.
#[test]
fn the_rows_render_and_collapse() {
    let anchor = Instant::now();
    let panel = built(anchor);
    let elapsed = format_working_elapsed;
    let park = park_label(
        &QuotaPark {
            resume_at: at("12:00:00"),
            provider: Some("anthropic".to_string()),
        },
        ms(NOW),
    );
    let full = vec![
        " Agents  5 running  ! 1 quiet".to_string(),
        format!(
            " . |- worker-1  qwen3.8-27b:high  Executing - {}  -> bash {}  ctx 12k/128k 9%  $0.03  list crates/eukhe-tui",
            elapsed(120),
            elapsed(10)
        ),
        format!(
            " . |  `- worker-2  -  Retrying - {}  retry 2/5 in 8s: overloaded",
            elapsed(60)
        ),
        format!(
            " ! |- worker-3  -  Thinking - {}  no activity for {}",
            elapsed(180),
            elapsed(90)
        ),
        format!(" ~ |- worker-4  -  {park}"),
        format!(" ~ `- worker-6  -  Queued - {}", elapsed(0)),
    ];
    assert_eq!(texts(&panel, PinnedAgents::Full, anchor), full);
    let mut collapsed = full[..4].to_vec();
    collapsed.push("   ... 2 more (alt+a, space: expand)".to_string());
    assert_eq!(texts(&panel, PinnedAgents::Collapsed, anchor), collapsed);
    assert_eq!(
        texts(&panel, PinnedAgents::Off, anchor),
        Vec::<String>::new()
    );
}

/// The "N more" row names only keys that expand the block from where the
/// keys go: the expand key while the dock holds the focus; from the
/// editor (where a space is text) the focus key first; nothing while the
/// dock refuses the focus. It once said `space: expand` from the editor,
/// where Space only typed a space.
#[test]
fn the_more_row_names_only_keys_that_work() {
    let anchor = Instant::now();
    let panel = built(anchor);
    let more = |reach| {
        texts_from(&panel, PinnedAgents::Collapsed, reach, anchor)
            .last()
            .cloned()
            .unwrap_or_default()
    };
    assert_eq!(
        [
            ExpandReach::Focused,
            ExpandReach::AfterFocus("alt+a"),
            ExpandReach::Blocked
        ]
        .map(more),
        [
            "   ... 2 more (space: expand)".to_string(),
            "   ... 2 more (alt+a, space: expand)".to_string(),
            "   ... 2 more".to_string(),
        ]
    );
}

/// The expand key opens a collapsed block and folds a full one; the
/// setting's words parse, anything else reads as the default.
#[test]
fn the_mode_toggles_and_parses() {
    assert_eq!(
        [
            PinnedAgents::Off,
            PinnedAgents::Collapsed,
            PinnedAgents::Full
        ]
        .map(PinnedAgents::toggled),
        [
            PinnedAgents::Collapsed,
            PinnedAgents::Full,
            PinnedAgents::Collapsed
        ]
    );
    assert_eq!(
        ["off", "collapsed", "full", "bogus"].map(PinnedAgents::parse),
        [
            PinnedAgents::Off,
            PinnedAgents::Collapsed,
            PinnedAgents::Full,
            PinnedAgents::Collapsed
        ]
    );
}
