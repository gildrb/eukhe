use std::time::Instant;

use base64::Engine;
use eukhe_types::daemon::agent_tree::TreeStatus;

use super::*;
use crate::activity::{AgentActivity, TurnPhase};
use crate::agents_panel::AgentRow;
use crate::chat::{AssistantMessage, ChatEntry, MessageBlock, StatusKind};
use crate::swarm_block::RosterLine;

fn text(raw: &'static str) -> Text<'static> {
    Text::line(raw, MSG_MAX).expect("a printable line")
}

fn root(state: &State<'_>) -> String {
    report(&Status::Root(state))
}

fn decode(value: &str) -> String {
    let bytes = base64::engine::general_purpose::STANDARD
        .decode(value)
        .expect("standard base64");
    String::from_utf8(bytes).expect("UTF-8")
}

/// The pairs of one report, checked against the protocol: the framing,
/// the grammar, every limit, base64 that decodes to text without control
/// characters, and an id that matches the id grammar.
fn checked_pairs(sequence: &str) -> Vec<(String, String)> {
    assert!(sequence.len() <= 4096, "whole sequence over 4096 bytes");
    let body = sequence
        .strip_prefix("\x1b]7501;")
        .and_then(|rest| rest.strip_suffix("\x1b\\"))
        .expect("OSC 7501 framing with ST");
    let value_char =
        |c: char| c.is_ascii_alphanumeric() || matches!(c, '_' | '.' | ',' | '+' | '/' | '=' | '-');
    let pairs: Vec<(String, String)> = body
        .split(':')
        .map(|pair| {
            let (key, value) = pair.split_once('=').expect("key=value");
            assert!(!key.is_empty() && key.len() <= 16, "key length: {key}");
            assert!(
                key.chars().all(|c| c.is_ascii_lowercase()),
                "key set: {key}"
            );
            assert!(value.chars().all(value_char), "value set: {value}");
            (key.to_owned(), value.to_owned())
        })
        .collect();
    for (key, value) in &pairs {
        match key.as_str() {
            "msg" | "title" => {
                let (encoded_cap, decoded_cap) = if key == "msg" {
                    (2732, 2048)
                } else {
                    (256, 192)
                };
                assert!(
                    value.len() <= encoded_cap,
                    "{key} encoded over {encoded_cap}"
                );
                let decoded = decode(value);
                assert!(
                    decoded.len() <= decoded_cap,
                    "{key} decoded over {decoded_cap}"
                );
                assert!(
                    !decoded.chars().any(char::is_control),
                    "{key} has a control char"
                );
            }
            "app" => assert_eq!(value, APP),
            "id" => {
                assert!(value.len() <= 128, "id over 128 bytes");
                let segments: Vec<&str> = value.split('/').collect();
                assert!(segments.len() <= 8, "id deeper than 8");
                for segment in segments {
                    assert!(
                        (1..=32).contains(&segment.len()),
                        "segment length: {segment}"
                    );
                    assert!(
                        segment.chars().all(
                            |c| c.is_ascii_alphanumeric() || matches!(c, '_' | '.' | '+' | '-')
                        ),
                        "segment set: {segment}"
                    );
                }
            }
            "state" => assert!(
                ["idle", "working", "done", "blocked", "error", "clear"].contains(&value.as_str()),
                "state {value}"
            ),
            "kind" => assert!(["permission", "question", "auth"].contains(&value.as_str())),
            other => panic!("unexpected key {other}"),
        }
    }
    pairs
}

/// The spec's examples, with `app=eukhe` in place of their `app`.
#[test]
fn reports_match_the_spec_examples() {
    assert_eq!(
        root(&State::Working {
            msg: Some(text("Installing updates"))
        }),
        "\x1b]7501;state=working:app=eukhe:msg=SW5zdGFsbGluZyB1cGRhdGVz\x1b\\"
    );
    assert_eq!(
        root(&State::Blocked {
            kind: Kind::Auth,
            msg: text("Password required to install updates")
        }),
        "\x1b]7501;state=blocked:kind=auth:app=eukhe:msg=UGFzc3dvcmQgcmVxdWlyZWQgdG8gaW5zdGFsbCB1cGRhdGVz\x1b\\"
    );
    assert_eq!(
        root(&State::Done {
            msg: text("Upgraded 12 packages")
        }),
        "\x1b]7501;state=done:app=eukhe:msg=VXBncmFkZWQgMTIgcGFja2FnZXM=\x1b\\"
    );
    assert_eq!(
        root(&State::Blocked {
            kind: Kind::Permission,
            msg: text("Apply 3 to add, 1 to change, 0 to destroy?")
        }),
        "\x1b]7501;state=blocked:kind=permission:app=eukhe:msg=QXBwbHkgMyB0byBhZGQsIDEgdG8gY2hhbmdlLCAwIHRvIGRlc3Ryb3k/\x1b\\"
    );
    let us_east = ChildRecord {
        id: RecordId("us-east".to_owned()),
        title: text("US East"),
    };
    assert_eq!(
        report(&Status::Child(&us_east)),
        "\x1b]7501;state=working:id=us-east:app=eukhe:title=VVMgRWFzdA==\x1b\\"
    );
    assert_eq!(
        report(&Status::Clear(&us_east.id)),
        "\x1b]7501;state=clear:id=us-east\x1b\\"
    );
    assert_eq!(report(&Status::ClearAll), "\x1b]7501;state=clear\x1b\\");
    assert_eq!(root(&State::Idle), "\x1b]7501;state=idle:app=eukhe\x1b\\");
    assert_eq!(
        root(&State::Error {
            msg: text("rsync failed")
        }),
        "\x1b]7501;state=error:app=eukhe:msg=cnN5bmMgZmFpbGVk\x1b\\"
    );
}

#[test]
fn every_report_passes_the_protocol_checks() {
    let long = "x".repeat(5000);
    let states = [
        State::Idle,
        State::Working { msg: None },
        State::Working {
            msg: Text::line(&long, MSG_MAX),
        },
        State::Blocked {
            kind: Kind::Question,
            msg: text("Summarize branch?"),
        },
        State::Done {
            msg: text("line \u{1b}[31m red \u{7}\u{85} done"),
        },
        State::Error {
            msg: text("Error: 429\n\ttoo many requests"),
        },
    ];
    for state in &states {
        let pairs = checked_pairs(&root(state));
        assert_eq!(pairs[0], ("state".to_owned(), state.wire().to_owned()));
    }
    let child = ChildRecord {
        id: RecordId::of_segments(&[segment(&"n".repeat(40)), segment("a/b c")]).expect("an id"),
        title: Text::line(&"\u{e9}".repeat(400), TITLE_MAX)
            .expect("a title")
            .into_owned(),
    };
    checked_pairs(&report(&Status::Child(&child)));
    checked_pairs(&report(&Status::Clear(&child.id)));
}

#[test]
fn text_is_one_clean_line_within_its_cap() {
    assert_eq!(
        Text::line("  a\nb\tc\u{1b}[0m\u{9f}d  ", MSG_MAX).map(|t| t.0.into_owned()),
        Some("a b c [0m d".to_owned())
    );
    assert_eq!(Text::line(" \n\t\u{7}", MSG_MAX), None);
    assert_eq!(Text::line("", MSG_MAX), None);
    // Clean text borrows.
    assert!(matches!(
        Text::line("Turn finished", MSG_MAX),
        Some(Text(Cow::Borrowed("Turn finished")))
    ));
    // A cut lands on a character boundary and ends in the ellipsis.
    let accents = "\u{e9}".repeat(200);
    let cut = Text::line(&accents, MSG_MAX).expect("a line");
    assert!(cut.0.len() <= MSG_MAX);
    assert!(cut.0.ends_with(ELLIPSIS));
    assert!(cut
        .0
        .trim_end_matches(ELLIPSIS)
        .chars()
        .all(|c| c == '\u{e9}'));
}

#[test]
fn ids_follow_the_id_grammar() {
    assert_eq!(segment("Worker 1/éa"), "Worker-1--a");
    assert_eq!(segment(""), "agent");
    assert_eq!(segment(&"x".repeat(50)).len(), SEGMENT_MAX);
    let nine: Vec<String> = (0..9).map(|n| format!("s{n}")).collect();
    assert_eq!(RecordId::of_segments(&nine), None);
    let wide: Vec<String> = (0..5).map(|_| "x".repeat(32)).collect();
    assert_eq!(RecordId::of_segments(&wide), None, "over 128 bytes");
    let parent = RecordId("a".to_owned());
    assert!(RecordId("a/b".to_owned()).is_within(&parent));
    assert!(RecordId("a".to_owned()).is_within(&parent));
    assert!(!RecordId("ab".to_owned()).is_within(&parent));
}

fn agent(name: &str, depth: usize, status: TreeStatus, activity: AgentActivity) -> AgentRow {
    AgentRow {
        line: RosterLine {
            tree: String::new(),
            name: name.to_owned(),
            status: "running".to_owned(),
            admission: None,
            depth,
            model: String::new(),
            note: None,
        },
        status,
        role: None,
        scope: Vec::new(),
        elapsed_secs: None,
        activity,
        tool: None,
        retry: None,
        context: None,
        cost: None,
        heard_ms: None,
        worker: None,
    }
}

fn working() -> AgentActivity {
    AgentActivity::Working {
        phase: TurnPhase::Requesting,
        since: Instant::now(),
    }
}

fn ids(records: &[ChildRecord]) -> Vec<&str> {
    records.iter().map(|record| record.id.0.as_str()).collect()
}

#[test]
fn running_agents_become_child_records_by_path() {
    let agents = [
        agent("planner", 1, TreeStatus::Running, working()),
        agent("worker", 2, TreeStatus::Running, working()),
        agent("worker", 2, TreeStatus::Running, working()),
        agent("done one", 2, TreeStatus::Finished, AgentActivity::Idle),
        agent("paused", 1, TreeStatus::Running, AgentActivity::Idle),
        agent("bad/name", 1, TreeStatus::Running, working()),
    ];
    let records = child_records(&agents);
    assert_eq!(
        ids(&records),
        ["bad-name", "planner", "planner/worker", "planner/worker+2"]
    );
    assert_eq!(records[2].title, text("worker"));
}

#[test]
fn child_records_stop_at_the_cap() {
    let agents: Vec<AgentRow> = (0..100)
        .map(|n| agent(&format!("a{n}"), 1, TreeStatus::Running, working()))
        .collect();
    assert_eq!(child_records(&agents).len(), CHILDREN_MAX);
}

#[test]
fn a_step_writes_only_changes() {
    let reporter = Reporter::default();
    let (reporter, out) =
        reporter.step(State::Idle, Family::Now(Vec::new()), TerminalProgress::Off);
    assert_eq!(out, "\x1b]7501;state=idle:app=eukhe\x1b\\");
    let (reporter, out) = reporter.step(State::Idle, Family::Unchanged, TerminalProgress::Off);
    assert_eq!(out, "");
    let (reporter, out) = reporter.step(
        State::Working {
            msg: Some(text("fix it")),
        },
        Family::Unchanged,
        TerminalProgress::Shown,
    );
    assert_eq!(
        out,
        format!("\x1b]7501;state=working:app=eukhe:msg=Zml4IGl0\x1b\\{PROGRESS_BUSY}")
    );
    let (reporter, out) = reporter.step(
        State::Working {
            msg: Some(text("fix it")),
        },
        Family::Unchanged,
        TerminalProgress::Shown,
    );
    assert_eq!(out, "", "the same state again writes nothing");
    let (_, out) = reporter.step(
        State::Done { msg: text("Done.") },
        Family::Unchanged,
        TerminalProgress::Shown,
    );
    assert_eq!(
        out,
        format!("\x1b]7501;state=done:app=eukhe:msg=RG9uZS4=\x1b\\{PROGRESS_CLEAR}")
    );
}

#[test]
fn turning_progress_off_clears_it() {
    let busy = || State::Working { msg: None };
    let (reporter, _) =
        Reporter::default().step(busy(), Family::Unchanged, TerminalProgress::Shown);
    let (_, out) = reporter.step(busy(), Family::Unchanged, TerminalProgress::Off);
    assert_eq!(out, PROGRESS_CLEAR);
}

#[test]
fn children_clear_when_they_stop_and_reappear_under_a_cleared_parent() {
    let record = |id: &str| ChildRecord {
        id: RecordId(id.to_owned()),
        title: Text::line(id, TITLE_MAX).expect("a title").into_owned(),
    };
    let (reporter, _) = Reporter::default().step(
        State::Idle,
        Family::Now(vec![record("a"), record("a/b"), record("c")]),
        TerminalProgress::Off,
    );
    let (_, out) = reporter.step(
        State::Idle,
        Family::Now(vec![record("a/b"), record("c")]),
        TerminalProgress::Off,
    );
    assert_eq!(
        out,
        format!(
            "\x1b]7501;state=clear:id=a\x1b\\{}",
            report(&Status::Child(&record("a/b")))
        )
    );
}

#[test]
fn a_process_exit_leaves_the_latest_run_end() {
    let answered = RunEnd::Answered(text("All tests pass."));
    // Read and back at the prompt: the exit leaves the end again.
    let (idle, _) = Reporter::default().step(State::Idle, Family::Unchanged, TerminalProgress::Off);
    assert_eq!(
        idle.leave(Leave::Process {
            last_run: Some(&answered)
        }),
        "\x1b]7501;state=done:app=eukhe:msg=QWxsIHRlc3RzIHBhc3Mu\x1b\\"
    );
    // Still unread: nothing more to say.
    let (done, _) =
        Reporter::default().step(answered.state(), Family::Unchanged, TerminalProgress::Off);
    assert_eq!(
        done.leave(Leave::Process {
            last_run: Some(&answered)
        }),
        ""
    );
    // A run still going when the client leaves: the terminal drops the
    // working record; progress goes.
    let (busy, _) = Reporter::default().step(
        State::Working { msg: None },
        Family::Unchanged,
        TerminalProgress::Shown,
    );
    assert_eq!(
        busy.leave(Leave::Process {
            last_run: Some(&answered)
        }),
        PROGRESS_CLEAR
    );
    // No run, or one the user stopped: nothing.
    let (idle, _) = Reporter::default().step(State::Idle, Family::Unchanged, TerminalProgress::Off);
    assert_eq!(idle.leave(Leave::Process { last_run: None }), "");
    let (idle, _) = Reporter::default().step(State::Idle, Family::Unchanged, TerminalProgress::Off);
    assert_eq!(
        idle.leave(Leave::Process {
            last_run: Some(&RunEnd::Interrupted)
        }),
        ""
    );
    let (busy, _) = Reporter::default().step(
        State::Working { msg: None },
        Family::Unchanged,
        TerminalProgress::Shown,
    );
    assert_eq!(
        busy.leave(Leave::Handoff),
        format!("\x1b]7501;state=clear\x1b\\{PROGRESS_CLEAR}")
    );
}

fn reply(blocks: Vec<MessageBlock>, error: Option<&str>, aborted: bool) -> ChatEntry {
    ChatEntry::Assistant(Box::new(AssistantMessage {
        blocks,
        has_tool_calls: false,
        streaming: false,
        error: error.map(str::to_owned),
        aborted,
    }))
}

fn user() -> ChatEntry {
    ChatEntry::User {
        text: "go".to_owned(),
    }
}

#[test]
fn a_run_end_reads_the_rows_after_the_prompt() {
    let answer = reply(
        vec![MessageBlock::Text(
            "Fixed it.\n\n```rust\nfn x() {}\n```\nAll tests pass.\n".to_owned(),
        )],
        None,
        false,
    );
    assert_eq!(
        run_end(&[user(), answer.clone()]),
        RunEnd::Answered(text("All tests pass."))
    );
    assert_eq!(
        run_end(&[
            user(),
            reply(Vec::new(), Some("Error: 500 overloaded"), false)
        ]),
        RunEnd::Failed(text("Error: 500 overloaded"))
    );
    assert_eq!(
        run_end(&[
            user(),
            ChatEntry::Status {
                text: "! Error: the session closed".to_owned(),
                kind: StatusKind::Error,
            }
        ]),
        RunEnd::Failed(text("! Error: the session closed"))
    );
    assert_eq!(
        run_end(&[user(), reply(Vec::new(), Some("Operation aborted"), true)]),
        RunEnd::Interrupted
    );
    // A reply before this run's prompt is not its answer.
    assert_eq!(run_end(&[answer, user()]), RunEnd::Answered(TURN_FINISHED));
}
