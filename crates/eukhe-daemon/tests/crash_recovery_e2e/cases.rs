//! The crash matrix: every phase against every kill target.

use super::*;

/// The threshold-compaction world: a small window and reserve, so a few
/// padded turns cross the blocking threshold.
const COMPACTION_WINDOW: u64 = 24_000;
const COMPACTION_RESERVE: u64 = 4_000;

/// Filler words of a padded turn (about two tokens each).
const TURN_PAD: usize = 600;

/// A message long enough (over one 512-byte tree line) that the chat
/// compactor summarizes it.
const NODE_PAD: usize = 120;

fn run_case(phase: Phase, target: Target) {
    let (rlm_depth, window, settings) = match phase {
        Phase::Compaction => (
            1,
            COMPACTION_WINDOW,
            json!({ "compaction": {
                "enabled": true,
                "reserveTokens": COMPACTION_RESERVE,
                "keepRecentTokens": 10,
            }}),
        ),
        Phase::Stream | Phase::Tool | Phase::MemoryNode => (0, 128_000, json!({})),
    };
    let mut world = World::new(window, &settings);
    let mut client = world.connect();
    let session_id = world.create(&mut client, rlm_depth);
    let mut prompts: Vec<String> = Vec::new();

    // Pre-crash history.
    for tag in ["t1", "t2"] {
        let message = prompt(tag, &[], 0);
        run_turn(&mut client, &session_id, &message);
        prompts.push(message);
    }

    // Drive the crash turn into its phase.
    let pid = worker_pid(&mut client, &session_id);
    let crash_prompt = match phase {
        Phase::Stream => {
            let message = prompt("crash", &[HOLD_STREAM], 0);
            client.send(
                &json!({ "type": "prompt", "activeSessionId": session_id, "message": message }),
            );
            world.mock.wait_for(WAIT, "the held answer stream", |log| {
                log.iter()
                    .any(|entry| entry.holding && entry.request.prompt.contains(HOLD_STREAM))
                    .then_some(())
            });
            message
        }
        Phase::Tool => {
            let message = prompt("crash", &[SLOW_TOOL], 0);
            client.send(
                &json!({ "type": "prompt", "activeSessionId": session_id, "message": message }),
            );
            let runs = world.tool_runs_path();
            let deadline = Instant::now() + WAIT;
            while !runs.exists() {
                assert!(Instant::now() < deadline, "the slow tool never started");
                std::thread::sleep(Duration::from_millis(20));
            }
            message
        }
        Phase::MemoryNode => {
            let message = prompt("crash", &[], NODE_PAD);
            client.send(
                &json!({ "type": "prompt", "activeSessionId": session_id, "message": message }),
            );
            world.mock.wait_for(WAIT, "the held tree line", |log| {
                log.iter()
                    .any(|entry| entry.holding && entry.request.kind == RequestKind::MemoryNode)
                    .then_some(())
            });
            message
        }
        Phase::Compaction => {
            // Padded turns until one's preparation holds the summarizer.
            let mut turn = 0;
            loop {
                turn += 1;
                assert!(turn < 30, "the threshold never crossed");
                let message = prompt(&format!("p{turn}"), &[], TURN_PAD);
                let id = client.send(&json!({
                    "type": "prompt_and_wait",
                    "activeSessionId": session_id,
                    "message": message,
                }));
                let held = world
                    .mock
                    .wait_for(WAIT, "the turn or its compaction", |log| {
                        if log.iter().any(|entry| {
                            entry.holding && entry.request.kind == RequestKind::Summarizer
                        }) {
                            return Some(true);
                        }
                        client.try_response(&id).map(|_| false)
                    });
                if held {
                    break message;
                }
                let done = client.response(&id, WAIT);
                assert_eq!(done["success"], true, "padded turn: {done}");
                prompts.push(message);
            }
        }
    };
    prompts.push(crash_prompt);
    let chat_before = world.chat_messages();
    let log_before = world.mock.log().len();

    // The crash.
    match target {
        Target::Worker => {
            sigkill(pid);
            wait_dead(pid);
        }
        Target::Supervisor => world.kill_supervisor(),
        Target::Both => {
            world.kill_supervisor();
            sigkill(pid);
            wait_dead(pid);
        }
    }
    drop(client);
    // Reattach mid-turn: after a worker crash the supervisor relaunches the
    // worker under the same active id; after a supervisor crash the client
    // resumes the stored session (a revived worker is joined).
    let (mut client, session_id) = match target {
        Target::Worker => (reattach(&world, &session_id), session_id),
        Target::Supervisor | Target::Both => {
            world.start_supervisor();
            let mut client = world.connect();
            let session_id = world.resume(&mut client, rlm_depth);
            (client, session_id)
        }
    };
    match phase {
        Phase::Stream => world.mock.open_gate(STREAM_GATE),
        Phase::Tool => std::fs::write(world.release_path(), "go").expect("release the tool"),
        Phase::Compaction => world.mock.open_gate(SUMMARIZER_GATE),
        Phase::MemoryNode => world.mock.open_gate(NODE_GATE),
    }
    wait_idle(&mut client, &session_id);

    // The session keeps working after the recovery.
    let next = prompt("next", &[], 0);
    run_turn(&mut client, &session_id, &next);
    prompts.push(next.clone());
    wait_idle(&mut client, &session_id);

    let log = world.mock.log();
    let context = format!(
        "phase {phase:?}, target {target:?}; provider log: {:#?}",
        mock_llm::summary(&log)
    );

    // Each turn finished exactly once; nothing lost or duplicated.
    assert_transcript(&world, &prompts);

    // The crash phase's own provider traffic.
    let crashed = &log[..log_before];
    let after = &log[log_before..];
    match phase {
        Phase::Stream => {
            let held = requests(&log, |entry| {
                entry.request.kind == RequestKind::Turn
                    && entry.request.prompt.contains(HOLD_STREAM)
            });
            match target {
                // The killed worker's stream dropped; its replacement asked
                // again once and got the answer.
                Target::Worker | Target::Both => assert_eq!(
                    served(
                        &held
                            .iter()
                            .map(|entry| (*entry).clone())
                            .collect::<Vec<_>>()
                    ),
                    vec![Served::Dropped, Served::Complete],
                    "{context}"
                ),
                // The worker outlived its supervisor: the one stream ran on.
                Target::Supervisor => assert_eq!(
                    served(
                        &held
                            .iter()
                            .map(|entry| (*entry).clone())
                            .collect::<Vec<_>>()
                    ),
                    vec![Served::Complete],
                    "{context}"
                ),
            }
        }
        Phase::Tool => {
            // The cell ran once: a resumed run never runs a call again that
            // may have partially run; it stores the interruption as the
            // call's one result instead.
            let runs = std::fs::read_to_string(world.tool_runs_path()).expect("tool runs");
            assert_eq!(runs.lines().count(), 1, "{context}");
            let transcript = world.transcript();
            let results: Vec<String> = messages_of(&transcript, "toolResult")
                .iter()
                .map(|(_, message)| texts(message).join("\n"))
                .collect();
            let expected = match target {
                Target::Worker | Target::Both => {
                    "Tool ipython was interrupted and may have partially run"
                }
                Target::Supervisor => "tool finished",
            };
            assert!(
                results.len() == 1 && results[0].contains(expected),
                "the call's one result: {results:?}; {context}"
            );
            let after_tool: Vec<Served> = log
                .iter()
                .filter(|entry| entry.request.after_tool)
                .map(|entry| entry.served)
                .collect();
            assert_eq!(after_tool, vec![Served::Complete], "{context}");
        }
        Phase::Compaction => {
            let summarizers = |entries: &[Logged]| {
                entries
                    .iter()
                    .filter(|entry| entry.request.kind == RequestKind::Summarizer)
                    .map(|entry| entry.served)
                    .collect::<Vec<_>>()
            };
            let expected = match target {
                Target::Worker | Target::Both => (vec![Served::Dropped], vec![Served::Complete]),
                Target::Supervisor => (vec![Served::Complete], vec![]),
            };
            assert_eq!(
                (summarizers(crashed), summarizers(after)),
                expected,
                "{context}"
            );
            // Exactly one compaction, committed (never a second run, never
            // a failure row for the run that finished).
            let transcript = world.transcript();
            assert_eq!(
                (
                    transcript.of_kind("pi.compaction").len(),
                    transcript.custom_rows("compaction_outcome").len()
                ),
                (1, 0),
                "{context}"
            );
        }
        Phase::MemoryNode => {
            let nodes = |entries: &[Logged]| {
                entries
                    .iter()
                    .filter(|entry| entry.request.kind == RequestKind::MemoryNode)
                    .map(|entry| entry.served)
                    .collect::<Vec<_>>()
            };
            // The supervisor owns the chat and runs its compactor: a dead
            // session worker leaves the held call alone; a dead supervisor
            // takes it along, and the next owner asks again, once.
            let expected = match target {
                Target::Worker => (vec![Served::Complete], vec![]),
                Target::Supervisor | Target::Both => {
                    (vec![Served::Dropped], vec![Served::Complete])
                }
            };
            assert_eq!((nodes(crashed), nodes(after)), expected, "{context}");
        }
    }

    // The chat memory: the pre-crash content, then the finished turns,
    // each message once.
    let chat_after = world.chat_messages();
    assert_chat_log(&chat_after);
    assert_chat_tree(&world.chat_tree());
    let before = chat_content(&chat_before);
    let after_content = chat_content(&chat_after);
    match phase {
        Phase::Compaction => {
            // A depth-1 session reads the chat and logs nothing.
            assert_eq!(after_content, before, "{context}");
        }
        Phase::Stream | Phase::Tool | Phase::MemoryNode => {
            assert_eq!(
                &after_content[..before.len().min(after_content.len())],
                &before[..],
                "the pre-crash chat is a prefix: {context}"
            );
            let unique: BTreeSet<&(String, String)> = after_content.iter().collect();
            assert_eq!(
                unique.len(),
                after_content.len(),
                "a chat message is logged twice: {after_content:#?}"
            );
            let users: Vec<&str> = after_content
                .iter()
                .filter(|(kind, _)| kind == "user")
                .map(|(_, text)| text.as_str())
                .collect();
            assert_eq!(
                users,
                prompts.iter().map(String::as_str).collect::<Vec<_>>(),
                "every prompt logged once, in order"
            );
            let answers: Vec<&str> = after_content
                .iter()
                .filter(|(_, text)| text.starts_with("answer to "))
                .map(|(_, text)| text.as_str())
                .collect();
            let expected: Vec<String> = prompts
                .iter()
                .map(|prompt| answer_for(&prompt_tag(prompt)))
                .collect();
            assert_eq!(
                answers,
                expected.iter().map(String::as_str).collect::<Vec<_>>(),
                "every answer logged once, in order"
            );
        }
    }
    if phase == Phase::MemoryNode {
        // The long message's tree line was built exactly once, from the
        // one call that finished.
        let crash_id = chat_after
            .iter()
            .find(|message| message["text"].as_str() == prompts.get(2).map(String::as_str))
            .and_then(|message| message["i"].as_u64())
            .expect("the crash prompt is in the chat");
        let texts: Vec<Value> = world
            .chat_tree()
            .into_iter()
            .filter(|line| line["l"] == 0 && line["i"] == crash_id)
            .map(|line| line["text"].clone())
            .collect();
        assert_eq!(texts, vec![json!("A padded user message.")], "{context}");
    }
}

#[test]
fn worker_killed_mid_stream() {
    run_case(Phase::Stream, Target::Worker);
}

#[test]
fn supervisor_killed_mid_stream() {
    run_case(Phase::Stream, Target::Supervisor);
}

#[test]
fn daemon_and_worker_killed_mid_stream() {
    run_case(Phase::Stream, Target::Both);
}

#[test]
fn worker_killed_mid_tool_call() {
    run_case(Phase::Tool, Target::Worker);
}

#[test]
fn supervisor_killed_mid_tool_call() {
    run_case(Phase::Tool, Target::Supervisor);
}

#[test]
fn daemon_and_worker_killed_mid_tool_call() {
    run_case(Phase::Tool, Target::Both);
}

#[test]
fn worker_killed_mid_compaction() {
    run_case(Phase::Compaction, Target::Worker);
}

#[test]
fn supervisor_killed_mid_compaction() {
    run_case(Phase::Compaction, Target::Supervisor);
}

#[test]
fn daemon_and_worker_killed_mid_compaction() {
    run_case(Phase::Compaction, Target::Both);
}

#[test]
fn worker_killed_mid_memory_compaction() {
    run_case(Phase::MemoryNode, Target::Worker);
}

#[test]
fn supervisor_killed_mid_memory_compaction() {
    run_case(Phase::MemoryNode, Target::Supervisor);
}

#[test]
fn daemon_and_worker_killed_mid_memory_compaction() {
    run_case(Phase::MemoryNode, Target::Both);
}
