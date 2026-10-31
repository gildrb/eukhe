//! `rlm.query`, `rlm.query_batch` and `history` on a real kernel with the
//! faux provider: answers come back as values, nothing but the cell's own
//! call and result enters the transcript, a batch never runs more queries
//! at once than the session's cap, a batch over the budget is refused with
//! its exact text, and the queries' usage lands on the cell's call.

use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::{Arc, Mutex, PoisonError};

use eukhe_ai::providers::faux::{
    faux_assistant_message, faux_text, FauxAssistantMessageOptions, FauxResponseStep,
};
use eukhe_durable::types::SubmissionStatus;
use eukhe_types::pi_ai::{Message, TextContent, UserContent, UserContentBlock};
use futures::FutureExt;

use super::{
    entries, ipython, kernel_test_lock, result_text, results, settle, submit, text, Fixture,
};

/// A faux step answering `reply` that keeps the request's messages.
fn answering(reply: &'static str, seen: &Arc<Mutex<Vec<Vec<Message>>>>) -> FauxResponseStep {
    let seen = Arc::clone(seen);
    FauxResponseStep::factory(move |context, _options, _state, _model| {
        seen.lock()
            .unwrap_or_else(PoisonError::into_inner)
            .push(context.messages().to_vec());
        Ok(faux_assistant_message(
            vec![faux_text(reply)],
            FauxAssistantMessageOptions::default(),
        ))
    })
}

fn write_settings(fixture: &Fixture, settings: &serde_json::Value) {
    std::fs::write(
        fixture.dir.path().join("agent").join("settings.json"),
        settings.to_string(),
    )
    .expect("settings written");
}

#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn a_query_answers_the_cell_as_a_value_and_leaves_no_entry() {
    let _kernel = kernel_test_lock().await;
    let fixture = Fixture::new();
    let seen = Arc::default();
    let code = "ctx = 'alpha ' * 10\nr = await rlm.query('summarize', ctx)\nprint(len(r), r, r.truncated, r.model)\nprint([e.kind for e in history.entries()])";
    fixture.faux.set_responses(vec![
        ipython("c1", code),
        answering("short answer", &seen),
        text("done"),
    ]);
    let session = fixture.open().await;

    let id = submit(&session, "go").await;
    assert_eq!(settle(&session, id).await, SubmissionStatus::Done);
    let all = entries(&session).await;
    let tool_results = results(&all);
    assert_eq!(
        (
            all.iter()
                .map(|entry| entry.kind.as_str())
                .collect::<Vec<_>>(),
            result_text(&tool_results[0]),
        ),
        (
            // The session's own system and custom rows of the turn, then the
            // cell's call and result: the query added no entry.
            vec![
                "pi.user",
                "pi.system",
                "eukhe.custom",
                "pi.assistant",
                "pi.tool-result",
                "pi.assistant"
            ],
            "12 short answer False faux/faux-1\n['user', 'system', 'custom', 'assistant']\n"
                .to_owned()
        )
    );
    assert!(
        tool_results[0]
            .usage
            .as_ref()
            .is_some_and(|usage| usage.total_tokens > 0),
        "the query's usage counts on the cell's call: {:?}",
        tool_results[0].usage
    );
    let seen = seen.lock().unwrap_or_else(PoisonError::into_inner).clone();
    assert_eq!(seen.len(), 1);
    let users: Vec<&UserContent> = seen[0]
        .iter()
        .filter_map(|message| match message {
            Message::User(user) => Some(&user.content),
            Message::System(_) | Message::Assistant(_) | Message::ToolResult(_) => None,
        })
        .collect();
    assert_eq!(
        users,
        vec![&UserContent::Blocks(vec![
            UserContentBlock::Text(TextContent::new(format!(
                "<context>\n{}\n</context>",
                "alpha ".repeat(10)
            ))),
            UserContentBlock::Text(TextContent::new("summarize")),
        ])]
    );
    assert!(
        seen[0].iter().all(|message| match message {
            Message::System(system) => system.tools_added.as_ref().is_none_or(Vec::is_empty),
            Message::User(_) | Message::Assistant(_) | Message::ToolResult(_) => true,
        }),
        "a query offers no tools: {:?}",
        seen[0]
    );
    session.close(super::cx()).await.expect("close");
}

#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn a_batch_never_runs_more_queries_than_the_cap() {
    let _kernel = kernel_test_lock().await;
    let fixture = Fixture::new();
    write_settings(
        &fixture,
        &serde_json::json!({ "rlm": { "queryConcurrency": 2 } }),
    );
    let in_flight = Arc::new(AtomicUsize::new(0));
    let peak = Arc::new(AtomicUsize::new(0));
    // Each query waits for a second one: a wave of two passes, and any
    // run of more than two at once shows in the peak.
    let pair = Arc::new(tokio::sync::Barrier::new(2));
    let step = || {
        let (in_flight, peak, pair) =
            (Arc::clone(&in_flight), Arc::clone(&peak), Arc::clone(&pair));
        FauxResponseStep::Factory(Arc::new(move |_context, _options, _state, _model| {
            let (in_flight, peak, pair) =
                (Arc::clone(&in_flight), Arc::clone(&peak), Arc::clone(&pair));
            async move {
                let now = in_flight.fetch_add(1, Ordering::SeqCst) + 1;
                peak.fetch_max(now, Ordering::SeqCst);
                pair.wait().await;
                in_flight.fetch_sub(1, Ordering::SeqCst);
                Ok(faux_assistant_message(
                    vec![faux_text("part")],
                    FauxAssistantMessageOptions::default(),
                ))
            }
            .boxed()
        }))
    };
    let code = "rs = await rlm.query_batch([{'prompt': f'q{i}', 'context': 'shared'} for i in range(6)])\nprint([str(r) for r in rs])";
    let mut steps = vec![ipython("c1", code)];
    steps.extend((0..6).map(|_| step()));
    steps.push(text("done"));
    fixture.faux.set_responses(steps);
    let session = fixture.open().await;

    let id = submit(&session, "go").await;
    assert_eq!(settle(&session, id).await, SubmissionStatus::Done);
    let all = results(&entries(&session).await);
    assert_eq!(
        (result_text(&all[0]), peak.load(Ordering::SeqCst)),
        (format!("{:?}\n", ["part"; 6]).replace('"', "'"), 2)
    );
    session.close(super::cx()).await.expect("close");
}

#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn a_batch_over_the_budget_is_refused_with_its_text() {
    let _kernel = kernel_test_lock().await;
    let fixture = Fixture::new();
    write_settings(
        &fixture,
        &serde_json::json!({ "rlm": { "queryBudgetBytes": 10 } }),
    );
    let code = "try:\n    await rlm.query('summarize', 'x' * 20)\nexcept rlm.RLMQueryError as error:\n    print(error)\ntry:\n    chat.view()\nexcept RuntimeError as error:\n    print(error)";
    fixture
        .faux
        .set_responses(vec![ipython("c1", code), text("done")]);
    let session = fixture.open().await;

    let id = submit(&session, "go").await;
    assert_eq!(settle(&session, id).await, SubmissionStatus::Done);
    let all = results(&entries(&session).await);
    assert_eq!(
        result_text(&all[0]),
        "rlm.query needs 29 bytes of input; the session's query budget has 10 of 10 bytes left (rlm.queryBudgetBytes)\nthis session has no chat memory: read its history with history.entries(), history.entry(id) and history.compactions()\n"
    );
    assert_eq!(
        fixture.faux.state().call_count,
        2,
        "the refused query made no model call"
    );
    session.close(super::cx()).await.expect("close");
}
