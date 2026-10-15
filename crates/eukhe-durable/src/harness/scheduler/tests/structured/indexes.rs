//! The scheduler's ownership indexes are bounded by live work.

use eukhe_chord::json::JsonValue;

use super::{
    create, end, in_conversation, open_memory_nodes, owned, owned_conversation, running, settle,
    Behavior, End, Opened, Script,
};
use crate::harness::scheduler::IndexSizes;
use crate::harness::tests::support::context;
use crate::types::TaskOutcome;

/// Subagent calls the parent makes, one after the other.
const CALLS: usize = 25;

#[tokio::test]
async fn forgets_the_chains_of_ended_subagent_calls_below_a_live_parent() {
    let script = Script::new();
    let Opened { harness, root, .. } = open_memory_nodes(&script).await;
    script.script(
        "parent",
        Behavior::default().run(|script, runtime, cx| async move {
            script.slot("running").resolve(runtime.task_id().erase());
            script.gate("parent").wait().await;
            runtime
                .commit(
                    |_, _| async { Ok(Some(end(End::Completed, "parent"))) },
                    &cx,
                )
                .await
        }),
    );
    // A subagent call: a conversation the call owns, with a run in it; the
    // call ends in its next phase, holding its outcome until the run ends.
    script.script(
        "call",
        Behavior::default().run(|script, runtime, cx| async move {
            let call = runtime.task_id().erase();
            runtime
                .commit(
                    move |tx, _| async move {
                        let conversation =
                            tx.create_conversation(owned_conversation(call)).await?.id;
                        create(&tx, script.node(), "run", in_conversation(conversation)).await?;
                        Ok(Some(running(1)))
                    },
                    &cx,
                )
                .await
        }),
    );
    script.open("run");
    let parent = script.start(&root, "parent").await;
    script.slot("running").wait().await;
    // The parent, listed below the root conversation, whose edge is known.
    let baseline = IndexSizes {
        live: 1,
        settled: 0,
        edges: 1,
        below: 1,
        roots: 1,
        unloaded: 0,
        drop_queue: 0,
    };
    assert_eq!(harness.core().tasks().index_sizes(), baseline);
    for _ in 0..CALLS {
        let call = script.start_with(&root, "call", owned(parent)).await;
        assert_eq!(
            settle(&harness, call).await,
            TaskOutcome::Completed {
                result: JsonValue::from("call")
            }
        );
    }
    // Neither the ended calls nor their conversations' owner edges are kept.
    assert_eq!(harness.core().tasks().index_sizes(), baseline);
    script.open("parent");
    assert_eq!(
        settle(&harness, parent).await,
        TaskOutcome::Completed {
            result: JsonValue::from("parent")
        }
    );
    harness.close(context()).await.unwrap();
}
