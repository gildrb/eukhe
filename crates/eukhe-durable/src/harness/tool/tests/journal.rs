//! A tool call's journal as the compiled core runs it (`laws/tool_call.bend`):
//! reports raced from real threads against the call's end.

use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::{Arc, Mutex, PoisonError};
use std::thread::JoinHandle;

use eukhe_ai::providers::faux::RegisterFauxProviderOptions;
use tokio::sync::Notify;

use super::support::{calls, done, result_text, results, run, tool_with};
use crate::harness::output::Truncation;
use crate::harness::tests::chat_support::chat_setup;
use crate::harness::tests::support::{add_tool, context};
use crate::harness::types::{ToolExecutionResult, ToolOutputChunk};

/// Threads that report while the call ends.
const THREADS: usize = 4;
/// Reports the call takes before its execute returns.
const BEFORE_END: usize = 200;

fn lock<T>(mutex: &Mutex<T>) -> std::sync::MutexGuard<'_, T> {
    mutex.lock().unwrap_or_else(PoisonError::into_inner)
}

/// Each thread reports one byte at a time until the call refuses it; the
/// execute returns once the call took [`BEFORE_END`] reports, while the
/// threads go on. The settle carries exactly the bytes the call took, and
/// every thread ends on the refusal of a settled call
/// (`stream_settle_carries_all`, `tool_call_step_is_model`).
#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn reports_racing_the_end_from_threads_settle_exactly_what_the_call_took() {
    let setup = chat_setup(RegisterFauxProviderOptions::default());
    let taken = Arc::new(AtomicUsize::new(0));
    let threads: Arc<Mutex<Vec<JoinHandle<String>>>> = Arc::default();
    let (counted, spawned) = (Arc::clone(&taken), Arc::clone(&threads));
    add_tool(
        &setup.registry,
        tool_with(
            "racer",
            move |_, api, _| {
                let (taken, threads) = (Arc::clone(&counted), Arc::clone(&spawned));
                async move {
                    let enough = Arc::new(Notify::new());
                    // The progress publications a report schedules run on the runtime.
                    let runtime = tokio::runtime::Handle::current();
                    for _ in 0..THREADS {
                        let (api, taken, enough, runtime) = (
                            Arc::clone(&api),
                            Arc::clone(&taken),
                            Arc::clone(&enough),
                            runtime.clone(),
                        );
                        lock(&threads).push(std::thread::spawn(move || {
                            let _runtime = runtime.enter();
                            loop {
                                match api.output(ToolOutputChunk::Text("x"), None) {
                                    Ok(()) => {
                                        if taken.fetch_add(1, Ordering::SeqCst) + 1 == BEFORE_END {
                                            enough.notify_one();
                                        }
                                    }
                                    Err(refused) => return refused.to_string(),
                                }
                            }
                        }));
                    }
                    enough.notified().await;
                    Ok(ToolExecutionResult::default())
                }
            },
            |registration| registration.truncation = Truncation::Off,
        ),
        None,
    )
    .unwrap();
    let ran = run(
        &setup,
        vec![
            calls(&[("racer", serde_json::json!({}), "c1")]).into(),
            done().into(),
        ],
    )
    .await;
    let refusals: Vec<String> = std::mem::take(&mut *lock(&threads))
        .into_iter()
        .map(|thread| thread.join().unwrap())
        .collect();
    let taken = taken.load(Ordering::SeqCst);
    assert!(taken >= BEFORE_END, "{taken}");
    assert_eq!(
        (result_text(&results(&ran.entries)[0]), refusals),
        (
            "x".repeat(taken),
            vec!["Tool call c1 has settled".to_owned(); THREADS]
        )
    );
    ran.harness.close(context()).await.unwrap();
}
