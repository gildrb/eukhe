//! The bridge between the idle deadline's decisions and its Bend model
//! (`bend/retry.bend` §6, whose laws `LAWS.bend` section `retry` states
//! and `PROOF.bend` proves): both run the same scenarios and must print
//! the same transcript, byte for byte. `bend/bridge_retry.bend` documents
//! the scenario format (its `i` lines). The deferred job (§4) has no
//! bridge: its decisions run as `bend/run.bend` in the compiled core (laws
//! `run_failed_poll_is_the_job_model` and the like); the stall (§5) runs
//! as the compiled model too (`bend/ffi_retry.bend`).
//!
//! An `i` case runs the real idle deadline (`StreamIdle::within` behind
//! [`Models::complete_simple`]) on a stream whose provider sends an event
//! after each gap and ends it with the last one, on paused tokio time: the
//! clock moves only to the next timer, so the end is exact. No gap equals
//! the deadline: an event and the deadline at the same instant race.
//!
//! [`compare`] runs it (and skips without `bend`, unless
//! `EUKHE_REQUIRE_BEND` is set).

use std::fmt::Write as _;
use std::sync::Arc;
use std::time::Duration;

use eukhe_ai::models::{create_models, CreateModelsOptions, Models};
use eukhe_ai::providers::faux::{
    faux_assistant_message, faux_provider, FauxAssistantMessageOptions, RegisterFauxProviderOptions,
};
use eukhe_ai::types::SimpleStreamOptions;
use eukhe_ai::utils::event_stream::AssistantMessageEventStream;
use eukhe_ai::utils::retry::stalled_idle_ms;
use eukhe_types::pi_ai::{AssistantMessageEvent, Context, DoneReason, StopReason};
use tokio::time::Instant;

use crate::testing::bridge::{compare, Rng, Scenario};

/// A stream whose events come `gaps` ms apart; the last one ends it. With
/// no gap it sends nothing and never ends.
fn paced(gaps: Vec<u64>) -> AssistantMessageEventStream {
    let stream = AssistantMessageEventStream::new();
    let target = stream.clone();
    let message = faux_assistant_message("ok", FauxAssistantMessageOptions::default());
    tokio::spawn(async move {
        let Some((end, events)) = gaps.split_last() else {
            return std::future::pending().await;
        };
        for gap in events {
            tokio::time::sleep(Duration::from_millis(*gap)).await;
            target.push(AssistantMessageEvent::Start {
                partial: message.clone().into(),
            });
        }
        tokio::time::sleep(Duration::from_millis(*end)).await;
        target.push(AssistantMessageEvent::Done {
            reason: DoneReason::Stop,
            message: message.clone(),
        });
        target.end(Some(message));
    });
    stream
}

/// How the real idle deadline of `deadline` ms ends the paced stream of
/// `gaps`: the `i` line.
fn idle_line(deadline: u64, gaps: &[u64]) -> String {
    let runtime = tokio::runtime::Builder::new_current_thread()
        .enable_all()
        .start_paused(true)
        .build()
        .expect("a paused runtime");
    runtime.block_on(async {
        let faux = faux_provider(RegisterFauxProviderOptions::default());
        let model = faux.get_model();
        let mut provider = faux.provider.clone();
        let gaps = gaps.to_vec();
        provider.stream_simple = Arc::new(move |_, _, _| paced(gaps.clone()));
        let models: Models = create_models(CreateModelsOptions::default());
        models.set_provider(provider);
        let mut options = SimpleStreamOptions::default();
        #[expect(
            clippy::cast_precision_loss,
            reason = "the bridge's deadlines are far below 2^53 ms"
        )]
        let idle = deadline as f64;
        options.stream.request.stream_idle_timeout_ms = Some(idle);
        let context: Context = serde_json::from_value(serde_json::json!({
            "messages": [{ "role": "user", "content": "hi", "timestamp": 0 }],
        }))
        .expect("context");
        let start = Instant::now();
        let message = models
            .complete_simple(&model, context, options.into())
            .await;
        let at = start.elapsed().as_millis();
        if stalled_idle_ms(&message).is_some() {
            format!("i stalled {at}")
        } else {
            assert_eq!(message.stop_reason, StopReason::Stop, "{message:?}");
            "i done".to_owned()
        }
    })
}

fn idle_case(rng: &mut Rng, events: &mut String, transcript: &mut String) {
    let deadline = rng.range(1, 50);
    let gaps: Vec<u64> = (0..rng.range(0, 6))
        .map(|_| match rng.range(0, 2 * deadline) {
            gap if gap == deadline => gap + 1,
            gap => gap,
        })
        .collect();
    let mut line = format!("i {deadline}");
    for gap in &gaps {
        write!(line, " {gap}").unwrap();
    }
    writeln!(events, "{line}").unwrap();
    writeln!(transcript, "{}", idle_line(deadline, &gaps)).unwrap();
}

#[test]
fn the_rust_idle_deadline_equals_the_bend_model() {
    let scenarios = (1..=30).map(|seed| {
        let mut rng = Rng(seed);
        let mut events = String::new();
        let mut transcript = String::new();
        for _ in 0..12 {
            idle_case(&mut rng, &mut events, &mut transcript);
        }
        Scenario {
            name: seed.to_string(),
            events,
            transcript,
        }
    });
    compare("bend/bridge_retry.bend", scenarios);
}
