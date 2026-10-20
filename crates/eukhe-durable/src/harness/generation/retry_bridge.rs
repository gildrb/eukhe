//! The bridge between the deferred job's, the stall's and the idle
//! deadline's decisions and their Bend model (`bend/retry.bend` §4, §5 and
//! §6, whose laws `laws/retry.bend` states and `PROOF.bend` proves): both
//! run the same scenarios and must print the same transcript, byte for
//! byte. `bend/bridge_retry.bend` documents the scenario format (its `d`,
//! `s` and `i` lines).
//!
//! A `d` case is the replies to one request, from its first: each act is
//! what `classify` decides with the real decisions. A request's reply and
//! a poll's reply that is still deferred go through [`after_reply`] (its
//! time check of the job's deadline); a failed poll goes through
//! [`PollFailure::next`], and a poll again through [`after_reply`]. The
//! clock is the model's: a request's reply comes 0 ms after it was sent,
//! and the next reply of a job comes `gap + 1` ms after the one before.
//! After a send, a cancel, a quit or a settle, the next reply is the reply
//! of a new request. An `s` case is [`idle_after_stall`].
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
use std::num::NonZeroU32;
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

use super::decide::{after_reply, Counts, Failure, Limits, Reply, Step, MAX_NOTES};
use super::deferred::{idle_after_stall, FailedPoll, PollFailure};
use crate::testing::bridge::{compare, Rng, Scenario};

/// What a call that is out answers, as the model reads it.
#[derive(Clone, Copy)]
enum Got {
    /// The end of the turn.
    Answer,
    /// Still deferred; the next reply `gap + 1` ms later.
    Later { gap: u64 },
    /// A failure (retryable or not); the next reply `gap + 1` ms later.
    Broke { retryable: bool, gap: u64 },
}

/// The request's deferred job, as `classify` reads its poll.
#[derive(Clone, Copy)]
struct Job {
    /// The ms since the request was sent, at the job's next reply.
    waited: u64,
    /// The fetches of the job that failed in a row.
    failures: u32,
}

/// The acts of one request's replies. `fails` is `retry.maxRetries`, the
/// fetch failures a job may have in a row; `budget` the ms its job may
/// run. The request's own failures are below the retry budget: the model
/// counts no request retries (`bend/run.bend` does).
fn acts(fails: u32, budget: u64, gots: &[Got]) -> String {
    let limits = Limits {
        max_rounds: NonZeroU32::MIN,
        max_wait: budget,
        max_retries: u32::MAX,
        max_notes: MAX_NOTES,
    };
    let at = |waited| Counts {
        attempt: 1,
        notes: 0,
        waited,
        compacted: false,
    };
    let mut job: Option<Job> = None;
    let mut out = String::new();
    for got in gots {
        let (act, next) = match (job, *got) {
            (None | Some(_), Got::Answer) => match after_reply(at(0), Reply::<()>::Text, &limits) {
                Step::Answer => ("settle", None),
                step @ (Step::Tools
                | Step::Poll(())
                | Step::Retry
                | Step::Note
                | Step::Compact
                | Step::Fail(Failure::Model | Failure::Polls)) => {
                    panic!("a text reply makes {step:?}")
                }
            },
            (None, Got::Later { gap }) => {
                poll(after_reply(at(0), Reply::Deferred(()), &limits), 0, 0, gap)
            }
            (None, Got::Broke { retryable, gap: _ }) => {
                let reply = Reply::<()>::Error {
                    retryable,
                    noted: false,
                };
                match after_reply(at(0), reply, &limits) {
                    Step::Retry => ("send", None),
                    Step::Fail(Failure::Model) => ("quit", None),
                    step @ (Step::Answer
                    | Step::Tools
                    | Step::Poll(())
                    | Step::Note
                    | Step::Compact
                    | Step::Fail(Failure::Polls)) => {
                        panic!("a request's failure makes {step:?}")
                    }
                }
            }
            (Some(Job { waited, .. }), Got::Later { gap }) => poll(
                after_reply(at(waited), Reply::Deferred(()), &limits),
                waited,
                0,
                gap,
            ),
            (Some(Job { waited, failures }), Got::Broke { retryable, gap }) => {
                let failure = PollFailure {
                    retryable,
                    failures,
                };
                match failure.next(fails) {
                    FailedPoll::Repoll => poll(
                        after_reply(at(waited), Reply::Deferred(()), &limits),
                        waited,
                        failures + 1,
                        gap,
                    ),
                    FailedPoll::Cancel => ("cancel", None),
                }
            }
        };
        job = next;
        let _ = write!(out, " {act}");
    }
    out
}

/// The act of a job's deferred reply `waited` ms after its request: a
/// poll whose reply comes `gap + 1` ms later with `failures` in a row, or
/// a cancel at the deadline.
fn poll(step: Step<()>, waited: u64, failures: u32, gap: u64) -> (&'static str, Option<Job>) {
    match step {
        Step::Poll(()) => (
            "poll",
            Some(Job {
                waited: waited + 1 + gap,
                failures,
            }),
        ),
        Step::Fail(Failure::Polls) => ("cancel", None),
        step @ (Step::Answer
        | Step::Tools
        | Step::Retry
        | Step::Note
        | Step::Compact
        | Step::Fail(Failure::Model)) => panic!("a deferred reply makes {step:?}"),
    }
}

fn deferred_case(rng: &mut Rng, events: &mut String, transcript: &mut String) {
    let fails = u32::try_from(rng.range(0, 3)).unwrap();
    let budget = rng.range(0, 40);
    let gots: Vec<Got> = (0..rng.range(1, 12))
        .map(|_| match rng.below(10) {
            0 => Got::Answer,
            1..=5 => Got::Later {
                gap: rng.range(0, 9),
            },
            _ => Got::Broke {
                retryable: rng.chance(70),
                gap: rng.range(0, 9),
            },
        })
        .collect();
    let shown: String = gots
        .iter()
        .map(|got| match got {
            Got::Answer => " a".to_owned(),
            Got::Later { gap } => format!(" l{gap}"),
            Got::Broke { retryable, gap } => format!(" b{}:{gap}", u8::from(*retryable)),
        })
        .collect();
    writeln!(events, "d {fails} {budget}{shown}").unwrap();
    writeln!(transcript, "d{}", acts(fails, budget, &gots)).unwrap();
}

fn stall_case(rng: &mut Rng, events: &mut String, transcript: &mut String) {
    let idle = [0, 1, 200, 300_000][usize::try_from(rng.below(4)).unwrap()] + rng.range(0, 1_000);
    writeln!(events, "s {idle}").unwrap();
    writeln!(transcript, "s {}", idle_after_stall(idle)).unwrap();
}

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
fn the_rust_deferred_decisions_equal_the_bend_model() {
    let scenarios = (1..=30).map(|seed| {
        let mut rng = Rng(seed);
        let mut events = String::new();
        let mut transcript = String::new();
        for _ in 0..40 {
            match rng.below(10) {
                0..=6 => deferred_case(&mut rng, &mut events, &mut transcript),
                7 => stall_case(&mut rng, &mut events, &mut transcript),
                _ => idle_case(&mut rng, &mut events, &mut transcript),
            }
        }
        Scenario {
            name: seed.to_string(),
            events,
            transcript,
        }
    });
    compare("bend/bridge_retry.bend", scenarios);
}
