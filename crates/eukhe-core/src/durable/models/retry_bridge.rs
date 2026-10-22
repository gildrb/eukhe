//! The bridge between the retry decisions and their Bend model
//! (`bend/retry.bend`, whose laws `LAWS.bend` section `retry` states and
//! `PROOF.bend` proves): the classifier (`FailureFacts::retryable` over
//! real failed messages), the wait (`RetryWait::of`) and the failover walk
//! ([`next_switch`]) run the same scenarios as the model and must print
//! the same transcript, byte for byte. `bend/bridge_retry.bend` documents
//! the scenario format (its `c`, `w` and `f` lines).
//!
//! [`compare`] runs it (and skips without `bend`, unless
//! `EUKHE_REQUIRE_BEND` is set).

use std::fmt::Write as _;

use eukhe_ai::utils::retry::{
    is_retryable_assistant_error, FailureFacts, RetryWait, QUOTA_PARK_DIAGNOSTIC,
};
use eukhe_durable::testing::bridge::{compare, Rng, Scenario};
use eukhe_types::pi_ai::{
    AssistantMessage, AssistantMessageDiagnostic, StopReason, StreamFailureKind, Usage,
};

use super::failover::{next_switch, ProviderFailoverPolicy, Switch, Tried};

/// Failure texts, real and adversarial: the Anthropic image-size 400
/// (whose byte count holds `524`), transport words, limits, the refused
/// server wait, and text that names nothing.
const TEXTS: [&str; 9] = [
    "Provider rejected the request (invalid_request_error, 400): image exceeds 5 MB maximum: 7340032 bytes > 5242880 bytes",
    "invalid timeout parameter",
    "terminated",
    "insufficient_quota: You exceeded your current quota",
    "Server requested 300s retry delay (max: 60s). 429 Too Many Requests",
    "503 Service Unavailable",
    "socket hang up",
    "The model returned an empty answer",
    "Overloaded",
];

const STATUSES: [u16; 11] = [200, 400, 402, 404, 408, 409, 429, 499, 500, 503, 529];

/// "-" for none, else the number.
fn shown(value: Option<u64>) -> String {
    value.map_or_else(|| "-".to_owned(), |value| value.to_string())
}

/// A failed message as a provider leaves it: its text, and a stream
/// failure diagnostic with the recorded status, kind and provider error
/// type; the quota park's diagnostic when `parked`.
fn failed_message(rng: &mut Rng) -> AssistantMessage {
    let text = TEXTS[usize::try_from(rng.below(9)).unwrap()];
    let mut details = serde_json::Map::new();
    if rng.chance(60) {
        let status = STATUSES[usize::try_from(rng.below(11)).unwrap()];
        details.insert("status".to_owned(), status.into());
    }
    if rng.chance(60) {
        let kinds = StreamFailureKind::ALL;
        let count = u64::try_from(kinds.len()).unwrap();
        let kind = kinds[usize::try_from(rng.below(count)).unwrap()];
        details.insert("kind".to_owned(), kind.as_str().into());
    }
    if rng.chance(10) {
        details.insert("providerErrorType".to_owned(), "billing_hard_limit".into());
    }
    let mut diagnostics = vec![AssistantMessageDiagnostic {
        kind: "provider_stream_failure".to_owned(),
        timestamp: 0,
        error: None,
        details: Some(details),
    }];
    if rng.chance(10) {
        diagnostics.push(AssistantMessageDiagnostic {
            kind: QUOTA_PARK_DIAGNOSTIC.to_owned(),
            timestamp: 0,
            error: None,
            details: None,
        });
    }
    AssistantMessage {
        content: Vec::new(),
        api: "faux".to_owned(),
        provider: "faux".to_owned(),
        model: "faux-1".to_owned(),
        response_model: None,
        response_id: None,
        provider_thinking_level: None,
        thinking_level: None,
        diagnostics: Some(diagnostics),
        usage: Usage::default(),
        stop_reason: StopReason::Error,
        deferred: None,
        error_message: Some(text.to_owned()),
        raw_stop_reason: None,
        end_turn: None,
        timestamp: 0,
        duration_ms: None,
        timing: None,
    }
}

fn classify_case(rng: &mut Rng, events: &mut String, transcript: &mut String) {
    let message = failed_message(rng);
    let facts = FailureFacts::of(&message).expect("a failed message has facts");
    let kind = facts.kind.map(|kind| {
        let at = StreamFailureKind::ALL
            .iter()
            .position(|known| *known == kind)
            .expect("every kind is listed");
        u64::try_from(at).unwrap()
    });
    writeln!(
        events,
        "c {} {} {} {} {}",
        u8::from(facts.parked),
        u8::from(facts.limit),
        shown(facts.status.map(u64::from)),
        shown(kind),
        u8::from(facts.transient_text),
    )
    .unwrap();
    writeln!(
        transcript,
        "c {}",
        u8::from(is_retryable_assistant_error(&message))
    )
    .unwrap();
}

fn wait_case(rng: &mut Rng, events: &mut String, transcript: &mut String) {
    let jitter = rng.range(0, 5_000);
    let server = rng.chance(70).then(|| rng.range(0, 120_000));
    let cap: u32 = [0, 1_000, 60_000, 90_000][usize::try_from(rng.below(4)).unwrap()];
    writeln!(events, "w {jitter} {} {cap}", shown(server)).unwrap();
    #[expect(
        clippy::cast_precision_loss,
        reason = "the bridge's numbers are below 2^53"
    )]
    let wait = RetryWait::of(jitter as f64, server.map(|ms| ms as f64), f64::from(cap));
    let line = match wait {
        RetryWait::After(ms) => format!("w after {ms}"),
        RetryWait::Refused { server_ms, cap_ms } => format!("w refused {server_ms} {cap_ms}"),
    };
    writeln!(transcript, "{line}").unwrap();
}

fn failover_case(rng: &mut Rng, events: &mut String, transcript: &mut String) {
    let len = rng.range(1, 5);
    let policy = ProviderFailoverPolicy {
        enabled: true,
        max_switches: u32::try_from(rng.range(0, 8)).unwrap(),
        base_delay_ms: [0, 1, 1_000, 2_500][usize::try_from(rng.below(4)).unwrap()],
        max_delay_ms: [0, 2_000, 30_000][usize::try_from(rng.below(3)).unwrap()],
    };
    let attempts = rng.range(0, 9);
    let tried: Vec<Tried> = (0..attempts)
        .map(|_| Tried {
            at: usize::try_from(rng.below(len)).unwrap(),
            server_wait_ms: rng.chance(40).then(|| rng.range(0, 40_000)),
        })
        .collect();
    let mut shown_tried = String::new();
    for attempt in &tried {
        write!(
            shown_tried,
            " {}:{}",
            attempt.at,
            shown(attempt.server_wait_ms)
        )
        .unwrap();
    }
    writeln!(
        events,
        "f {len} {} {} {}{shown_tried}",
        policy.max_switches, policy.base_delay_ms, policy.max_delay_ms
    )
    .unwrap();
    let line = match next_switch(usize::try_from(len).unwrap(), &tried, &policy) {
        None => "f none".to_owned(),
        Some(Switch { to, delay_ms }) => format!("f {to} {delay_ms}"),
    };
    writeln!(transcript, "{line}").unwrap();
}

#[test]
fn the_rust_retry_decisions_equal_the_bend_model() {
    let scenarios = (1..=30).map(|seed| {
        let mut rng = Rng(seed);
        let mut events = String::new();
        let mut transcript = String::new();
        for _ in 0..60 {
            match rng.below(3) {
                0 => classify_case(&mut rng, &mut events, &mut transcript),
                1 => wait_case(&mut rng, &mut events, &mut transcript),
                _ => failover_case(&mut rng, &mut events, &mut transcript),
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
