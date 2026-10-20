use std::time::{Duration, Instant};

use eukhe_types::ai::{AssistantMessage, Usage};
use eukhe_types::pi_ai::{PromptProgress, ResponseTiming};

use super::{Prefill, ResponseSpeed, SpeedClock, SpeedPhase, SpeedSample};

fn usage(input: u64, cache_read: u64, cache_write: u64, output: u64) -> Usage {
    Usage {
        input,
        output,
        cache_read,
        cache_write,
        total_tokens: input + cache_read + cache_write + output,
        ..Usage::default()
    }
}

fn timing(first_token_ms: u64, last_token_ms: u64) -> ResponseTiming {
    ResponseTiming {
        first_byte_ms: Some(first_token_ms / 2),
        first_token_ms: Some(first_token_ms),
        last_token_ms: Some(last_token_ms),
    }
}

fn message(stop_reason: &str, usage: Usage, timing: Option<ResponseTiming>) -> AssistantMessage {
    let mut message: AssistantMessage = serde_json::from_value(serde_json::json!({
        "content": [{ "type": "text", "text": "ok" }],
        "api": "openai-completions",
        "provider": "llama-cpp",
        "model": "m",
        "usage": {
            "input": 0, "output": 0, "cacheRead": 0, "cacheWrite": 0, "totalTokens": 0,
            "cost": { "input": 0, "output": 0, "cacheRead": 0, "cacheWrite": 0, "total": 0 },
        },
        "stopReason": stop_reason,
        "timestamp": 1,
    }))
    .unwrap();
    message.usage = usage;
    message.timing = timing;
    message
}

#[test]
fn a_sample_takes_the_uncached_prompt_and_the_stream_marks() {
    assert_eq!(
        SpeedSample::of(&usage(900, 3000, 100, 51), &timing(500, 1500)),
        Some(SpeedSample {
            uncached: 1000,
            cache_read: 3000,
            output: 51,
            ttft: Duration::from_millis(500),
            decode: Duration::from_millis(1000),
        })
    );
    let no_token = ResponseTiming {
        first_byte_ms: Some(20),
        first_token_ms: None,
        last_token_ms: None,
    };
    assert_eq!(SpeedSample::of(&usage(10, 0, 0, 0), &no_token), None);
}

#[test]
fn prefill_rate_is_uncached_prompt_over_ttft_and_decode_skips_the_first_token() {
    let speed = ResponseSpeed::of(SpeedSample {
        uncached: 1000,
        cache_read: 3000,
        output: 51,
        ttft: Duration::from_millis(500),
        decode: Duration::from_millis(1000),
    });
    assert_eq!(
        speed,
        ResponseSpeed {
            ttft: Duration::from_millis(500),
            prefill: Prefill::Rate(2000.0),
            decode_tokens_per_second: Some(50.0),
        }
    );
    assert_eq!(
        speed.summary(),
        "prefill 2000 tok/s (TTFT 0.50s) · decode 50.0 tok/s"
    );
}

#[test]
fn a_nearly_all_cached_prompt_reads_cached() {
    let speed = ResponseSpeed::of(SpeedSample {
        uncached: 50,
        cache_read: 9950,
        output: 201,
        ttft: Duration::from_millis(1200),
        decode: Duration::from_millis(2000),
    });
    assert_eq!(
        speed,
        ResponseSpeed {
            ttft: Duration::from_millis(1200),
            prefill: Prefill::Cached,
            decode_tokens_per_second: Some(100.0),
        }
    );
    assert_eq!(
        speed.summary(),
        "prefill cached (TTFT 1.2s) · decode 100 tok/s"
    );
}

#[test]
fn no_prompt_count_and_one_token_leave_only_the_ttft() {
    let speed = ResponseSpeed::of(SpeedSample {
        uncached: 0,
        cache_read: 0,
        output: 1,
        ttft: Duration::from_millis(12_400),
        decode: Duration::ZERO,
    });
    assert_eq!(
        speed,
        ResponseSpeed {
            ttft: Duration::from_millis(12_400),
            prefill: Prefill::Unknown,
            decode_tokens_per_second: None,
        }
    );
    assert_eq!(speed.summary(), "TTFT 12s");
}

#[test]
fn the_clock_runs_prefill_progress_decode_and_the_exact_summary() {
    let start = Instant::now();
    let mut clock = SpeedClock::default();
    clock.request_started(start);
    assert_eq!(
        clock.phase(),
        Some(&SpeedPhase::Prefill {
            since: start,
            progress: None,
            uncached_estimate: None,
        })
    );
    assert_eq!(
        clock
            .phase()
            .unwrap()
            .text(start + Duration::from_millis(3200)),
        "prefill 3.2s"
    );

    let progress = PromptProgress {
        total: 8192,
        cache: 2048,
        processed: 4096,
        time_ms: 900,
    };
    clock.prompt_progress(progress);
    assert_eq!(
        clock.phase().unwrap().text(start),
        "prefill 4096/8192 tokens"
    );

    // A frame without content keeps the prefill.
    clock.streamed(start + Duration::from_millis(100), 0);
    let first_token = start + Duration::from_secs(2);
    clock.streamed(first_token, 3);
    clock.streamed(first_token + Duration::from_millis(500), 21);
    assert_eq!(
        clock.phase(),
        Some(&SpeedPhase::Decode {
            since: start,
            first_token,
            tokens: 21,
        })
    );
    assert_eq!(
        clock
            .phase()
            .unwrap()
            .text(first_token + Duration::from_millis(100)),
        "decode"
    );
    assert_eq!(
        clock
            .phase()
            .unwrap()
            .text(first_token + Duration::from_millis(500)),
        "decode 40.0 tok/s"
    );

    clock.settled(
        &message("stop", usage(6144, 2048, 0, 101), Some(timing(2000, 4000))),
        first_token + Duration::from_secs(3),
    );
    assert_eq!(
        clock.phase(),
        Some(&SpeedPhase::Done(ResponseSpeed {
            ttft: Duration::from_secs(2),
            prefill: Prefill::Rate(3072.0),
            decode_tokens_per_second: Some(50.0),
        }))
    );
}

#[test]
fn without_stream_marks_the_summary_uses_the_client_clock() {
    let start = Instant::now();
    let mut clock = SpeedClock::default();
    clock.request_started(start);
    let first_token = start + Duration::from_millis(400);
    clock.streamed(first_token, 1);
    clock.settled(
        &message("toolUse", usage(800, 0, 0, 41), None),
        first_token + Duration::from_secs(2),
    );
    assert_eq!(
        clock.phase(),
        Some(&SpeedPhase::Done(ResponseSpeed {
            ttft: Duration::from_millis(400),
            prefill: Prefill::Rate(2000.0),
            decode_tokens_per_second: Some(20.0),
        }))
    );
}

#[test]
fn the_next_prefill_estimates_the_uncached_prompt_and_a_failure_shows_nothing() {
    let start = Instant::now();
    let mut clock = SpeedClock::default();
    clock.request_started(start);
    clock.settled(
        &message("toolUse", usage(10, 0, 0, 120), Some(timing(100, 200))),
        start,
    );
    // A tool result of 2,000 characters before the next request, and 400
    // after it starts: 120 output tokens plus ceil(2,400 / 3.5) = 686
    // (chars/4 made 720 in all).
    clock.prompt_added(2000);
    clock.request_started(start);
    clock.prompt_added(400);
    assert_eq!(
        clock.phase(),
        Some(&SpeedPhase::Prefill {
            since: start,
            progress: None,
            uncached_estimate: Some(806),
        })
    );
    assert_eq!(
        clock.phase().unwrap().text(start),
        "prefill 0.0s (~806 tok)"
    );

    clock.settled(&message("error", usage(0, 0, 0, 0), None), start);
    assert_eq!(clock.phase(), None);
}
