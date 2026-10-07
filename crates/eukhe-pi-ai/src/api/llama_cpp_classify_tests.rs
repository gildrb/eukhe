//! Port of `test/llama-cpp-classify.test.ts`.

use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::{Arc, Mutex, PoisonError};

use eukhe_chord::context::AbortController;
use eukhe_types::pi_ai::{
    ClassifierAnswer, ClassifierContext, ClassifierModel, ClassifierQuestion, ClassifierStopReason,
    IndexMap, JsonValue,
};
use futures::FutureExt;
use serde_json::json;

use super::{
    answer_from_probabilities, classify, label_probabilities, llama_server_root, peak_confidence,
    render_question,
};
use crate::api::system_one_shared::test_fetch::{
    json_response, mock_fetch, recorded, response, Recorded, Requests,
};
use crate::types::{
    ClassifierOptions, FetchFunction, OnPayload, OnResponse, ProviderRequestOptions,
};

static SERVER_COUNT: AtomicUsize = AtomicUsize::new(0);

/// A fresh server URL per test: label tokens are cached per server and model.
fn model() -> ClassifierModel {
    let server = SERVER_COUNT.fetch_add(1, Ordering::SeqCst) + 1;
    serde_json::from_value(json!({
        "type": "classifier",
        "id": "qwen",
        "name": "qwen",
        "api": "llama-cpp-classify",
        "provider": "llama.cpp",
        "baseUrl": format!("http://llama-{server}.test:8080/v1"),
        "input": ["text"],
        "cost": { "input": 0, "output": 0, "cacheRead": 0, "cacheWrite": 0 },
        "contextWindow": 32768,
    }))
    .expect("model")
}

type Next = Box<dyn Fn(&str, f64) -> Vec<(String, f64)> + Send + Sync>;
type Template = Box<dyn Fn(&[JsonValue]) -> String + Send + Sync>;
type Tokenize = Box<dyn Fn(&str) -> Vec<u32> + Send + Sync>;

#[derive(Default)]
struct FakeServerOptions {
    /// Log-probabilities of the next token by token text, in rank order.
    next: Option<Next>,
    template: Option<Template>,
    tokenize: Option<Tokenize>,
}

/// Token IDs: one per character, the character code.
fn char_tokens(content: &str) -> Vec<u32> {
    content.chars().map(u32::from).collect()
}

fn logprobs(entries: &[(&str, f64)]) -> Vec<(String, f64)> {
    entries
        .iter()
        .map(|(token, logprob)| ((*token).to_owned(), *logprob))
        .collect()
}

fn path_of(url: &str) -> String {
    url::Url::parse(url).expect("url").path().to_owned()
}

fn fake_server(options: FakeServerOptions) -> (FetchFunction, Requests) {
    mock_fetch(move |request: &Recorded| {
        let body = request.json();
        match path_of(&request.url).as_str() {
            "/tokenize" => {
                let content = body["content"].as_str().unwrap_or_default();
                let tokens = options
                    .tokenize
                    .as_ref()
                    .map_or_else(|| char_tokens(content), |tokenize| tokenize(content));
                json_response(200, &json!({ "tokens": tokens }))
            }
            "/apply-template" => {
                let messages = body["messages"].as_array().cloned().unwrap_or_default();
                let prompt = options.template.as_ref().map_or_else(
                    || {
                        let mut rendered = String::new();
                        for message in &messages {
                            rendered.push_str("<|");
                            rendered.push_str(message["role"].as_str().unwrap_or_default());
                            rendered.push_str("|>\n");
                            rendered.push_str(message["content"].as_str().unwrap_or_default());
                            rendered.push('\n');
                        }
                        format!("{rendered}<|assistant|>\n")
                    },
                    |template| template(&messages),
                );
                json_response(200, &json!({ "prompt": prompt }))
            }
            "/completion" => {
                let prompt = body["prompt"].as_str().unwrap_or_default();
                let depth = body["n_probs"].as_f64().unwrap_or(f64::NAN);
                let next = options.next.as_ref().map_or_else(
                    || logprobs(&[("A", -0.1), ("B", -2.5)]),
                    |next| next(prompt, depth),
                );
                let top_logprobs: Vec<JsonValue> = next
                    .iter()
                    .map(|(token, logprob)| {
                        json!({
                            "id": token.chars().next().map(u32::from),
                            "token": token,
                            "bytes": [],
                            "logprob": logprob,
                        })
                    })
                    .collect();
                json_response(
                    200,
                    &json!({
                        "content": "A",
                        "completion_probabilities": [{ "id": 65, "token": "A", "top_logprobs": top_logprobs }],
                    }),
                )
            }
            _ => response(404, &[], "not found".to_owned()),
        }
    })
}

/// Completion log-probabilities for bool (Yes/No) and letter labels; the
/// fake tokenizer maps a label to its first character.
fn answer_by_prompt(prompt: &str, _depth: f64) -> Vec<(String, f64)> {
    if prompt.contains("Answer Yes or No.") {
        return logprobs(&[("Y", -0.05), ("N", -3.0)]);
    }
    if prompt.contains("Answer with one level number.") {
        return logprobs(&[("2", -0.2), ("1", -1.8), ("0", -4.0)]);
    }
    logprobs(&[("B", -0.3), ("A", -1.5), ("C", -3.0)])
}

fn context() -> ClassifierContext {
    serde_json::from_value(json!({
        "state": { "message": "Help! My payouts have been failing for 3 days." },
        "questions": {
            "team": {
                "type": "choice",
                "instructions": "Which team should handle this?",
                "criteria": { "billing": "Payments and refunds", "technical": "Bugs and outages", "sales": "" },
            },
            "urgent": {
                "type": "bool",
                "instructions": "Does this convey urgency?",
                "criteria": { "true": "The user needs help soon", "false": "No time pressure" },
            },
            "severity": { "type": "score", "instructions": "How severe is this?", "criteria": ["low", "medium", "high"] },
        },
    }))
    .expect("context")
}

fn pick_context(instructions: &str) -> ClassifierContext {
    serde_json::from_value(json!({
        "state": {},
        "questions": { "pick": { "type": "choice", "instructions": instructions, "criteria": { "a": "", "b": "" } } },
    }))
    .expect("context")
}

/// Maps multi-character labels to single tokens, as a real vocabulary would.
fn word_tokens(content: &str) -> Vec<u32> {
    let mut tokens = Vec::new();
    let mut part = String::new();
    let flush = |part: &mut String, tokens: &mut Vec<u32>| {
        match part.as_str() {
            "" => {}
            "Yes" => tokens.push(89),
            "No" => tokens.push(78),
            other => tokens.extend(char_tokens(other)),
        }
        part.clear();
    };
    for c in content.chars() {
        if c == '\n' {
            flush(&mut part, &mut tokens);
            tokens.push(u32::from('\n'));
        } else {
            part.push(c);
        }
    }
    flush(&mut part, &mut tokens);
    tokens
}

fn options(fetch: FetchFunction) -> ClassifierOptions {
    ClassifierOptions {
        request: ProviderRequestOptions {
            fetch: Some(fetch),
            ..ProviderRequestOptions::default()
        },
        temperature: None,
    }
}

fn completion_depths(requests: &[Recorded]) -> Vec<f64> {
    requests
        .iter()
        .filter(|request| request.url.ends_with("/completion"))
        .map(|request| request.json()["n_probs"].as_f64().unwrap_or(f64::NAN))
        .collect()
}

#[tokio::test]
async fn answers_choice_bool_and_score_questions_from_label_log_probabilities() {
    let (fetch, requests) = fake_server(FakeServerOptions {
        next: Some(Box::new(answer_by_prompt)),
        tokenize: Some(Box::new(word_tokens)),
        ..FakeServerOptions::default()
    });
    let classifier_model = model();
    let mut opts = options(fetch);
    opts.request.api_key = Some("local".to_owned());

    let result = classify(classifier_model.clone(), context(), opts).await;

    assert_eq!(result.error_message, None);
    assert_eq!(result.stop_reason, ClassifierStopReason::Stop);
    let choice = label_probabilities(&[-1.5, -0.3, -3.0], 1.0);
    assert_eq!(
        result.answers["team"],
        ClassifierAnswer::Choice {
            choice: "technical".to_owned(),
            probabilities: [
                ("billing".to_owned(), choice[0]),
                ("technical".to_owned(), choice[1]),
                ("sales".to_owned(), choice[2]),
            ]
            .into_iter()
            .collect(),
            confidence: peak_confidence(&choice),
        }
    );
    assert_eq!(
        result.answers["urgent"],
        ClassifierAnswer::Bool {
            probability: label_probabilities(&[-0.05, -3.0], 1.0)[0]
        }
    );
    let levels = label_probabilities(&[-4.0, -1.8, -0.2], 1.0);
    assert_eq!(
        result.answers["severity"],
        ClassifierAnswer::Score {
            score: levels[1] + 2.0 * levels[2],
            confidence: peak_confidence(&levels),
        }
    );

    let root = classifier_model.base_url.trim_end_matches("/v1").to_owned();
    let requests = recorded(&requests);
    for request in &requests {
        assert!(request.url.starts_with(&format!("{root}/")));
        assert_eq!(request.json()["model"], "qwen");
        assert_eq!(request.header("authorization"), Some("Bearer local"));
    }
    let completion = requests
        .iter()
        .find(|request| request.url.ends_with("/completion"))
        .expect("completion")
        .json();
    assert_eq!(completion["n_predict"], 1);
    assert_eq!(completion["n_probs"], 256);
    assert_eq!(completion["post_sampling_probs"], false);
    assert_eq!(completion["cache_prompt"], true);
    let template = requests
        .iter()
        .find(|request| request.url.ends_with("/apply-template"))
        .expect("template")
        .json();
    assert_eq!(
        template["chat_template_kwargs"],
        json!({ "enable_thinking": false })
    );
}

#[test]
fn repeats_the_state_around_all_questions_and_ends_with_this_questions_labels() {
    let rendered = render_question(&context(), "team").expect("rendered");
    let state = "State:\n{\n \"message\": \"Help! My payouts have been failing for 3 days.\"\n}";
    assert_eq!(rendered.labels, ["A", "B", "C"]);
    assert_eq!(rendered.keys, ["billing", "technical", "sales"]);
    assert_eq!(
        rendered.content,
        [
            state,
            "",
            "Task: answer each of the following questions about the state.",
            "",
            "Question: Which team should handle this?",
            "",
            "Options:",
            "- billing: Payments and refunds",
            "- technical: Bugs and outages",
            "- sales",
            "",
            "Question: Does this convey urgency?",
            "",
            "Yes means: The user needs help soon",
            "No means: No time pressure",
            "",
            "Question: How severe is this?",
            "",
            "Levels:",
            "0. low",
            "1. medium",
            "2. high",
            "",
            state,
            "",
            "Question: Which team should handle this?",
            "",
            "Options:",
            "A. billing: Payments and refunds",
            "B. technical: Bugs and outages",
            "C. sales",
            "",
            "Answer with one letter.",
        ]
        .join("\n")
    );
}

#[test]
fn shares_everything_before_the_final_question_across_the_questions_of_a_request() {
    let prefix = |id: &str| {
        let content = render_question(&context(), id).expect("rendered").content;
        let end = content.rfind("Question:").expect("question");
        content[..end].to_owned()
    };
    assert_eq!(prefix("urgent"), prefix("team"));
    assert_eq!(prefix("severity"), prefix("team"));
    assert!(render_question(&context(), "urgent")
        .expect("rendered")
        .content
        .ends_with("No means: No time pressure\n\nAnswer Yes or No."));
    assert!(render_question(&context(), "severity")
        .expect("rendered")
        .content
        .ends_with("2. high\n\nAnswer with one level number."));
}

#[tokio::test]
async fn divides_label_log_probabilities_by_the_temperature() {
    let (fetch, _) = fake_server(FakeServerOptions {
        next: Some(Box::new(|_, _| logprobs(&[("A", -0.1), ("B", -2.5)]))),
        ..FakeServerOptions::default()
    });
    let mut opts = options(fetch);
    opts.temperature = Some(2.0);

    let result = classify(model(), pick_context("Pick one"), opts).await;

    let expected = label_probabilities(&[-0.1 / 2.0, -2.5 / 2.0], 1.0);
    let ClassifierAnswer::Choice { probabilities, .. } = &result.answers["pick"] else {
        panic!("expected a choice answer: {result:?}");
    };
    let expected_map: IndexMap<String, f64> =
        [("a".to_owned(), expected[0]), ("b".to_owned(), expected[1])]
            .into_iter()
            .collect();
    assert_eq!(probabilities, &expected_map);
    assert_eq!(label_probabilities(&[-0.1, -2.5], 2.0), expected);
}

#[tokio::test]
async fn rejects_non_positive_temperatures_before_sending_requests() {
    let (fetch, requests) = fake_server(FakeServerOptions::default());
    let mut opts = options(fetch);
    opts.temperature = Some(0.0);
    let result = classify(model(), context(), opts).await;

    assert_eq!(result.stop_reason, ClassifierStopReason::Error);
    assert!(result
        .error_message
        .expect("message")
        .contains("Temperature must be a positive number, got 0"));
    assert!(recorded(&requests).is_empty());
}

#[tokio::test]
async fn retries_deeper_readouts_when_a_label_is_missing_and_fails_without_inventing_zeros() {
    let (deep, deep_requests) = fake_server(FakeServerOptions {
        next: Some(Box::new(|_, depth| {
            if depth < 4096.0 {
                logprobs(&[("A", -0.1)])
            } else {
                logprobs(&[("A", -0.1), ("B", -9.0)])
            }
        })),
        ..FakeServerOptions::default()
    });
    let recovered = classify(model(), pick_context("Pick one"), options(deep)).await;
    assert_eq!(recovered.stop_reason, ClassifierStopReason::Stop);
    assert_eq!(
        completion_depths(&recorded(&deep_requests)),
        [256.0, 4096.0]
    );

    let (never, never_requests) = fake_server(FakeServerOptions {
        next: Some(Box::new(|_, _| logprobs(&[("A", -0.1)]))),
        ..FakeServerOptions::default()
    });
    let failed = classify(model(), pick_context("Pick one"), options(never)).await;
    assert_eq!(failed.stop_reason, ClassifierStopReason::Error);
    assert!(failed.answers.is_empty());
    assert!(failed
        .error_message
        .expect("message")
        .contains("did not rank labels B for pick within the top 32768 tokens"));
    assert_eq!(
        completion_depths(&recorded(&never_requests)),
        [256.0, 4096.0, 32768.0]
    );
}

#[tokio::test]
async fn closes_a_reasoning_block_the_template_leaves_open() {
    let (fetch, requests) = fake_server(FakeServerOptions {
        template: Some(Box::new(|_| "<|assistant|>\n<think>".to_owned())),
        ..FakeServerOptions::default()
    });
    classify(model(), pick_context("Pick"), options(fetch)).await;

    let completion = recorded(&requests)
        .into_iter()
        .find(|request| request.url.ends_with("/completion"))
        .expect("completion")
        .json();
    assert_eq!(completion["prompt"], "<|assistant|>\n<think></think>");
}

#[tokio::test]
async fn reads_labels_in_reply_position_and_rejects_labels_that_are_not_one_token() {
    // A tokenizer that merges a newline with a following letter falls back to the label alone.
    let (merging, _) = fake_server(FakeServerOptions {
        tokenize: Some(Box::new(|content| {
            if content.starts_with('\n') && content.chars().count() > 1 {
                vec![1000]
            } else {
                char_tokens(content)
            }
        })),
        ..FakeServerOptions::default()
    });
    let merged = classify(model(), pick_context("Pick"), options(merging)).await;
    assert_eq!(merged.stop_reason, ClassifierStopReason::Stop);

    // The default fake tokenizer splits "Yes" into three tokens.
    let (split, _) = fake_server(FakeServerOptions::default());
    let bool_context: ClassifierContext = serde_json::from_value(json!({
        "state": {},
        "questions": { "ok": { "type": "bool", "instructions": "OK?", "criteria": { "true": "", "false": "" } } },
    }))
    .expect("context");
    let result = classify(model(), bool_context, options(split)).await;
    assert_eq!(result.stop_reason, ClassifierStopReason::Error);
    assert!(result
        .error_message
        .expect("message")
        .contains("Label \"Yes\" is not a single token for qwen"));
}

#[tokio::test]
async fn caches_label_tokens_per_server_and_model() {
    let classifier_model = model();
    let (fetch, requests) = fake_server(FakeServerOptions::default());
    let tokenizations = |requests: &Requests| {
        recorded(requests)
            .iter()
            .filter(|request| request.url.ends_with("/tokenize"))
            .count()
    };
    classify(
        classifier_model.clone(),
        pick_context("Pick"),
        options(Arc::clone(&fetch)),
    )
    .await;
    let first_tokenizations = tokenizations(&requests);
    classify(classifier_model, pick_context("Pick"), options(fetch)).await;

    assert!(first_tokenizations > 0);
    assert_eq!(tokenizations(&requests), first_tokenizations);
}

#[tokio::test]
async fn validates_option_counts_before_sending_requests() {
    let (fetch, requests) = fake_server(FakeServerOptions::default());
    let criteria: serde_json::Map<String, JsonValue> = (0..63)
        .map(|index| (format!("option{index}"), json!("")))
        .collect();
    let too_many_context: ClassifierContext = serde_json::from_value(json!({
        "state": {},
        "questions": { "pick": { "type": "choice", "instructions": "Pick", "criteria": criteria } },
    }))
    .expect("context");
    let too_few_context: ClassifierContext = serde_json::from_value(json!({
        "state": {},
        "questions": { "rate": { "type": "score", "instructions": "Rate", "criteria": ["only"] } },
    }))
    .expect("context");
    let too_many = classify(model(), too_many_context, options(Arc::clone(&fetch))).await;
    let too_few = classify(model(), too_few_context, options(fetch)).await;

    assert!(too_many
        .error_message
        .expect("message")
        .contains("A choice question needs 2 to 62 options, got 63"));
    assert!(too_few
        .error_message
        .expect("message")
        .contains("A score question needs 2 to 10 levels, got 1"));
    assert!(recorded(&requests).is_empty());
}

#[tokio::test]
async fn passes_completion_payloads_and_responses_through_the_request_hooks() {
    let (fetch, requests) = fake_server(FakeServerOptions::default());
    let payloads: Arc<Mutex<Vec<JsonValue>>> = Arc::default();
    let statuses: Arc<Mutex<Vec<u16>>> = Arc::default();
    let payload_sink = Arc::clone(&payloads);
    let status_sink = Arc::clone(&statuses);
    let on_payload: OnPayload<ClassifierModel> = Arc::new(move |payload, _model| {
        payload_sink
            .lock()
            .unwrap_or_else(PoisonError::into_inner)
            .push(payload.clone());
        let mut next = payload;
        if let Some(object) = next.as_object_mut() {
            object.insert("id_slot".to_owned(), json!(1));
        }
        async move { Ok(Some(next)) }.boxed()
    });
    let on_response: OnResponse<ClassifierModel> = Arc::new(move |response, _model| {
        status_sink
            .lock()
            .unwrap_or_else(PoisonError::into_inner)
            .push(response.status);
        async { Ok(()) }.boxed()
    });
    let mut opts = options(fetch);
    opts.request.on_payload = Some(on_payload);
    opts.request.on_response = Some(on_response);

    classify(model(), pick_context("Pick"), opts).await;

    let payloads = payloads.lock().unwrap_or_else(PoisonError::into_inner);
    assert_eq!(payloads.len(), 1);
    assert_eq!(payloads[0]["n_predict"], 1);
    assert_eq!(
        *statuses.lock().unwrap_or_else(PoisonError::into_inner),
        [200]
    );
    let completion = recorded(&requests)
        .into_iter()
        .find(|request| request.url.ends_with("/completion"))
        .expect("completion")
        .json();
    assert_eq!(completion["id_slot"], 1);
}

#[tokio::test]
async fn reports_server_errors_and_cancellation() {
    let (fetch, _) = mock_fetch(|_| {
        response(
            400,
            &[],
            r#"{"error":{"message":"context overflow"}}"#.to_owned(),
        )
    });
    let mut failing_options = options(fetch);
    failing_options.request.max_retries = Some(0);
    let failing = classify(model(), context(), failing_options).await;
    assert_eq!(failing.stop_reason, ClassifierStopReason::Error);
    let message = failing.error_message.expect("message");
    assert!(message.contains("llama.cpp error (400)"), "{message}");
    assert!(message.contains("context overflow"), "{message}");

    let controller = AbortController::new();
    controller.abort(None);
    let (fetch, _) = mock_fetch(|_| json_response(200, &json!({})));
    let mut aborted_options = options(fetch);
    aborted_options.request.signal = Some(controller.signal());
    let aborted = classify(model(), context(), aborted_options).await;
    assert_eq!(aborted.stop_reason, ClassifierStopReason::Aborted);
}

#[tokio::test]
async fn rejects_models_for_other_classifier_apis() {
    let (fetch, requests) = fake_server(FakeServerOptions::default());
    let mut other = model();
    other.api = "typesafe-system-one".to_owned();
    let result = classify(other, context(), options(fetch)).await;

    assert!(result
        .error_message
        .expect("message")
        .contains("Unsupported classifier API: typesafe-system-one"));
    assert!(recorded(&requests).is_empty());
}

#[test]
fn derives_the_server_root_from_openai_compatible_base_urls() {
    assert_eq!(
        llama_server_root("http://127.0.0.1:8080/v1/"),
        "http://127.0.0.1:8080"
    );
    assert_eq!(
        llama_server_root("https://example.com/prefix/v1"),
        "https://example.com/prefix"
    );
    assert_eq!(
        llama_server_root("http://127.0.0.1:8080"),
        "http://127.0.0.1:8080"
    );
}

#[test]
fn computes_typesafes_confidence_and_expected_scores() {
    assert!((peak_confidence(&[0.89, 0.06, 0.05]) - 0.835).abs() < 5e-3);
    assert!(peak_confidence(&[0.5, 0.5]).abs() < f64::EPSILON);
    assert!((peak_confidence(&[1.0, 0.0, 0.0]) - 1.0).abs() < f64::EPSILON);
    let question = ClassifierQuestion::Score {
        instructions: String::new(),
        criteria: vec!["a".to_owned(), "b".to_owned(), "c".to_owned()],
    };
    assert_eq!(
        answer_from_probabilities(
            &question,
            &["0".to_owned(), "1".to_owned(), "2".to_owned()],
            &[0.2, 0.3, 0.5]
        ),
        ClassifierAnswer::Score {
            score: 1.3,
            confidence: peak_confidence(&[0.2, 0.3, 0.5])
        }
    );
}
