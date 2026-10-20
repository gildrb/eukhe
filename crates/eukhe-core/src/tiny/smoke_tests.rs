//! The roles on real models: a session title (role `tiny`) and a typed
//! judgment through `Models::classify` (role `judge`, the `local`
//! provider). Runs only with `EUKHE_TINY_SMOKE_AGENT_DIR` (an agent dir
//! where `eukhe tiny-models download lfm2.5-230m` installed the model) and
//! `EUKHE_TINY_SMOKE_WORKER` (the `eukhe` binary that serves the worker);
//! the worker loads ONNX Runtime from `ORT_DYLIB_PATH`. Otherwise it prints
//! why it skips: a normal test run has neither the model nor the runtime.

use std::path::PathBuf;

use eukhe_ai::models::ModelsClassifierOptions;
use eukhe_types::pi_ai::{ClassifierContext, ClassifierStopReason};
use serde_json::json;

use super::judge::classifier_model;
use super::title::{generate_title, TitleOutcome, TitleRequest};
use super::*;
use crate::settings::cvar::{registry, Set, Sets};

/// The agent dir and the worker binary, or why the test skips.
fn smoke_env() -> Result<(PathBuf, PathBuf), String> {
    let var = |name: &str| {
        std::env::var_os(name)
            .filter(|value| !value.is_empty())
            .map(PathBuf::from)
            .ok_or_else(|| format!("{name} is not set"))
    };
    Ok((
        var("EUKHE_TINY_SMOKE_AGENT_DIR")?,
        var("EUKHE_TINY_SMOKE_WORKER")?,
    ))
}

#[tokio::test]
async fn a_local_model_titles_a_session_and_judges() {
    let (agent_dir, worker) = match smoke_env() {
        Ok(env) => env,
        Err(reason) => {
            eprintln!("SKIPPED: {reason}");
            return;
        }
    };
    let cvars = Cvars::new(
        registry(),
        Sets(
            [
                ("modelRoles.tiny", json!("local/lfm2.5-230m")),
                ("retry.fallbackChains.tiny", json!([])),
                ("modelRoles.judge", json!("local/lfm2.5-230m")),
                ("retry.fallbackChains.judge", json!([])),
            ]
            .into_iter()
            .map(|(id, value)| Set {
                id: id.to_owned(),
                value,
            })
            .collect(),
        ),
    );
    let home = TinyHome::under(&agent_dir);
    let models = crate::durable::create_models(&agent_dir).models;
    let client = client(&agent_dir, &cvars, worker);

    let title = generate_title(TitleRequest {
        first_message: "How do I resize a btrfs partition on an encrypted LUKS volume?",
        cvars: &cvars,
        home: &home,
        client: &client,
        models: &models,
        session_model: None,
    })
    .await
    .unwrap();
    eprintln!("title: {title:?}");
    assert!(matches!(title, TitleOutcome::Titled(_)), "{title:?}");

    // The title started the worker; the judgment joins it (same tag).
    let judge = match resolve(Role::Judge, &role_settings(&cvars, Role::Judge), &home, "") {
        Pick::Use(candidate) => candidate,
        Pick::Unavailable => panic!("the judge role has no installed model"),
    };
    let local = judge.local_model().unwrap();
    let context: ClassifierContext = serde_json::from_value(json!({
        "state": { "message": "The app crashes with a null pointer exception when I click Save." },
        "questions": {
            "kind": {
                "type": "choice",
                "instructions": "What kind of message is this?",
                "criteria": {
                    "bug": "a report of a defect",
                    "praise": "a compliment",
                    "question": "a question about usage"
                }
            }
        }
    }))
    .unwrap();
    let result = models
        .classify(
            &classifier_model(local),
            &context,
            ModelsClassifierOptions::default(),
        )
        .await;
    eprintln!(
        "judgment: {:?} {:?} {:?}",
        result.stop_reason, result.answers, result.error_message
    );
    assert_eq!(
        (result.stop_reason, result.error_message),
        (ClassifierStopReason::Stop, None)
    );
}
