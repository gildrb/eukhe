use serde_json::json;

use super::*;
use crate::settings::cvar::{registry, Set, Sets};

const SESSION: &str = "anthropic/claude-sonnet";

fn cvars(sets: &[(&str, Value)]) -> Cvars {
    Cvars::new(
        registry(),
        Sets(
            sets.iter()
                .map(|(id, value)| Set {
                    id: (*id).to_owned(),
                    value: value.clone(),
                })
                .collect(),
        ),
    )
}

fn settings(primary: &str, fallback: FallbackChain) -> RoleSettings {
    RoleSettings {
        primary: primary.to_owned(),
        fallback,
    }
}

fn local(id: &str) -> Candidate {
    Candidate::Local(id.to_owned())
}

#[test]
fn role_settings_read_the_cvars() {
    let configured = cvars(&[
        ("modelRoles.tiny", json!("local/lfm2.5-230m")),
        ("retry.fallbackChains.tiny", json!([])),
        (
            "retry.fallbackChains.judge",
            json!(["local/lfm2.5-350m", " ", SESSION]),
        ),
        ("retry.fallbackChains.translate", json!("not a list")),
    ]);
    assert_eq!(
        Role::ALL.map(|role| role_settings(&configured, role)),
        [
            settings("local/lfm2.5-230m", FallbackChain::Explicit(Vec::new())),
            settings(
                "",
                FallbackChain::Explicit(vec!["local/lfm2.5-350m".to_owned(), SESSION.to_owned()])
            ),
            settings("", FallbackChain::Unset),
            settings("", FallbackChain::Unset),
            settings("", FallbackChain::Unset),
        ]
    );
}

#[test]
fn engine_options_and_switches_read_the_cvars() {
    let defaults = cvars(&[]);
    let configured = cvars(&[
        ("providers.tinyModelDevice", json!("cuda")),
        ("providers.tinyModelDtype", json!("fp16")),
        (
            "providers.tinyRuntimeLibrary",
            json!("/lib/libonnxruntime.so"),
        ),
        ("titles.generate", json!(false)),
        ("tts.localVoice", json!("bf_emma")),
    ]);
    assert_eq!(
        (
            engine_options(&defaults),
            titles_enabled(&defaults),
            local_voice(&defaults),
            engine_options(&configured),
            titles_enabled(&configured),
            local_voice(&configured),
        ),
        (
            EngineOptions {
                device: "cpu".to_owned(),
                dtype: String::new(),
                runtime_library: PathBuf::new(),
            },
            true,
            "af_heart".to_owned(),
            EngineOptions {
                device: "cuda".to_owned(),
                dtype: "fp16".to_owned(),
                runtime_library: PathBuf::from("/lib/libonnxruntime.so"),
            },
            false,
            "bf_emma".to_owned(),
        )
    );
}

#[test]
fn an_explicit_empty_chain_keeps_an_uninstalled_local_primary_unavailable() {
    let role = settings("local/lfm2.5-230m", FallbackChain::Explicit(Vec::new()));
    assert_eq!(
        resolve_with(Role::Tiny, &role, SESSION, |_| false),
        Pick::Unavailable
    );
}

#[test]
fn an_unset_chain_with_nothing_installed_uses_the_session_model() {
    let role = settings("", FallbackChain::Unset);
    assert_eq!(
        resolve_with(Role::Tiny, &role, SESSION, |_| false),
        Pick::Use(Candidate::Remote(SESSION.to_owned()))
    );
}

/// The built-in priority follows the catalog, except that `translate`
/// takes LFM2.5-350M first (the S9 translation eval).
#[test]
fn the_first_installed_local_model_comes_first() {
    let role = settings("", FallbackChain::Unset);
    assert_eq!(
        (
            eukhe_tiny::chain(Role::Translate, &role, SESSION),
            resolve_with(Role::Translate, &role, SESSION, |model| {
                model.id == "lfm2.5-230m"
            }),
            resolve_with(Role::Translate, &role, SESSION, |_| true),
            resolve_with(Role::Tiny, &role, SESSION, |_| true),
            resolve_with(Role::Dictation, &role, SESSION, |model| {
                model.id == "whisper-small"
            }),
        ),
        (
            vec![
                local("lfm2.5-350m"),
                local("lfm2.5-230m"),
                Candidate::Remote(SESSION.to_owned()),
            ],
            Pick::Use(local("lfm2.5-230m")),
            Pick::Use(local("lfm2.5-350m")),
            Pick::Use(local("lfm2.5-230m")),
            Pick::Use(local("whisper-small")),
        )
    );
}

#[test]
fn a_pick_never_leaves_the_chain() {
    let other_remote = settings(
        "",
        FallbackChain::Explicit(vec!["openai/gpt-5".to_owned(), "local/nope".to_owned()]),
    );
    let unset = settings("", FallbackChain::Unset);
    assert_eq!(
        (
            // A remote that is not the session's model is never available;
            // an id outside the catalog never is either.
            resolve_with(Role::Judge, &other_remote, SESSION, |_| true),
            // Speech takes no provider model: the session model is not in
            // its chain.
            resolve_with(Role::Speech, &unset, SESSION, |_| false),
            // No session model: nothing remote at all.
            resolve_with(Role::Tiny, &unset, "", |_| false),
        ),
        (Pick::Unavailable, Pick::Unavailable, Pick::Unavailable)
    );
}

#[test]
fn an_unavailable_role_names_its_chain_and_the_download() {
    let explicit = settings("local/lfm2.5-230m", FallbackChain::Explicit(Vec::new()));
    let remote_only = settings("openai/gpt-5", FallbackChain::Explicit(Vec::new()));
    let none = settings("", FallbackChain::Explicit(Vec::new()));
    assert_eq!(
        [
            RoleUnavailable::new(Role::Translate, &explicit, "").to_string(),
            RoleUnavailable::new(Role::Translate, &remote_only, "").to_string(),
            RoleUnavailable::new(Role::Speech, &none, "").to_string(),
        ],
        [
            "no model of the translate role is available (chain: local/lfm2.5-230m); install \
             one with `eukhe tiny-models download lfm2.5-230m`"
                .to_owned(),
            "no model of the translate role is available (chain: openai/gpt-5)".to_owned(),
            "no model for the speech role: set modelRoles.speech (or \
             retry.fallbackChains.speech); list the local models with `eukhe tiny-models`"
                .to_owned(),
        ]
    );
}

#[test]
fn the_worker_runs_as_eukhe() {
    let suffix = std::env::consts::EXE_SUFFIX;
    assert_eq!(
        (
            eukhe_sibling(Path::new(&format!("/opt/bin/eukhe{suffix}"))),
            eukhe_sibling(Path::new(&format!("/opt/bin/eukhe-daemon{suffix}"))),
        ),
        (
            PathBuf::from(format!("/opt/bin/eukhe{suffix}")),
            PathBuf::from(format!("/opt/bin/eukhe{suffix}")),
        )
    );
}

#[test]
fn a_judgment_reply_is_the_labeled_answer() {
    use eukhe_types::pi_ai::{
        ClassifierAnswer, ClassifierBoolCriteria, ClassifierQuestion, IndexMap,
    };

    let kind = ClassifierQuestion::Choice {
        instructions: "What kind of change?".to_owned(),
        criteria: IndexMap::from_iter([
            ("bug".to_owned(), String::new()),
            ("feature".to_owned(), String::new()),
        ]),
    };
    let done = ClassifierQuestion::Bool {
        instructions: "Is it done?".to_owned(),
        criteria: ClassifierBoolCriteria {
            when_true: "finished".to_owned(),
            when_false: "not finished".to_owned(),
        },
    };
    let ab = vec!["A".to_owned(), "B".to_owned()];
    let kinds = vec!["bug".to_owned(), "feature".to_owned()];
    let yes_no = vec!["Yes".to_owned(), "No".to_owned()];
    let bools = vec!["true".to_owned(), "false".to_owned()];
    assert_eq!(
        (
            judge::answer_from_reply(&kind, &ab, &kinds, "B"),
            judge::answer_from_reply(&done, &yes_no, &bools, "Yes."),
            judge::answer_from_reply(&done, &yes_no, &bools, "maybe"),
        ),
        (
            Some(ClassifierAnswer::Choice {
                choice: "feature".to_owned(),
                probabilities: IndexMap::from_iter([
                    ("bug".to_owned(), 0.0),
                    ("feature".to_owned(), 1.0),
                ]),
                confidence: 1.0,
            }),
            Some(ClassifierAnswer::Bool { probability: 1.0 }),
            None,
        )
    );
}

#[test]
fn the_local_provider_lists_the_text_models_as_classifiers() {
    let models: Vec<String> = (judge::local_provider(Path::new("/nonexistent")).get_models)()
        .expect("models")
        .iter()
        .map(|model| format!("{}/{}", model.provider(), model.id()))
        .collect();
    assert_eq!(models, ["local/lfm2.5-230m", "local/lfm2.5-350m"]);
}
