//! Local typed judgments (the `judge` role on a local model): the `local`
//! provider of a session's model collection serves each installed text
//! catalog model as a classifier model (`local/<id>`), so the existing
//! `classify` path (`Models::classify`, the code-mode `models.classify()`)
//! answers through the shared tiny worker. Each question is rendered as the
//! llama.cpp classifier renders it (`render_question`: the state, the
//! question, its answer labels), asked with `eukhe_tiny::judge_request`, and
//! read back with `eukhe_tiny::parse_label`: the greedy label is the answer
//! with probability 1. A classification that names no model takes the
//! `judge` role's model ([`judge_classifier`]).

#[cfg(test)]
mod tests;

use std::path::Path;
use std::sync::Arc;

use eukhe_ai::api::llama_cpp_classify::{answer_from_probabilities, render_question};
use eukhe_ai::api::ProviderClassifier;
use eukhe_ai::auth::{
    ApiKeyAuth, ApiKeyResolveInput, AuthOperationOptions, AuthResult, ProviderAuth,
};
use eukhe_ai::models::{create_provider, CreateProviderOptions, Models, Provider};
use eukhe_ai::utils::diagnostics::Thrown;
use eukhe_tiny::{
    Candidate, CatalogModel, ModelKind, Role, RoleSettings, TinyClient, TinyHome, CATALOG,
};
use eukhe_types::pi_ai::{
    AnyModel, ClassifierAnswer, ClassifierContext, ClassifierModel, ClassifierQuestion,
    ClassifierResult, ClassifierStopReason, IndexMap, Modality, ModelCost, ModelType,
};
use futures::future::BoxFuture;

use super::RoleUnavailable;
use crate::settings::SettingsManager;

/// The provider id of the local models (`local/<id>`).
pub const LOCAL_PROVIDER: &str = "local";

/// The classifier API of the local models.
pub const LOCAL_CLASSIFIER_API: &str = "eukhe-tiny";

/// The context window of the catalog's text models (LFM2.5: 32k).
const LOCAL_CONTEXT_WINDOW: u64 = 32_768;

/// The local provider needs no credential.
struct LocalAuth;

impl ApiKeyAuth for LocalAuth {
    // The trait returns a borrowed name; this one is a literal.
    #[allow(clippy::unnecessary_literal_bound)]
    fn name(&self) -> &str {
        "Local models"
    }

    fn resolve(
        &self,
        _input: ApiKeyResolveInput,
    ) -> BoxFuture<'_, Result<Option<AuthResult>, Thrown>> {
        Box::pin(async { Ok(Some(AuthResult::default())) })
    }
}

/// The classifier model of a text catalog model.
#[must_use]
pub fn classifier_model(model: &CatalogModel) -> ClassifierModel {
    ClassifierModel {
        id: model.id.to_owned(),
        name: model.title.to_owned(),
        api: LOCAL_CLASSIFIER_API.to_owned(),
        provider: LOCAL_PROVIDER.to_owned(),
        base_url: String::new(),
        input: vec![Modality::Text],
        input_limits: None,
        cost: ModelCost::default(),
        headers: None,
        context_window: LOCAL_CONTEXT_WINDOW,
    }
}

/// The catalog's text models as classifier models.
fn classifier_models() -> Arc<[AnyModel]> {
    CATALOG
        .iter()
        .filter(|model| match model.kind {
            ModelKind::Text { .. } => true,
            ModelKind::SpeechToText | ModelKind::TextToSpeech => false,
        })
        .map(|model| AnyModel::Classifier(classifier_model(model)))
        .collect()
}

/// The `local` provider of the agent dir's tiny models: every text catalog
/// model is listed; only the installed ones are available.
///
/// # Panics
///
/// Never: the provider has a classifier implementation.
#[must_use]
pub fn local_provider(agent_dir: &Path) -> Provider {
    let installed_home = TinyHome::under(agent_dir);
    let agent_dir = agent_dir.to_path_buf();
    let classify: eukhe_ai::api::ClassifyFn = Arc::new(move |model, context, _options| {
        let (agent_dir, model, context) = (agent_dir.clone(), model.clone(), context.clone());
        Box::pin(async move { classify(&agent_dir, &model, &context).await })
    });
    let options = CreateProviderOptions {
        id: LOCAL_PROVIDER.to_owned(),
        name: Some("Local models".to_owned()),
        auth: ProviderAuth {
            api_key: Some(Arc::new(LocalAuth)),
            oauth: None,
        },
        models: classifier_models(),
        filter_all_models: Some(Arc::new(move |models, _credential| {
            models
                .into_iter()
                .filter(|model| {
                    eukhe_tiny::find(model.id())
                        .is_some_and(|local| eukhe_tiny::installed(&installed_home, local))
                })
                .collect()
        })),
        classifiers: Some(IndexMap::from_iter([(
            LOCAL_CLASSIFIER_API.to_owned(),
            ProviderClassifier { classify },
        )])),
        ..CreateProviderOptions::default()
    };
    match create_provider(options) {
        Ok(provider) => provider,
        Err(error) => panic!("the local provider has a classifier: {error}"),
    }
}

/// Adds the `local` provider to `models` unless a provider of that id (a
/// user's `models.json` one) is already there.
pub fn add_local_provider(models: &Models, agent_dir: &Path) {
    if models.get_provider(LOCAL_PROVIDER).is_none() {
        models.set_provider(local_provider(agent_dir));
    }
}

/// Why the `judge` role gave no classifier model.
#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
pub enum JudgeClassifierError {
    /// No candidate of the role's chain is an available classifier model.
    #[error(transparent)]
    Unavailable(RoleUnavailable),
    /// Checking a provider candidate (its auth, its model list) failed.
    #[error("checking the classifier models of provider {provider}: {message}")]
    Provider { provider: String, message: String },
}

/// The classifier model of the `judge` role for a
/// classification that names no model: the first candidate of the role's
/// chain that is an available classifier model of `models` (`pick` in
/// bend/tiny.bend; later candidates are not checked). A local candidate is
/// available when `installed` holds for its catalog entry and `models`
/// serves it (the `local` provider); a provider selector (`provider/id`)
/// when its provider has configured auth and lists `id` as a classifier
/// model. `session_model` is the conversation's chat model (`provider/id`;
/// empty: none), the chain's last candidate with an unset fallback.
///
/// # Errors
///
/// [`JudgeClassifierError::Unavailable`], with the role and its chain, when
/// no candidate is available; [`JudgeClassifierError::Provider`] when a
/// provider candidate cannot be checked.
pub async fn judge_classifier(
    models: &Models,
    settings: &RoleSettings,
    session_model: &str,
    installed: impl Fn(&CatalogModel) -> bool,
) -> Result<ClassifierModel, JudgeClassifierError> {
    let chain = eukhe_tiny::chain(Role::Judge, settings, session_model);
    for candidate in &chain {
        let found = match candidate {
            Candidate::Local(id) => match candidate.local_model() {
                Some(local) if installed(local) => {
                    models.get_model_of_type(ModelType::Classifier, LOCAL_PROVIDER, id)
                }
                Some(_) | None => None,
            },
            Candidate::Remote(selector) => match selector.split_once('/') {
                Some((provider, id)) => models
                    .get_available_of_type(
                        ModelType::Classifier,
                        Some(provider),
                        AuthOperationOptions::default(),
                    )
                    .await
                    .map_err(|error| JudgeClassifierError::Provider {
                        provider: provider.to_owned(),
                        message: error.to_string(),
                    })?
                    .into_iter()
                    .find(|model| model.id() == id),
                None => None,
            },
        };
        if let Some(AnyModel::Classifier(model)) = found {
            return Ok(model);
        }
    }
    Err(JudgeClassifierError::Unavailable(RoleUnavailable {
        role: Role::Judge,
        chain,
    }))
}

fn now_ms() -> u64 {
    std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .map_or(0, |elapsed| {
            u64::try_from(elapsed.as_millis()).unwrap_or(u64::MAX)
        })
}

/// The answer a judgment `reply` gives to `question`, whose answer labels
/// stand for `keys`: the label's key with probability 1. `None` when the
/// reply is no label.
#[must_use]
pub fn answer_from_reply(
    question: &ClassifierQuestion,
    labels: &[String],
    keys: &[String],
    reply: &str,
) -> Option<ClassifierAnswer> {
    let index = eukhe_tiny::parse_label(reply, labels)?;
    let probabilities: Vec<f64> = (0..keys.len())
        .map(|at| if at == index { 1.0 } else { 0.0 })
        .collect();
    Some(answer_from_probabilities(question, keys, &probabilities))
}

/// Every question of `context` on the local `model` through `client`.
///
/// # Errors
///
/// The first question that fails: a render error, the worker's failure,
/// or a reply that is no label.
#[tracing::instrument(skip_all, fields(model = model.id))]
pub async fn judge_all(
    client: &TinyClient,
    model: &'static CatalogModel,
    context: &ClassifierContext,
) -> Result<IndexMap<String, ClassifierAnswer>, String> {
    let mut answers = IndexMap::new();
    for (id, question) in &context.questions {
        let labeled = render_question(context, id).map_err(|error| error.to_string())?;
        let request = eukhe_tiny::judge_request(&labeled.content, &labeled.labels);
        let reply = client
            .chat(model, request)
            .await
            .map_err(|error| error.to_string())?;
        let answer = answer_from_reply(question, &labeled.labels, &labeled.keys, &reply.text)
            .ok_or_else(|| {
                format!(
                    "local/{} answered {:?}, not one of the labels {}",
                    model.id,
                    reply.text.trim(),
                    labeled.labels.join(", ")
                )
            })?;
        answers.insert(id.clone(), answer);
    }
    Ok(answers)
}

/// The classifier entry of the `local` provider. Never fails: a failure
/// is an error result.
#[tracing::instrument(skip_all, fields(model = %model.id))]
async fn classify(
    agent_dir: &Path,
    model: &ClassifierModel,
    context: &ClassifierContext,
) -> ClassifierResult {
    let answered = match eukhe_tiny::find(&model.id) {
        Some(local) => match super::worker_exe() {
            Ok(worker_exe) => {
                let settings = SettingsManager::create(agent_dir, agent_dir);
                let client = super::client(agent_dir, settings.cvars(), worker_exe);
                judge_all(&client, local, context).await
            }
            Err(error) => Err(format!("the eukhe executable is unknown: {error}")),
        },
        None => Err(format!("`local/{}` is not a catalog model", model.id)),
    };
    let (answers, stop_reason, error_message) = match answered {
        Ok(answers) => (answers, ClassifierStopReason::Stop, None),
        Err(message) => (IndexMap::new(), ClassifierStopReason::Error, Some(message)),
    };
    ClassifierResult {
        api: model.api.clone(),
        provider: model.provider.clone(),
        model: model.id.clone(),
        answers,
        usage: None,
        stop_reason,
        error_message,
        timestamp: now_ms(),
    }
}
