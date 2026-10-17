//! The S9 roles (docs/inference.md S9): each role's settings from its cvars
//! (`modelRoles.<role>`, `retry.fallbackChains.<role>`, `providers.tiny*`),
//! the resolution of a role to one model of its chain, and the run of a
//! text role's request on the picked model: a local catalog model through
//! the shared tiny worker ([`eukhe_tiny::TinyClient`]), the session's
//! provider model through the one-shot `complete_simple` path.
//!
//! A task uses the first available model of its chain and only that one:
//! a failing local model never falls through to another (a local primary
//! is a no-billing boundary); with none available the outcome is
//! [`Pick::Unavailable`].

use std::fmt;
use std::path::{Path, PathBuf};

use eukhe_ai::models::{Models, ModelsSimpleStreamOptions};
use eukhe_ai::types::{SimpleStreamOptions, StreamOptions};
use eukhe_tiny::{CatalogModel, ChatRequest, ChatRole, EngineOptions, FallbackChain};
use eukhe_types::pi_ai::{
    AssistantContentBlock, Context as PiContext, Message, Model, StopReason, UserContent,
    UserMessage,
};
use serde_json::Value;

use crate::settings::cvar::{table, Cvars, Decl};

pub use eukhe_tiny::{Candidate, Pick, Role, RoleSettings, TinyClient, TinyError, TinyHome};

pub mod judge;
#[cfg(test)]
mod smoke_tests;
#[cfg(test)]
mod tests;
pub mod title;

/// The `modelRoles.<role>` and `retry.fallbackChains.<role>` cvars.
fn role_decls(role: Role) -> (&'static Decl, &'static Decl) {
    match role {
        Role::Tiny => (&table::MODEL_ROLE_TINY, &table::FALLBACK_CHAIN_TINY),
        Role::Judge => (&table::MODEL_ROLE_JUDGE, &table::FALLBACK_CHAIN_JUDGE),
        Role::Translate => (
            &table::MODEL_ROLE_TRANSLATE,
            &table::FALLBACK_CHAIN_TRANSLATE,
        ),
        Role::Speech => (&table::MODEL_ROLE_SPEECH, &table::FALLBACK_CHAIN_SPEECH),
        Role::Dictation => (
            &table::MODEL_ROLE_DICTATION,
            &table::FALLBACK_CHAIN_DICTATION,
        ),
    }
}

/// A `retry.fallbackChains.<role>` value: `null` (or anything that is not
/// a list) is unset; a list keeps its non-blank string selectors.
fn fallback_chain(value: &Value) -> FallbackChain {
    match value {
        Value::Array(items) => FallbackChain::Explicit(
            items
                .iter()
                .filter_map(Value::as_str)
                .map(str::trim)
                .filter(|selector| !selector.is_empty())
                .map(str::to_owned)
                .collect(),
        ),
        Value::Null | Value::Bool(_) | Value::Number(_) | Value::String(_) | Value::Object(_) => {
            FallbackChain::Unset
        }
    }
}

/// The settings of `role`.
#[must_use]
pub fn role_settings(cvars: &Cvars, role: Role) -> RoleSettings {
    let (primary, fallback) = role_decls(role);
    RoleSettings {
        primary: cvars.optional_text(primary).unwrap_or_default(),
        fallback: fallback_chain(&cvars.value(fallback)),
    }
}

/// How the tiny worker runs (`providers.tinyModelDevice`,
/// `providers.tinyModelDtype`, `providers.tinyRuntimeLibrary`).
#[must_use]
pub fn engine_options(cvars: &Cvars) -> EngineOptions {
    EngineOptions {
        device: cvars
            .optional_text(&table::PROVIDERS_TINY_MODEL_DEVICE)
            .unwrap_or_else(|| "cpu".to_owned()),
        dtype: cvars
            .optional_text(&table::PROVIDERS_TINY_MODEL_DTYPE)
            .unwrap_or_default(),
        runtime_library: cvars
            .optional_text(&table::PROVIDERS_TINY_RUNTIME_LIBRARY)
            .map(PathBuf::from)
            .unwrap_or_default(),
    }
}

/// `titles.generate`.
#[must_use]
pub fn titles_enabled(cvars: &Cvars) -> bool {
    cvars.bool(&table::TITLES_GENERATE)
}

/// `tts.localVoice` (blank: `af_heart`).
#[must_use]
pub fn local_voice(cvars: &Cvars) -> String {
    cvars
        .optional_text(&table::TTS_LOCAL_VOICE)
        .unwrap_or_else(|| "af_heart".to_owned())
}

/// The model `role` uses: the first of its chain that is available. A
/// local candidate is available when `installed` holds for its catalog
/// entry (an id outside the catalog never is); a remote one when it is
/// `session_model`, the session's usable provider model (`provider/id`;
/// empty: none).
#[must_use]
pub fn resolve_with(
    role: Role,
    settings: &RoleSettings,
    session_model: &str,
    installed: impl Fn(&CatalogModel) -> bool,
) -> Pick<Candidate> {
    let chain = eukhe_tiny::chain(role, settings, session_model);
    let available: Vec<Candidate> = chain
        .iter()
        .filter(|candidate| match candidate {
            Candidate::Local(_) => candidate.local_model().is_some_and(&installed),
            Candidate::Remote(selector) => !session_model.is_empty() && selector == session_model,
        })
        .cloned()
        .collect();
    match eukhe_tiny::pick(&chain, &available) {
        Pick::Use(candidate) => Pick::Use(candidate.clone()),
        Pick::Unavailable => Pick::Unavailable,
    }
}

/// [`resolve_with`] over the models installed under `home`.
#[must_use]
pub fn resolve(
    role: Role,
    settings: &RoleSettings,
    home: &TinyHome,
    session_model: &str,
) -> Pick<Candidate> {
    resolve_with(role, settings, session_model, |model| {
        eukhe_tiny::installed(home, model)
    })
}

/// The `provider/id` selector of a provider model.
#[must_use]
pub fn model_selector(model: &Model) -> String {
    format!("{}/{}", model.provider, model.id)
}

/// A role with no available model: its chain, for the message.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RoleUnavailable {
    pub role: Role,
    pub chain: Vec<Candidate>,
}

impl RoleUnavailable {
    /// The unavailable outcome of `role` with these settings.
    #[must_use]
    pub fn new(role: Role, settings: &RoleSettings, session_model: &str) -> Self {
        Self {
            role,
            chain: eukhe_tiny::chain(role, settings, session_model),
        }
    }
}

fn candidate_text(candidate: &Candidate) -> String {
    match candidate {
        Candidate::Local(id) => format!("{}{id}", eukhe_tiny::LOCAL_PREFIX),
        Candidate::Remote(selector) => selector.clone(),
    }
}

impl fmt::Display for RoleUnavailable {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let role = self.role.id();
        if self.chain.is_empty() {
            return write!(
                f,
                "no model for the {role} role: set modelRoles.{role} (or \
                 retry.fallbackChains.{role}); list the local models with `eukhe tiny-models`"
            );
        }
        let chain: Vec<String> = self.chain.iter().map(candidate_text).collect();
        let local = self.chain.iter().find_map(|candidate| match candidate {
            Candidate::Local(id) => Some(id.as_str()),
            Candidate::Remote(_) => None,
        });
        write!(
            f,
            "no model of the {role} role is available (chain: {})",
            chain.join(", ")
        )?;
        match local {
            Some(id) => write!(f, "; install one with `eukhe tiny-models download {id}`"),
            None => Ok(()),
        }
    }
}

impl std::error::Error for RoleUnavailable {}

/// Why a role's request failed on its picked model.
#[derive(Debug, Clone, PartialEq, thiserror::Error)]
pub enum RoleRunError {
    /// The local selector names no catalog model.
    #[error("`local/{0}` is not a catalog model (see `eukhe tiny-models`)")]
    UnknownLocal(String),
    /// The tiny worker failed.
    #[error(transparent)]
    Local(#[from] TinyError),
    /// The remote candidate is not the session's model (nothing to call).
    #[error("{0} is not the session's model")]
    NoRemote(String),
    /// The provider request failed.
    #[error("{0}")]
    Remote(String),
}

/// The models a text role's request may run on.
pub struct TextBackends<'a> {
    /// The tiny worker client.
    pub client: &'a TinyClient,
    /// The provider model collection and the session's usable model (the
    /// only remote candidate a pick can give).
    pub models: Option<&'a Models>,
    pub session_model: Option<&'a Model>,
}

/// Runs `request` on `candidate` and answers the completion text (after
/// the prefill, before any stop string).
///
/// # Errors
///
/// The worker or provider failure; see [`RoleRunError`].
#[tracing::instrument(skip_all, fields(candidate = ?candidate))]
pub async fn run_text(
    candidate: &Candidate,
    request: ChatRequest,
    backends: &TextBackends<'_>,
) -> Result<String, RoleRunError> {
    match candidate {
        Candidate::Local(id) => {
            let model = candidate
                .local_model()
                .ok_or_else(|| RoleRunError::UnknownLocal(id.clone()))?;
            Ok(backends.client.chat(model, request).await?.text)
        }
        Candidate::Remote(selector) => {
            let (Some(models), Some(model)) = (backends.models, backends.session_model) else {
                return Err(RoleRunError::NoRemote(selector.clone()));
            };
            if model_selector(model) != *selector {
                return Err(RoleRunError::NoRemote(selector.clone()));
            }
            run_remote(models, model, &request).await
        }
    }
}

/// `request` as a one-shot provider request (the prefill rides as text:
/// a provider cannot prefill).
#[tracing::instrument(skip_all, fields(model = %model.id))]
async fn run_remote(
    models: &Models,
    model: &Model,
    request: &ChatRequest,
) -> Result<String, RoleRunError> {
    let mut system = Vec::new();
    let mut messages = Vec::new();
    for message in &request.messages {
        match message.role {
            ChatRole::System => system.push(message.content.clone()),
            ChatRole::User => messages.push(Message::User(UserMessage {
                content: UserContent::Text(message.content.clone()),
                timestamp: 0,
            })),
            ChatRole::Assistant => messages.push(Message::User(UserMessage {
                content: UserContent::Text(format!("(assistant) {}", message.content)),
                timestamp: 0,
            })),
        }
    }
    let context = PiContext {
        system_prompt: (!system.is_empty()).then(|| system.join("\n\n")),
        messages,
        tools: None,
    };
    let options = SimpleStreamOptions {
        stream: StreamOptions {
            max_tokens: Some(u64::from(request.max_tokens).max(256)),
            ..StreamOptions::default()
        },
        ..SimpleStreamOptions::default()
    };
    let reply = models
        .complete_simple(model, context, ModelsSimpleStreamOptions::from(options))
        .await;
    match reply.stop_reason {
        StopReason::Error | StopReason::Aborted => {
            return Err(RoleRunError::Remote(
                reply
                    .error_message
                    .unwrap_or_else(|| "the provider request failed".to_owned()),
            ))
        }
        StopReason::Pending | StopReason::Deferred => {
            return Err(RoleRunError::Remote(
                "the provider request did not complete".to_owned(),
            ))
        }
        StopReason::Stop | StopReason::Length | StopReason::ToolUse => {}
    }
    let text: String = reply
        .content
        .iter()
        .filter_map(|block| match block {
            AssistantContentBlock::Text(text) => Some(text.text.as_str()),
            AssistantContentBlock::Thinking(_) | AssistantContentBlock::ToolCall(_) => None,
        })
        .collect();
    Ok(eukhe_tiny::remote_reply_text(request, &text))
}

/// The executable the tiny worker runs as (`eukhe tiny-worker`): this
/// process's executable when it is `eukhe`, else the `eukhe` next to it
/// (the `eukhe-daemon` binary).
///
/// # Errors
///
/// The current executable cannot be resolved.
pub fn worker_exe() -> std::io::Result<PathBuf> {
    let current = std::env::current_exe()?;
    Ok(eukhe_sibling(&current))
}

/// `exe` when its name is `eukhe`, else `eukhe` in its directory.
fn eukhe_sibling(exe: &Path) -> PathBuf {
    let name = exe.file_stem().and_then(|stem| stem.to_str());
    match name {
        Some("eukhe") => exe.to_path_buf(),
        Some(_) | None => exe.with_file_name(format!("eukhe{}", std::env::consts::EXE_SUFFIX)),
    }
}

/// The tiny client of an agent dir with the settings' engine options.
#[must_use]
pub fn client(agent_dir: &Path, cvars: &Cvars, worker_exe: PathBuf) -> TinyClient {
    TinyClient::new(
        TinyHome::under(agent_dir),
        engine_options(cvars),
        worker_exe,
    )
}
