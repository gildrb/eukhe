//! Auxiliary-model routing for background summarizer passes (TS #2411's
//! `_resolveAuxiliaryModel`): compaction and branch summaries resolve
//! their model through the `auxiliaryModel` setting, so their one-off
//! prompts run off the session model and the session's provider
//! prompt-cache prefix stays intact. An unset or equal selector keeps the
//! session model. A set, different selector that cannot be used falls back
//! to the session model, and the session shows why ([`AuxiliaryNotices`]):
//! the fallback changes cost, prompt cache and maybe provider, so the user
//! must see it (TS only writes a `console.warn`).
//!
//! [`decide_auxiliary_route`] is the one decision both resolvers use (this
//! one and the daemon's branch summary); its Bend model is
//! `bend/aux_fallback.bend`.

use std::collections::{BTreeMap, HashSet};
use std::path::PathBuf;
use std::sync::{Mutex, PoisonError};

use eukhe_ai::models::Models;
use eukhe_bend::wire::{Reader, Writer, NAT_MAX};
use eukhe_bend::{expect_core, Entry, WireError};
use eukhe_chord::context::Context;
use eukhe_durable::harness::types::{SubmissionDraft, WriteSubmissionDraft};
use eukhe_durable::harness::Conversation;
use eukhe_types::pi_ai::Model;

/// The custom type of the row that tells why a summarizer pass did not use
/// the `auxiliaryModel` setting (display-only: the user sees it, the model
/// does not).
pub const AUXILIARY_MODEL_NOTICE_CUSTOM_TYPE: &str = "eukhe.auxiliary_model";

/// The routing context: the working directory and agent directory the
/// settings (`auxiliaryModel`, `allowedModels`) and the model registry
/// (`models.json`, auth storage) resolve against.
#[derive(Debug, Clone)]
pub struct AuxiliaryModelContext {
    pub cwd: PathBuf,
    pub agent_dir: PathBuf,
}

/// What the `auxiliaryModel` setting names, next to the session model.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum AuxiliarySelector {
    /// Unset, blank, or malformed (TS `getAuxiliaryModel`).
    Unset,
    /// The session model itself.
    SessionModel,
    /// Another model: `provider/model-id`, in lower case.
    Other(String),
}

impl AuxiliarySelector {
    /// The selector of the `setting` value for a session on
    /// `session_provider`/`session_model_id`.
    #[must_use]
    pub fn of(setting: Option<&str>, session_provider: &str, session_model_id: &str) -> Self {
        let Some(selector) = setting
            .map(|selector| selector.trim().to_lowercase())
            .filter(|selector| !selector.is_empty())
        else {
            return Self::Unset;
        };
        if format!("{session_provider}/{session_model_id}").to_lowercase() == selector {
            Self::SessionModel
        } else {
            Self::Other(selector)
        }
    }
}

/// Why a set, different selector was not used.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum FallbackReason {
    /// `allowedModels` does not admit it (the daemon's guardrail).
    NotAllowed,
    /// The list of available models could not be read.
    ModelListFailed,
    /// No authenticated catalog model has this selector.
    NotFound,
    /// The model's API key or headers did not resolve.
    NoKey,
    /// The session's model collection does not serve it.
    NotInSession,
    /// Its known context window is smaller than the request.
    WindowTooSmall,
}

/// A model the selector found, with its context window (`0`: unknown).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Found<T> {
    pub model: T,
    pub context_window: u64,
}

/// Where a summarizer pass runs.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum AuxiliaryRoute<T> {
    /// The selector is unset or names the session model: the session
    /// model, with nothing to say.
    Session,
    /// The selector's model.
    Routed(T),
    /// The session model in place of the set selector, and why.
    Fallback {
        selector: String,
        reason: FallbackReason,
    },
}

/// What the decision knows before the resolver's lookups
/// (`bend/aux_fallback.bend` `Gate`): the route, or that the lookups of
/// the named selector must run.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Gate<'a> {
    /// The session model runs, with nothing to say.
    Session,
    /// The session model runs in place of the named selector.
    Fallback(&'a str, FallbackReason),
    /// The lookups of the named selector decide.
    Lookup(&'a str),
}

/// A fallback reason's number in `bend/aux_fallback.bend`.
fn reason_nat(reason: FallbackReason) -> u64 {
    match reason {
        FallbackReason::NotAllowed => 0,
        FallbackReason::ModelListFailed => 1,
        FallbackReason::NotFound => 2,
        FallbackReason::NoKey => 3,
        FallbackReason::NotInSession => 4,
        FallbackReason::WindowTooSmall => 5,
    }
}

/// The fallback key of a reply (`p`, `s`, `r`); the purpose and the
/// selector are the opaque 0 the requests send.
fn read_reason(reader: &mut Reader<'_>) -> Result<FallbackReason, WireError> {
    reader.nat()?;
    reader.nat()?;
    let at = 0;
    match reader.nat()? {
        0 => Ok(FallbackReason::NotAllowed),
        1 => Ok(FallbackReason::ModelListFailed),
        2 => Ok(FallbackReason::NotFound),
        3 => Ok(FallbackReason::NoKey),
        4 => Ok(FallbackReason::NotInSession),
        5 => Ok(FallbackReason::WindowTooSmall),
        _reason => Err(WireError::Malformed {
            at,
            expected: "a fallback reason",
        }),
    }
}

/// The selector, then `allowedModels` (`allowed`: whether it admits the
/// selector; read only for another model): `bend/aux_fallback.bend`
/// `gate`, run by the compiled core.
///
/// # Panics
///
/// When the compiled core fails or answers out of shape: an inconsistent
/// build ([`eukhe_bend::expect_core`]).
pub(crate) fn gate(selector: &AuxiliarySelector, allowed: bool) -> Gate<'_> {
    let decided = (|| -> Result<Gate<'_>, eukhe_bend::Error> {
        let mut request = Writer::new();
        request.tag(0).nat(0);
        let name = match selector {
            AuxiliarySelector::Unset => {
                request.tag(0);
                None
            }
            AuxiliarySelector::SessionModel => {
                request.tag(1);
                None
            }
            AuxiliarySelector::Other(name) => {
                request.tag(2).nat(0);
                Some(name.as_str())
            }
        };
        request.bool(allowed);
        let reply = eukhe_bend::call(Entry::AuxFallback, &request.finish()?)?;
        let mut reader = Reader::reply(&reply)?;
        let out_of_shape = || WireError::Malformed {
            at: 0,
            expected: "a gate of the selector",
        };
        let decided = match (reader.tag_of(2, "a gate")?, name) {
            (0, name) => match (reader.tag_of(3, "a route")?, name) {
                (0, None) => Gate::Session,
                (2, Some(name)) => Gate::Fallback(name, read_reason(&mut reader)?),
                (_route, _) => return Err(out_of_shape().into()),
            },
            (1, Some(name)) => {
                reader.nat()?;
                reader.nat()?;
                Gate::Lookup(name)
            }
            (_gate, _) => return Err(out_of_shape().into()),
        };
        reader.end()?;
        Ok(decided)
    })();
    expect_core(Entry::AuxFallback, decided)
}

/// The route of an admitted selector once its lookups ran: `found` is the
/// found model (its context window `0`: unknown) or why nothing usable was
/// found; `required_context_tokens` is the request's size (`None`:
/// unknown). `Ok` routes the pass to the found model, `Err` is the reason
/// it falls back: `bend/aux_fallback.bend` `settle`, run by the compiled
/// core. Sizes past the wire's largest Nat saturate.
///
/// # Panics
///
/// When the compiled core fails or answers out of shape: an inconsistent
/// build ([`eukhe_bend::expect_core`]).
pub(crate) fn settle<T>(
    found: Result<Found<T>, FallbackReason>,
    required_context_tokens: Option<u64>,
) -> Result<T, FallbackReason> {
    let decided = (|| -> Result<Result<T, FallbackReason>, eukhe_bend::Error> {
        let mut request = Writer::new();
        request.tag(1).tag(1).nat(0).nat(0);
        match &found {
            Err(reason) => request.tag(0).nat(reason_nat(*reason)),
            Ok(found) => request.tag(1).nat(found.context_window.min(NAT_MAX)),
        };
        request.nat(required_context_tokens.unwrap_or(0).min(NAT_MAX));
        let reply = eukhe_bend::call(Entry::AuxFallback, &request.finish()?)?;
        let mut reader = Reader::reply(&reply)?;
        let settled = match (reader.tag_of(3, "a route")?, found) {
            (1, Ok(found)) => Ok(found.model),
            (2, _) => Err(read_reason(&mut reader)?),
            (_route, _) => {
                return Err(WireError::Malformed {
                    at: 0,
                    expected: "the route of a looked-up selector",
                }
                .into())
            }
        };
        reader.end()?;
        Ok(settled)
    })();
    expect_core(Entry::AuxFallback, decided)
}

/// Decide where a summarizer pass runs, with the checks in their order:
/// the selector (unset or the session model keeps the session), then
/// `allowedModels`, then `find` (the resolver's own lookups: catalog, key,
/// collection), then the context window against `required_context_tokens`
/// (a known window smaller than the request falls back; an unknown window
/// or an unknown request keeps the route). `find` runs only when the gate
/// asks for the lookups.
pub fn decide_auxiliary_route<T>(
    selector: &AuxiliarySelector,
    allowlist: Option<&[String]>,
    required_context_tokens: Option<u64>,
    find: impl FnOnce(&str) -> Result<Found<T>, FallbackReason>,
) -> AuxiliaryRoute<T> {
    let allowed = match selector {
        AuxiliarySelector::Other(name) => {
            allowlist.is_none_or(|allowlist| crate::models::model_allowed(name, allowlist))
        }
        AuxiliarySelector::Unset | AuxiliarySelector::SessionModel => true,
    };
    let (name, reason) = match gate(selector, allowed) {
        Gate::Session => return AuxiliaryRoute::Session,
        Gate::Fallback(name, reason) => (name, reason),
        Gate::Lookup(name) => match settle(find(name), required_context_tokens) {
            Ok(model) => return AuxiliaryRoute::Routed(model),
            Err(reason) => (name, reason),
        },
    };
    AuxiliaryRoute::Fallback {
        selector: name.to_owned(),
        reason,
    }
}

/// The fallbacks one session has shown. Each distinct purpose, selector
/// and reason shows once per session: a selector that cannot be used would
/// otherwise add the same row at every compaction, and one row tells the
/// cause. A new selector, purpose or reason is new information, so it
/// shows. The set lives in memory: a reopened session shows a fallback
/// again once.
#[derive(Debug, Default)]
pub struct AuxiliaryNotices {
    shown: Mutex<HashSet<(String, String, FallbackReason)>>,
}

impl AuxiliaryNotices {
    /// The notice text of `route` for `purpose` (e.g. "compaction summary")
    /// when it is a fallback this session has not shown yet; `None`
    /// otherwise. `session_model` is the `provider/model-id` that ran the
    /// pass. The text names the selector and the reason, never auth
    /// details: those can hold credential material (TS `CodeQL`
    /// `js/clear-text-logging`).
    pub fn take<T>(
        &self,
        purpose: &str,
        route: &AuxiliaryRoute<T>,
        session_model: &str,
    ) -> Option<String> {
        let (selector, reason) = match route {
            AuxiliaryRoute::Session | AuxiliaryRoute::Routed(_) => return None,
            AuxiliaryRoute::Fallback { selector, reason } => (selector, *reason),
        };
        let fresh = self
            .shown
            .lock()
            .unwrap_or_else(PoisonError::into_inner)
            .insert((purpose.to_owned(), selector.clone(), reason));
        if !fresh {
            return None;
        }
        let why = match reason {
            FallbackReason::NotAllowed => "allowedModels does not include it",
            FallbackReason::ModelListFailed => "the list of available models could not be read",
            FallbackReason::NotFound => "no model with a configured key has this name",
            FallbackReason::NoKey => "its API key could not be found",
            FallbackReason::NotInSession => "the session's model list does not include it",
            FallbackReason::WindowTooSmall => "its context window is too small for the request",
        };
        Some(format!(
            "The auxiliaryModel setting \"{selector}\" was not used for the {purpose}: {why}. The session model {session_model} ran it."
        ))
    }
}

/// Show the notice `text` as a display-only row of `conversation`. It is a
/// write submission: placed at once when the conversation is idle,
/// otherwise at its next boundary (nothing else may append to a busy
/// conversation). A row that cannot be submitted is logged: it has no
/// other place to go.
pub async fn show_auxiliary_notice(conversation: &Conversation, text: String, cx: &Context) {
    show_notice_row(conversation, AUXILIARY_MODEL_NOTICE_CUSTOM_TYPE, text, cx).await;
}

/// Show the notice `text` as a display-only row of `custom_type` (one of
/// [`crate::durable::entries::is_display_only_custom_type`]) on
/// `conversation`, as [`show_auxiliary_notice`] does.
#[tracing::instrument(skip_all, fields(custom_type = %custom_type))]
pub(crate) async fn show_notice_row(
    conversation: &Conversation,
    custom_type: &str,
    text: String,
    cx: &Context,
) {
    let notice = crate::durable::rlm::CustomNotice::new(custom_type, text, true, None);
    let submitted = match notice.draft() {
        Ok(entry) => conversation
            .submit(
                SubmissionDraft::Write(WriteSubmissionDraft {
                    request_id: None,
                    entry,
                }),
                cx,
            )
            .await
            .map(drop)
            .map_err(anyhow::Error::from),
        Err(error) => Err(anyhow::Error::from(error)),
    };
    if let Err(error) = submitted {
        tracing::warn!(%error, custom_type, "notice row not delivered");
    }
}

/// Where a compaction summary runs: the model, the key it sends (the
/// session model's own auth rides the session's [`Models`] when `None`),
/// its merged request headers (TS `_resolveAuxiliaryModel`'s `{ model,
/// apiKey, headers }`), and the notice text to show, if any.
#[derive(Debug, Clone)]
pub struct AuxiliaryResolution {
    pub model: Model,
    pub api_key: Option<String>,
    pub headers: Option<BTreeMap<String, String>>,
    pub notice: Option<String>,
}

/// Resolve a compaction summary's model through the `auxiliaryModel`
/// setting (TS #2411's `_resolveAuxiliaryModel`), with the lookups in
/// order: the authenticated catalog (TS `_authenticatedRlmModels`, the
/// registry's searchable set), the model's key, and the session's model
/// collection `models` (which owns provider overrides).
/// `required_context_tokens` is the size of the request the pass will
/// issue (`None` when unknown).
///
/// The session fallback resolves its merged headers through the same
/// registry the session's own requests use, so it ships the stored team
/// header exactly like them.
#[must_use]
pub fn resolve_auxiliary_model(
    context: &AuxiliaryModelContext,
    models: &Models,
    notices: &AuxiliaryNotices,
    purpose: &str,
    session_model: &Model,
    required_context_tokens: Option<u64>,
) -> AuxiliaryResolution {
    let settings = crate::settings::SettingsManager::create(&context.cwd, &context.agent_dir);
    let selector = AuxiliarySelector::of(
        settings.get_auxiliary_model().as_deref(),
        &session_model.provider,
        &session_model.id,
    );
    let auth = crate::auth::AuthStorage::create(&context.agent_dir);
    let mut registry =
        crate::models::ModelRegistry::create(auth, context.agent_dir.join("models.json"));
    let route = decide_auxiliary_route(
        &selector,
        settings.get_allowed_models().as_deref(),
        required_context_tokens,
        |selector| {
            let model = registry
                .get_rlm_searchable_models()
                .into_iter()
                .find(|model| format!("{}/{}", model.provider, model.id).to_lowercase() == selector)
                .cloned()
                .ok_or(FallbackReason::NotFound)?;
            let resolved = registry.get_api_key_and_headers(&model);
            if !resolved.ok {
                return Err(FallbackReason::NoKey);
            }
            let served = models
                .get_model(&model.provider, &model.id)
                .ok_or(FallbackReason::NotInSession)?;
            Ok(Found {
                context_window: model.context_window,
                model: (served, resolved.api_key, resolved.headers),
            })
        },
    );
    let notice = notices.take(
        purpose,
        &route,
        &format!("{}/{}", session_model.provider, session_model.id),
    );
    match route {
        AuxiliaryRoute::Routed((model, api_key, headers)) => AuxiliaryResolution {
            model,
            api_key,
            headers,
            notice,
        },
        AuxiliaryRoute::Session | AuxiliaryRoute::Fallback { .. } => {
            let legacy = crate::durable::rlm::refine::legacy_model(session_model);
            AuxiliaryResolution {
                model: session_model.clone(),
                api_key: None,
                headers: registry.get_api_key_and_headers(&legacy).headers,
                notice,
            }
        }
    }
}

#[cfg(test)]
mod tests;
