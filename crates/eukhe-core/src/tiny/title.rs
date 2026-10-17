//! Session titles (the `tiny` role): a top-level session's first user
//! message becomes a 3–7 word title (`eukhe_tiny::title_request`, read
//! back by `eukhe_tiny::normalize_title`). The host runs it in the
//! background and stores the title through its session-name path; a
//! failure leaves the session untitled.

use eukhe_ai::models::Models;
use eukhe_tiny::{Pick, Role, TinyClient, TinyHome};
use eukhe_types::pi_ai::Model;

use super::{resolve, role_settings, run_text, titles_enabled, RoleRunError, TextBackends};
use crate::settings::cvar::Cvars;

/// What a title request needs.
pub struct TitleRequest<'a> {
    /// The session's first user message.
    pub first_message: &'a str,
    /// The session's settings.
    pub cvars: &'a Cvars,
    /// Where the tiny models are installed.
    pub home: &'a TinyHome,
    pub client: &'a TinyClient,
    pub models: &'a Models,
    /// The session's usable provider model (the role's remote candidate).
    pub session_model: Option<&'a Model>,
}

/// How a title request ended without an error.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TitleOutcome {
    Titled(String),
    /// `titles.generate` is off.
    Disabled,
    /// No model of the `tiny` role is available.
    Unavailable,
    /// The model's reply held no title.
    Empty,
}

/// The title of a session's first message.
///
/// # Errors
///
/// The picked model failed (nothing else is tried).
#[tracing::instrument(skip_all)]
pub async fn generate_title(request: TitleRequest<'_>) -> Result<TitleOutcome, RoleRunError> {
    if !titles_enabled(request.cvars) {
        return Ok(TitleOutcome::Disabled);
    }
    if request.first_message.trim().is_empty() {
        return Ok(TitleOutcome::Empty);
    }
    let session_model = request
        .session_model
        .map(super::model_selector)
        .unwrap_or_default();
    let settings = role_settings(request.cvars, Role::Tiny);
    let candidate = match resolve(Role::Tiny, &settings, request.home, &session_model) {
        Pick::Use(candidate) => candidate,
        Pick::Unavailable => return Ok(TitleOutcome::Unavailable),
    };
    let backends = TextBackends {
        client: request.client,
        models: Some(request.models),
        session_model: request.session_model,
    };
    let reply = run_text(
        &candidate,
        eukhe_tiny::title_request(request.first_message),
        &backends,
    )
    .await?;
    Ok(match eukhe_tiny::normalize_title(&reply) {
        Some(title) => TitleOutcome::Titled(title),
        None => TitleOutcome::Empty,
    })
}
