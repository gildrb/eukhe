//! The request options of the Google wire APIs (TS `GoogleOptions` /
//! `GoogleVertexOptions`), the shared `streamSimple` option mapping, and the
//! client header and thinking-budget helpers both TS modules duplicate.

use eukhe_chord::context::AbortSignal;
use eukhe_types::pi_ai::{
    IndexMap, JsonObject, JsonValue, Model, ModelThinkingLevel, ProviderHeaders, ThinkingBudgets,
    TranscriptContext,
};
use serde::Deserialize;

use super::super::simple_options::build_base_options;
use super::{
    as_thinking_level, resolve_google_thinking_level, to_google_thinking_level,
    uses_google_thinking_level, GoogleApiThinkingLevel, ResolvedGoogleThinkingLevel,
};
use crate::models::clamp_thinking_level;
use crate::types::{ProviderStreamOptions, SimpleStreamOptions, StreamOptions};
use crate::utils::diagnostics::{ErrorObject, Thrown};
use crate::utils::headers::provider_headers_to_record;
use crate::utils::pi_user_agent::get_pi_user_agent;

/// TS `GoogleOptions.thinking` / `GoogleVertexOptions.thinking`.
#[derive(Debug, Clone, PartialEq, Eq, Deserialize)]
#[serde(rename_all = "camelCase")]
pub(crate) struct GoogleThinkingOptions {
    pub enabled: bool,
    /// -1 for dynamic, 0 to disable.
    #[serde(default)]
    pub budget_tokens: Option<i64>,
    #[serde(default)]
    pub level: Option<GoogleApiThinkingLevel>,
}

/// TS `GoogleOptions` / `GoogleVertexOptions`: the shared stream options
/// plus the API-specific keys of [`ProviderStreamOptions::extra`].
#[derive(Debug, Clone, Default)]
pub(crate) struct GoogleRequestOptions {
    pub stream: StreamOptions,
    /// `"auto" | "none" | "any"`.
    pub tool_choice: Option<String>,
    pub thinking: Option<GoogleThinkingOptions>,
    /// Vertex only.
    pub project: Option<String>,
    /// Vertex only.
    pub location: Option<String>,
}

fn extra_option<T: serde::de::DeserializeOwned>(
    extra: &JsonObject,
    key: &str,
) -> Result<Option<T>, Thrown> {
    match extra.get(key) {
        None | Some(JsonValue::Null) => Ok(None),
        Some(value) => serde_json::from_value(value.clone())
            .map(Some)
            .map_err(|error| {
                ErrorObject::new(format!("Invalid Google option \"{key}\": {error}")).thrown()
            }),
    }
}

impl GoogleRequestOptions {
    /// Read the API-specific keys (`toolChoice`, `thinking`, `project`,
    /// `location`) from `extra`.
    ///
    /// # Errors
    ///
    /// When a key holds a value of the wrong shape.
    pub(crate) fn from_provider_options(options: ProviderStreamOptions) -> Result<Self, Thrown> {
        let ProviderStreamOptions { stream, extra } = options;
        Ok(Self {
            tool_choice: extra_option(&extra, "toolChoice")?,
            thinking: extra_option(&extra, "thinking")?,
            project: extra_option(&extra, "project")?,
            location: extra_option(&extra, "location")?,
            stream,
        })
    }

    pub(crate) fn signal(&self) -> Option<&AbortSignal> {
        self.stream.request.signal.as_ref()
    }
}

/// A module's `getGoogleBudget(model, level, customBudgets)`.
pub(crate) type GetGoogleBudget =
    fn(&Model, ResolvedGoogleThinkingLevel, Option<&ThinkingBudgets>) -> i64;

/// The `streamSimple` body shared by both TS modules: base options plus
/// `toolChoice`, and `thinking` disabled, level-based, or budget-based.
///
/// # Errors
///
/// An unsupported thinking-level mapping (a synchronous throw in TS).
pub(crate) fn simple_request_options(
    model: &Model,
    context: &TranscriptContext,
    options: SimpleStreamOptions,
    api_key: Option<&str>,
    get_google_budget: GetGoogleBudget,
) -> Result<GoogleRequestOptions, Thrown> {
    let stream = build_base_options(model, context, Some(&options), api_key);
    let SimpleStreamOptions {
        tool_choice,
        reasoning,
        thinking_budgets,
        ..
    } = options;
    let base = GoogleRequestOptions {
        stream,
        tool_choice: tool_choice.map(|choice| choice.as_str().to_owned()),
        ..GoogleRequestOptions::default()
    };
    let clamped = reasoning.and_then(|reasoning| {
        as_thinking_level(clamp_thinking_level(
            model,
            ModelThinkingLevel::from(reasoning),
        ))
    });
    let Some(clamped) = clamped else {
        return Ok(GoogleRequestOptions {
            thinking: Some(GoogleThinkingOptions {
                enabled: false,
                budget_tokens: None,
                level: None,
            }),
            ..base
        });
    };
    let resolved = resolve_google_thinking_level(model, clamped)?;
    let thinking = if uses_google_thinking_level(model) {
        GoogleThinkingOptions {
            enabled: true,
            budget_tokens: None,
            level: Some(to_google_thinking_level(resolved)),
        }
    } else {
        GoogleThinkingOptions {
            enabled: true,
            budget_tokens: Some(get_google_budget(
                model,
                resolved,
                thinking_budgets.as_ref(),
            )),
            level: None,
        }
    };
    Ok(GoogleRequestOptions {
        thinking: Some(thinking),
        ..base
    })
}

/// `providerHeadersToRecord({ "User-Agent": getPiUserAgent(),
/// ...model.headers, ...optionsHeaders })`.
pub(crate) fn pi_headers(
    model: &Model,
    options_headers: Option<&ProviderHeaders>,
) -> Option<IndexMap<String, String>> {
    // Object spread: a repeated key keeps its first position.
    let mut spread = ProviderHeaders::new();
    spread.insert(
        "User-Agent".to_owned(),
        Some(get_pi_user_agent().to_owned()),
    );
    for (name, value) in model.headers.iter().flatten() {
        spread.insert(name.clone(), Some(value.clone()));
    }
    for (name, value) in options_headers.into_iter().flatten() {
        spread.insert(name.clone(), value.clone());
    }
    provider_headers_to_record(&[Some(&spread)])
}

/// `customBudgets?.[level]`.
pub(crate) fn custom_budget(
    custom_budgets: Option<&ThinkingBudgets>,
    level: ResolvedGoogleThinkingLevel,
) -> Option<i64> {
    let budgets = custom_budgets?;
    let budget = match level {
        ResolvedGoogleThinkingLevel::Minimal => budgets.minimal,
        ResolvedGoogleThinkingLevel::Low => budgets.low,
        ResolvedGoogleThinkingLevel::Medium => budgets.medium,
        ResolvedGoogleThinkingLevel::High => budgets.high,
    }?;
    Some(i64::try_from(budget).unwrap_or(i64::MAX))
}

/// The `[minimal, low, medium, high]` table entry for `level`.
pub(crate) const fn budget_for(budgets: [i64; 4], level: ResolvedGoogleThinkingLevel) -> i64 {
    match level {
        ResolvedGoogleThinkingLevel::Minimal => budgets[0],
        ResolvedGoogleThinkingLevel::Low => budgets[1],
        ResolvedGoogleThinkingLevel::Medium => budgets[2],
        ResolvedGoogleThinkingLevel::High => budgets[3],
    }
}
