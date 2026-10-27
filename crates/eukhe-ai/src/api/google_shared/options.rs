//! The request options of the Google wire APIs (TS `GoogleOptions` /
//! `GoogleVertexOptions`), the shared `streamSimple` option mapping, and the
//! client header and thinking-budget helpers both TS modules duplicate.

use eukhe_chord::context::AbortSignal;
use eukhe_types::pi_ai::{
    IndexMap, JsonObject, JsonValue, Model, ModelThinkingLevel, ProviderHeaders, ThinkingBudgets,
    ToolChoice, TranscriptContext,
};
use serde::Deserialize;

use super::super::simple_options::{
    budgets_call, build_base_options, write_budgets, write_customs,
};
use super::{
    as_thinking_level, resolve_google_thinking_level, to_google_thinking_level,
    uses_google_thinking_level, GoogleApiThinkingLevel, ResolvedGoogleThinkingLevel,
};
use crate::models::clamp_thinking_level;
use crate::quirks::Quirks;
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
    /// eukhe addition (`allowedFunctionNames`): the functions a `"any"`
    /// tool choice may call; one name forces that function.
    pub allowed_function_names: Option<Vec<String>>,
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
    /// Read the API-specific keys (`toolChoice`, `allowedFunctionNames`,
    /// `thinking`, `project`, `location`) from `extra`.
    ///
    /// # Errors
    ///
    /// When a key holds a value of the wrong shape.
    pub(crate) fn from_provider_options(options: ProviderStreamOptions) -> Result<Self, Thrown> {
        let ProviderStreamOptions { stream, extra } = options;
        Ok(Self {
            tool_choice: extra_option(&extra, "toolChoice")?,
            allowed_function_names: extra_option(&extra, "allowedFunctionNames")?,
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
) -> Result<GoogleRequestOptions, Thrown> {
    let stream = build_base_options(model, context, Some(&options), api_key);
    let SimpleStreamOptions {
        tool_choice,
        reasoning,
        thinking_budgets,
        ..
    } = options;
    // A forced call is Gemini's `ANY` mode; a named tool also narrows the
    // allowed functions to it.
    let (tool_choice, allowed_function_names) = match tool_choice {
        None => (None, None),
        Some(ToolChoice::Auto) => (Some("auto"), None),
        Some(ToolChoice::None) => (Some("none"), None),
        Some(ToolChoice::Required) => (Some("any"), None),
        Some(ToolChoice::Tool(name)) => (Some("any"), Some(vec![name])),
    };
    let base = GoogleRequestOptions {
        stream,
        tool_choice: tool_choice.map(str::to_owned),
        allowed_function_names,
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
            budget_tokens: Some(google_thinking_budget(
                model,
                resolved,
                thinking_budgets.as_ref(),
            )?),
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

/// The `thinkingBudget` of `level` (S10.3; model
/// `bend/facts.bend` `gbudget`): the user's custom budget of the level,
/// else the quirks rulebook's budget of the model (`thinking_budgets`),
/// held inside the model's range (the rule's `minimal` to its `high`). A
/// model that the rulebook gives no budgets takes the custom budget, else
/// `-1` (dynamic: the server decides).
///
/// # Errors
///
/// A budget rule that is not ordered (`minimal <= low <= medium <= high`)
/// has no range to hold a budget in (`laws/facts.bend`
/// `facts_google_unordered_refused`; the rulebook compiler refuses such a
/// rule, so a shipped or loaded rulebook never has one).
pub fn google_thinking_budget(
    model: &Model,
    level: ResolvedGoogleThinkingLevel,
    custom_budgets: Option<&ThinkingBudgets>,
) -> Result<i64, Thrown> {
    let rule = Quirks::of(model).thinking_budgets();
    let budget = budgets_call(
        3,
        |writer| {
            if let Some(rule) = rule {
                writer.some();
                write_budgets(writer, rule);
            } else {
                writer.none();
            }
            write_customs(writer, custom_budgets);
            writer.tag(match level {
                ResolvedGoogleThinkingLevel::Minimal => 0,
                ResolvedGoogleThinkingLevel::Low => 1,
                ResolvedGoogleThinkingLevel::Medium => 2,
                ResolvedGoogleThinkingLevel::High => 3,
            });
        },
        |reader| {
            // `tag_of` answers 0, 1 or 2.
            let tag = reader.tag_of(3, "a Google budget")?;
            Ok(if tag == 0 {
                GoogleBudget::Dynamic
            } else if tag == 1 {
                GoogleBudget::Tokens(reader.nat()?)
            } else {
                GoogleBudget::Unordered
            })
        },
    )
    .map_err(|error| ErrorObject::new(error.to_string()).thrown())?;
    match budget {
        GoogleBudget::Dynamic => Ok(-1),
        GoogleBudget::Tokens(tokens) => {
            i64::try_from(tokens).map_err(|error| ErrorObject::new(error.to_string()).thrown())
        }
        GoogleBudget::Unordered => Err(ErrorObject::new(format!(
            "The thinking_budgets rule of {}/{} is not ordered (minimal <= low <= medium <= high)",
            model.provider, model.id
        ))
        .thrown()),
    }
}

/// The reply of the compiled Google budget rule (model `Fx.GB`).
enum GoogleBudget {
    /// `-1`: the server decides.
    Dynamic,
    Tokens(u64),
    /// The model's budget rule is not ordered.
    Unordered,
}
