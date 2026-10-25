//! Model resolution, scoping, and CLI selection. Port of model-resolver.ts.

use eukhe_ai::quirks::provider_default_model;
use eukhe_bend::rules::glob::{self, GlobOptions};
use eukhe_bend::{expect_core, Entry};
use eukhe_types::ai::{Model, PRIME_INFERENCE_PROVIDER_ID};
use eukhe_types::pi_ai::ModelThinkingLevel;

use super::prime_inference::is_private_prime_inference_model;

/// A resolved model plus an explicit thinking level from the pattern.
#[derive(Debug, Clone)]
pub struct ScopedModel {
    pub model: Model,
    pub thinking_level: Option<ModelThinkingLevel>,
}

/// True when a model id looks like an alias (no date suffix).
fn is_alias(id: &str) -> bool {
    if id.ends_with("-latest") {
        return true;
    }
    id.len() < 9
        || !id[id.len() - 9..].starts_with('-')
        || id[id.len() - 8..].parse::<u32>().is_err()
}

/// Exact reference match: canonical provider/id, provider/id split, or an
/// unambiguous bare id.
#[must_use]
pub fn find_exact_model_reference_match<'a, I>(
    model_reference: &str,
    models: I,
) -> Option<&'a Model>
where
    I: IntoIterator<Item = &'a Model>,
    I::IntoIter: Clone,
{
    let available_models = models.into_iter();
    let trimmed = model_reference.trim();
    if trimmed.is_empty() {
        return None;
    }
    let normalized = trimmed.to_lowercase();
    let canonical: Vec<&Model> = available_models
        .clone()
        .filter(|model| format!("{}/{}", model.provider, model.id).to_lowercase() == normalized)
        .collect();
    if canonical.len() == 1 {
        return Some(canonical[0]);
    }
    if canonical.len() > 1 {
        return None;
    }
    if let Some(slash) = trimmed.find('/') {
        let provider = trimmed[..slash].trim();
        let model_id = trimmed[slash + 1..].trim();
        if !provider.is_empty() && !model_id.is_empty() {
            let provider_matches: Vec<&Model> = available_models
                .clone()
                .filter(|model| {
                    model.provider.to_lowercase() == provider.to_lowercase()
                        && model.id.to_lowercase() == model_id.to_lowercase()
                })
                .collect();
            if provider_matches.len() == 1 {
                return Some(provider_matches[0]);
            }
            if provider_matches.len() > 1 {
                return None;
            }
        }
    }
    let id_matches: Vec<&Model> = available_models
        .filter(|model| model.id.to_lowercase() == normalized)
        .collect();
    if id_matches.len() == 1 {
        Some(id_matches[0])
    } else {
        None
    }
}

fn fuzzy_match_model<'a>(pattern: &str, available_models: &'a [Model]) -> Option<&'a Model> {
    let normalized = pattern.to_lowercase();
    let matches: Vec<&Model> = available_models
        .iter()
        .filter(|model| {
            model.id.to_lowercase().contains(&normalized)
                || model.name.to_lowercase().contains(&normalized)
        })
        .collect();
    if matches.is_empty() {
        return None;
    }
    let (aliases, dated): (Vec<&Model>, Vec<&Model>) =
        matches.into_iter().partition(|model| is_alias(&model.id));
    let pool = if aliases.is_empty() { dated } else { aliases };
    pool.into_iter().max_by(|a, b| a.id.cmp(&b.id))
}

/// Rebuild an unknown id on a provider template (custom/unlisted models).
#[must_use]
pub fn build_fallback_model(
    provider: &str,
    model_id: &str,
    available_models: &[Model],
) -> Option<Model> {
    let provider_models: Vec<&Model> = available_models
        .iter()
        .filter(|model| model.provider == provider)
        .collect();
    if provider_models.is_empty() {
        return None;
    }
    // Private ids must inherit a private-route template.
    let template = if is_private_prime_inference_model(&Model {
        id: model_id.to_string(),
        provider: provider.to_string(),
        ..wire_skeleton()
    }) {
        provider_models.iter().copied().find(|model| {
            is_private_prime_inference_model(&Model {
                id: model.id.clone(),
                provider: model.provider.clone(),
                ..wire_skeleton()
            })
        })?
    } else {
        let default_id = provider_default_model(provider)?;
        provider_models
            .iter()
            .copied()
            .find(|model| model.id == default_id)
            .unwrap_or(provider_models[0])
    };
    let mut model = template.clone();
    model.id = model_id.to_string();
    model.name = model_id.to_string();
    Some(model)
}

fn wire_skeleton() -> Model {
    serde_json::from_value(serde_json::json!({
        "id": "", "name": "", "api": "openai-completions", "provider": "",
        "baseUrl": "", "reasoning": false, "input": [], "cost": {
            "input": 0, "output": 0, "cacheRead": 0, "cacheWrite": 0
        },
        "contextWindow": 0, "maxTokens": 0
    }))
    .expect("skeleton model serializes")
}

/// Preferred default: the Prime Inference default first, then the default
/// of each provider (the quirks rulebook's `provider_defaults`).
#[must_use]
pub fn find_preferred_default_model(available_models: &[Model]) -> Option<&Model> {
    let prime_default = provider_default_model(PRIME_INFERENCE_PROVIDER_ID);
    if let Some(model) = available_models.iter().find(|model| {
        model.provider == PRIME_INFERENCE_PROVIDER_ID && Some(model.id.as_str()) == prime_default
    }) {
        return Some(model);
    }
    available_models
        .iter()
        .find(|model| provider_default_model(&model.provider) == Some(model.id.as_str()))
}

pub(crate) fn is_valid_thinking_level(value: &str) -> bool {
    matches!(
        value,
        "off" | "minimal" | "low" | "medium" | "high" | "xhigh" | "max"
    )
}

fn parse_thinking_level(value: &str) -> Option<ModelThinkingLevel> {
    match value {
        "off" => Some(ModelThinkingLevel::Off),
        "minimal" => Some(ModelThinkingLevel::Minimal),
        "low" => Some(ModelThinkingLevel::Low),
        "medium" => Some(ModelThinkingLevel::Medium),
        "high" => Some(ModelThinkingLevel::High),
        "xhigh" => Some(ModelThinkingLevel::Xhigh),
        "max" => Some(ModelThinkingLevel::Max),
        _ => None,
    }
}

struct ParsedModelResult<'a> {
    model: Option<&'a Model>,
    thinking_level: Option<ModelThinkingLevel>,
    warning: Option<String>,
}

/// `model:level` parsing; colon-suffixed ids (`OpenRouter` `:exacto`) fall
/// through when the suffix is not a valid level.
fn parse_model_pattern<'a>(
    pattern: &str,
    available_models: &'a [Model],
    strict: bool,
) -> ParsedModelResult<'a> {
    if let Some(exact) = fuzzy_exact(pattern, available_models) {
        return ParsedModelResult {
            model: Some(exact),
            thinking_level: None,
            warning: None,
        };
    }
    let Some(last_colon) = pattern.rfind(':') else {
        return ParsedModelResult {
            model: None,
            thinking_level: None,
            warning: None,
        };
    };
    let prefix = &pattern[..last_colon];
    let suffix = &pattern[last_colon + 1..];
    if is_valid_thinking_level(suffix) {
        let result = parse_model_pattern(prefix, available_models, strict);
        if result.model.is_some() {
            return ParsedModelResult {
                model: result.model,
                thinking_level: Some(parse_thinking_level(suffix).expect("validated")),
                warning: result.warning,
            };
        }
        return result;
    }
    if strict {
        return ParsedModelResult {
            model: None,
            thinking_level: None,
            warning: None,
        };
    }
    let result = parse_model_pattern(prefix, available_models, strict);
    if result.model.is_some() {
        return ParsedModelResult {
            model: result.model,
            thinking_level: None,
            warning: Some(format!(
                "Invalid thinking level \"{suffix}\" in pattern \"{pattern}\". Using default instead."
            )),
        };
    }
    result
}

/// Exact match first, then fuzzy (`tryMatchModel`).
fn fuzzy_exact<'a>(pattern: &str, available_models: &'a [Model]) -> Option<&'a Model> {
    find_exact_model_reference_match(pattern, available_models)
        .or_else(|| fuzzy_match_model(pattern, available_models))
}

/// The models a glob (`?*[]` patterns, globset defaults) matches, as
/// written or lowercased, against provider/id or id; the compiled core
/// decides every model in one call.
fn glob_matching<'a>(pattern: &str, available_models: &'a [Model]) -> Vec<&'a Model> {
    let patterns = [pattern.to_lowercase(), pattern.to_string()];
    let groups: Vec<Vec<String>> = available_models
        .iter()
        .map(|model| vec![format!("{}/{}", model.provider, model.id), model.id.clone()])
        .collect();
    let hits = expect_core(
        Entry::Glob,
        glob::match_groups(GlobOptions::default(), &patterns, &groups),
    );
    available_models
        .iter()
        .zip(hits)
        .filter_map(|(model, hit)| hit.then_some(model))
        .collect()
}

/// Resolve model patterns to scoped models: exact/fuzzy for plain patterns,
/// glob expansion for wildcard patterns; `pattern:level` applies a level.
#[must_use]
pub fn resolve_model_scope_from_models(
    patterns: &[String],
    available_models: &[Model],
) -> Vec<ScopedModel> {
    let mut scoped: Vec<ScopedModel> = Vec::new();
    for pattern in patterns {
        if pattern.contains('*') || pattern.contains('?') || pattern.contains('[') {
            let (glob_pattern, thinking_level) = match pattern.rfind(':') {
                Some(idx) if is_valid_thinking_level(&pattern[idx + 1..]) => {
                    (&pattern[..idx], parse_thinking_level(&pattern[idx + 1..]))
                }
                _ => (pattern.as_str(), None),
            };
            let matching = glob_matching(glob_pattern, available_models);
            if matching.is_empty() {
                eprintln!("Warning: No models match pattern \"{pattern}\"");
                continue;
            }
            for model in matching {
                if !scoped.iter().any(|sm| models_equal(&sm.model, model)) {
                    scoped.push(ScopedModel {
                        model: model.clone(),
                        thinking_level,
                    });
                }
            }
            continue;
        }
        let parsed = parse_model_pattern(pattern, available_models, false);
        if let Some(warning) = &parsed.warning {
            eprintln!("Warning: {warning}");
        }
        let Some(model) = parsed.model else {
            eprintln!("Warning: No models match pattern \"{pattern}\"");
            continue;
        };
        if !scoped.iter().any(|sm| models_equal(&sm.model, model)) {
            scoped.push(ScopedModel {
                model: model.clone(),
                thinking_level: parsed.thinking_level,
            });
        }
    }
    scoped
}

fn models_equal(a: &Model, b: &Model) -> bool {
    a.provider == b.provider && a.id == b.id
}

/// Result of CLI model resolution.
#[derive(Debug, Default)]
pub struct ResolveCliModelResult {
    pub model: Option<Model>,
    pub thinking_level: Option<ModelThinkingLevel>,
    pub warning: Option<String>,
    pub error: Option<String>,
}

/// Resolve one model from `--provider`/`--model` flags against the full
/// catalog (not just auth-configured models).
#[must_use]
pub fn resolve_cli_model(
    cli_provider: Option<&str>,
    cli_model: &str,
    all_models: &[Model],
) -> ResolveCliModelResult {
    let mut result = ResolveCliModelResult::default();
    if all_models.is_empty() {
        result.error = Some(
            "No models available. Check your installation or add models to models.json."
                .to_string(),
        );
        return result;
    }
    let mut provider = None;
    if let Some(cli_provider) = cli_provider {
        let canonical = all_models
            .iter()
            .find(|model| model.provider.to_lowercase() == cli_provider.to_lowercase())
            .map(|model| model.provider.clone());
        if let Some(p) = canonical {
            provider = Some(p);
        } else {
            result.error = Some(format!(
                "Unknown provider \"{cli_provider}\". Use \"eukhe model list\" to see available providers/models."
            ));
            return result;
        }
    }

    let mut pattern = cli_model.to_string();
    let mut inferred_provider = false;
    if provider.is_none() {
        if let Some(slash) = cli_model.find('/') {
            let maybe_provider = &cli_model[..slash];
            let canonical = all_models
                .iter()
                .find(|model| model.provider.to_lowercase() == maybe_provider.to_lowercase())
                .map(|model| model.provider.clone());
            if let Some(p) = canonical {
                provider = Some(p);
                pattern = cli_model[slash + 1..].to_string();
                inferred_provider = true;
            }
        }
    }

    // Exact matches without provider inference (ids that contain slashes).
    if provider.is_none() {
        let lower = cli_model.to_lowercase();
        let exact = all_models
            .iter()
            .find(|model| {
                model.id.to_lowercase() == lower
                    || format!("{}/{}", model.provider, model.id).to_lowercase() == lower
            })
            .cloned();
        if let Some(model) = exact {
            result.model = Some(model);
            return result;
        }
    }

    if let Some(provider) = &provider {
        if cli_provider.is_some() {
            let prefix = format!("{provider}/");
            if pattern.to_lowercase().starts_with(&prefix.to_lowercase()) {
                pattern = pattern[prefix.len()..].to_string();
            }
        }
    }

    let candidates: Vec<&Model> = match &provider {
        Some(provider) => all_models
            .iter()
            .filter(|model| model.provider == *provider)
            .collect(),
        None => all_models.iter().collect(),
    };
    // Scope to the candidate slice for pattern parsing.
    let candidate_refs: Vec<Model> = candidates.into_iter().cloned().collect();
    let parsed = parse_model_pattern(&pattern, &candidate_refs, true);
    if let Some(model) = parsed.model {
        return ResolveCliModelResult {
            model: Some(model.clone()),
            thinking_level: parsed.thinking_level,
            warning: parsed.warning,
            error: None,
        };
    }

    if inferred_provider {
        let lower = cli_model.to_lowercase();
        let exact = all_models
            .iter()
            .find(|model| {
                model.id.to_lowercase() == lower
                    || format!("{}/{}", model.provider, model.id).to_lowercase() == lower
            })
            .cloned();
        if let Some(model) = exact {
            result.model = Some(model);
            return result;
        }
        let fallback = parse_model_pattern(cli_model, all_models, true);
        if fallback.model.is_some() {
            return ResolveCliModelResult {
                model: fallback.model.cloned(),
                thinking_level: fallback.thinking_level,
                warning: fallback.warning,
                error: None,
            };
        }
    }

    if let Some(provider) = &provider {
        if let Some(fallback_model) = build_fallback_model(provider, &pattern, all_models) {
            let fallback_warning = match parsed.warning {
                Some(warning) => format!(
                    "{warning} Model \"{pattern}\" not found for provider \"{provider}\". Using custom model id."
                ),
                None => format!(
                    "Model \"{pattern}\" not found for provider \"{provider}\". Using custom model id."
                ),
            };
            return ResolveCliModelResult {
                model: Some(fallback_model),
                thinking_level: None,
                warning: Some(fallback_warning),
                error: None,
            };
        }
    }

    let display = match &provider {
        Some(provider) => format!("{provider}/{pattern}"),
        None => cli_model.to_string(),
    };
    result.error = Some(format!(
        "Model \"{display}\" not found. Use \"eukhe model list\" to see available models."
    ));
    result
}

/// Provider-failover candidates for `current`: the other providers serving
/// the same model id, in catalog order starting after `current`'s provider,
/// one per provider.
///
/// The list is what the provider-failover loop walks when the current
/// provider exhausts its retries; the caller passes the auth-configured
/// catalog (`ModelRegistry::get_available`) so unconfigured providers never
/// surprise the user with a switch. Rotation keeps the chain stable for
/// every starting provider: with catalog order A, B, C the candidates for
/// B are C then A.
#[must_use]
pub fn failover_candidates(current: &Model, available: &[Model]) -> Vec<Model> {
    // Same model id, other providers: first catalog entry wins per provider.
    let mut candidates: Vec<&Model> = Vec::new();
    for model in available
        .iter()
        .filter(|model| model.id == current.id && model.provider != current.provider)
    {
        if !candidates
            .iter()
            .any(|candidate| candidate.provider == model.provider)
        {
            candidates.push(model);
        }
    }
    // Rotate so the provider after `current` (by catalog position) leads:
    // with catalog order A, B, C the candidates for B are C then A.
    let current_position = available
        .iter()
        .position(|model| model.provider == current.provider);
    if let Some(position) = current_position {
        candidates.sort_by_key(|candidate| {
            let candidate_position = available
                .iter()
                .position(|model| model.provider == candidate.provider)
                .unwrap_or(usize::MAX);
            if candidate_position > position {
                candidate_position
            } else {
                candidate_position + available.len()
            }
        });
    }
    candidates.into_iter().cloned().collect()
}

/// Inputs to the startup-model lookup (TS `findInitialModel`, composed with
/// the `--models`-scope handling from `prepareSessionOptions`).
#[derive(Clone, Copy)]
pub struct InitialModelOptions<'a> {
    /// Explicit `--provider` flag.
    pub cli_provider: Option<&'a str>,
    /// Explicit `--model` flag (a `provider/model` reference is inferred).
    pub cli_model: Option<&'a str>,
    /// Models resolved from `--models` patterns (against the available
    /// catalog, TS `resolveModelScope`).
    pub scoped_models: &'a [ScopedModel],
    /// A continued/resumed session skips the scoped-model step (TS
    /// `isContinuing`).
    pub is_continuing: bool,
    /// Saved default provider (settings `defaultProvider`).
    pub default_provider: Option<&'a str>,
    /// Saved default model id (settings `defaultModel`).
    pub default_model_id: Option<&'a str>,
    /// The full catalog (custom + built-in, auth not filtered).
    pub all_models: &'a [Model],
    /// The auth-configured catalog (TS `refreshAvailableModels`).
    pub available_models: &'a [Model],
}

/// The startup model, in the TS priority order:
/// 1. CLI flags (`--provider` + `--model`, resolved against the full catalog;
///    an unresolved flagged model resolves to `None`, the caller's error)
/// 2. `--provider` alone: that provider's saved default, else its featured
///    default, else its first model — authenticated models first, then the
///    full catalog (an `--api-key` run); an unknown provider resolves to
///    `None`
/// 3. The `--models` scope: the saved default when it is in scope, else the
///    first scoped model (skipped for a continued session)
/// 4. The saved settings default, rebuilt from the provider template when the
///    saved id is missing from the catalog
/// 5. The featured default (prime-inference glm-5.3, then per-provider ids)
/// 6. The first available model.
///
/// `None` past step 2 means no model has credentials; it never falls back
/// to an unauthenticated catalog model.
/// [`initial_model_unavailable_message`] phrases the miss for the caller.
#[must_use]
pub fn find_initial_model(options: &InitialModelOptions<'_>) -> Option<Model> {
    if let (Some(provider), Some(pattern)) = (options.cli_provider, options.cli_model) {
        let resolved = resolve_cli_model(Some(provider), pattern, options.all_models);
        // A flagged model that cannot resolve fails the whole lookup; the
        // caller surfaces the error (TS exits the process at this point).
        return resolved.model;
    }
    if let Some(provider) = options.cli_provider {
        let saved_id = options
            .default_provider
            .filter(|saved| saved.eq_ignore_ascii_case(provider))
            .and(options.default_model_id);
        let provider_model = |models: &[Model]| -> Option<Model> {
            let of_provider: Vec<&Model> = models
                .iter()
                .filter(|model| model.provider.eq_ignore_ascii_case(provider))
                .collect();
            let featured_id = of_provider
                .first()
                .and_then(|model| provider_default_model(&model.provider));
            of_provider
                .iter()
                .find(|model| Some(model.id.as_str()) == saved_id)
                .or_else(|| {
                    of_provider
                        .iter()
                        .find(|model| Some(model.id.as_str()) == featured_id)
                })
                .or_else(|| of_provider.first())
                .map(|model| (*model).clone())
        };
        return provider_model(options.available_models)
            .or_else(|| provider_model(options.all_models));
    }
    if !options.scoped_models.is_empty() && !options.is_continuing {
        let saved_in_scope = options
            .default_provider
            .zip(options.default_model_id)
            .and_then(|(provider, id)| {
                options
                    .scoped_models
                    .iter()
                    .find(|scoped| scoped.model.provider == provider && scoped.model.id == id)
            });
        return saved_in_scope
            .or_else(|| options.scoped_models.first())
            .map(|scoped| scoped.model.clone());
    }
    if let (Some(provider), Some(id)) = (options.default_provider, options.default_model_id) {
        if let Some(found) = options
            .available_models
            .iter()
            .find(|model| model.provider == provider && model.id == id)
        {
            return Some(found.clone());
        }
        // A saved id missing from this build's snapshot survives on the
        // provider template — except private Prime Inference ids, whose
        // template route is authorized per team.
        if !is_private_prime_inference_reference(provider, id) {
            if let Some(rebuilt) = build_fallback_model(provider, id, options.available_models) {
                return Some(rebuilt);
            }
        }
    }
    find_preferred_default_model(options.available_models)
        .cloned()
        .or_else(|| options.available_models.first().cloned())
}

/// Why the saved default model (settings `defaultProvider`/`defaultModel`)
/// cannot be the startup model. The startup chain never moves past the
/// saved default in silence: the caller reports the reason.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum DefaultMiss {
    /// The model catalog has no model with this provider and id.
    NotInCatalog,
    /// The provider of the model has no credentials.
    NoCredentials,
    /// The set `enabledModels` scope does not include the model.
    NotInScope,
}

impl std::fmt::Display for DefaultMiss {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(match self {
            DefaultMiss::NotInCatalog => "the model catalog does not have it",
            DefaultMiss::NoCredentials => "its provider has no credentials",
            DefaultMiss::NotInScope => "the enabledModels setting does not include it",
        })
    }
}

/// What the resolution knows of the saved default model
/// (`bend/default_model.bend` `In`): whether the full catalog has it,
/// whether the catalog with credentials has it, and whether a set
/// `--models` scope (the session is not continuing) leaves it out.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct SavedDefaultFacts {
    pub in_catalog: bool,
    pub has_credentials: bool,
    pub out_of_scope: bool,
}

/// The facts of the saved default of `options`; `None` when nothing is
/// saved. The CLI flags of `options` are not read.
#[must_use]
pub fn saved_default_facts(options: &InitialModelOptions<'_>) -> Option<SavedDefaultFacts> {
    let (provider, id) = options.default_provider.zip(options.default_model_id)?;
    let is_saved = |model: &Model| model.provider == provider && model.id == id;
    Some(SavedDefaultFacts {
        in_catalog: options.all_models.iter().any(is_saved),
        has_credentials: options.available_models.iter().any(is_saved),
        out_of_scope: !options.scoped_models.is_empty()
            && !options.is_continuing
            && !options
                .scoped_models
                .iter()
                .any(|scoped| is_saved(&scoped.model)),
    })
}

/// What the startup chain resolves with no model requested
/// (`bend/default_model.bend` `Res`).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DefaultResolution {
    /// The saved default runs.
    Saved,
    /// The chain's pick without the saved default runs; in place of the
    /// saved default (for this reason) when one is saved.
    Next(Option<DefaultMiss>),
    /// Nothing is saved and no model has credentials.
    Nothing,
    /// The saved default cannot run and no model runs in its place.
    Refused(DefaultMiss),
}

/// The resolution rule (`bend/default_model.bend` `resolve`, run by the
/// compiled core): the saved default's checks in order (the catalog, the
/// credentials, the scope), and whether the chain picks a model without
/// it (`has_next`). A saved default without credentials never gives way
/// to another provider.
///
/// # Panics
///
/// When the compiled core fails or answers out of shape: an inconsistent
/// build ([`eukhe_bend::expect_core`]).
#[must_use]
pub fn resolve_default(saved: Option<SavedDefaultFacts>, has_next: bool) -> DefaultResolution {
    use eukhe_bend::wire::{Reader, WireError, Writer};
    use eukhe_bend::Entry;
    // The model ids are opaque to the rule: the saved default is 0 and
    // the chain's pick 1.
    let resolved = (|| -> Result<DefaultResolution, eukhe_bend::Error> {
        let mut request = Writer::new();
        let facts = match saved {
            None => {
                request.tag(0);
                SavedDefaultFacts {
                    in_catalog: false,
                    has_credentials: false,
                    out_of_scope: false,
                }
            }
            Some(facts) => {
                request.tag(1).nat(0);
                facts
            }
        };
        request
            .bool(facts.in_catalog)
            .bool(facts.has_credentials)
            .bool(facts.out_of_scope);
        if has_next {
            request.tag(1).nat(1);
        } else {
            request.tag(0);
        }
        let reply = eukhe_bend::call(Entry::DefaultModel, &request.finish()?)?;
        let mut reader = Reader::reply(&reply)?;
        let out_of_shape = |expected| WireError::Malformed { at: 0, expected };
        let key = |reader: &mut Reader<'_>| -> Result<DefaultMiss, WireError> {
            reader.nat()?;
            match reader.tag_of(3, "a reason")? {
                0 => Ok(DefaultMiss::NotInCatalog),
                1 => Ok(DefaultMiss::NoCredentials),
                2 => Ok(DefaultMiss::NotInScope),
                _tag => Err(out_of_shape("a reason")),
            }
        };
        let resolution = match reader.tag_of(3, "a resolution")? {
            0 => {
                let saved_runs = reader.tag_of(2, "a pick")? == 0;
                if !saved_runs {
                    reader.nat()?;
                }
                let swapped = reader.tag_of(2, "a substitution")? == 1;
                match (saved_runs, swapped) {
                    (true, false) => DefaultResolution::Saved,
                    (true, true) => return Err(out_of_shape("a resolution").into()),
                    (false, false) => DefaultResolution::Next(None),
                    (false, true) => DefaultResolution::Next(Some(key(&mut reader)?)),
                }
            }
            1 => DefaultResolution::Nothing,
            2 => DefaultResolution::Refused(key(&mut reader)?),
            _tag => return Err(out_of_shape("a resolution").into()),
        };
        reader.end()?;
        Ok(resolution)
    })();
    eukhe_bend::expect_core(Entry::DefaultModel, resolved)
}

/// The first check the saved default of `options` fails, in this order:
/// the full catalog, the catalog with credentials, the `--models` scope
/// (when one is set and the session is not continuing). `None` when
/// nothing is saved or the saved default passes every check. The CLI
/// flags of `options` are not read: callers ask only when no flag picks
/// the model.
#[must_use]
pub fn saved_default_miss(options: &InitialModelOptions<'_>) -> Option<DefaultMiss> {
    match resolve_default(saved_default_facts(options), true) {
        DefaultResolution::Next(miss) => miss,
        DefaultResolution::Refused(miss) => Some(miss),
        DefaultResolution::Saved | DefaultResolution::Nothing => None,
    }
}

/// Why [`find_initial_model`] resolved nothing for `options`, naming the
/// fix: an empty catalog, the flagged model's resolution error, an unknown
/// `--provider`, or no model with credentials.
#[must_use]
pub fn initial_model_unavailable_message(options: &InitialModelOptions<'_>) -> String {
    if options.all_models.is_empty() {
        return "No models available. Check your installation or add models to models.json."
            .to_string();
    }
    match (options.cli_provider, options.cli_model) {
        (Some(provider), Some(pattern)) => {
            resolve_cli_model(Some(provider), pattern, options.all_models)
                .error
                .unwrap_or_else(|| format!("Model \"{provider}/{pattern}\" not found. Use \"eukhe model list\" to see available models."))
        }
        (Some(provider), None) => format!(
            "Unknown provider \"{provider}\". Use \"eukhe model list\" to see available providers/models."
        ),
        (None, Some(_) | None) => "No model has credentials. Run \"eukhe\" and use /login, set the provider's API key environment variable, or pass --model <provider>/<id> with --api-key.".to_string(),
    }
}

/// The private-model predicate without a full `Model` value (TS
/// `isPrivatePrimeInferenceModel({ provider, id })`).
fn is_private_prime_inference_reference(provider: &str, model_id: &str) -> bool {
    provider == "prime-inference"
        && super::prime_inference::is_private_prime_inference_model_id(model_id)
}

#[cfg(test)]
mod tests {
    use super::super::prime_inference::private_prime_inference_models;
    use super::*;

    fn model(provider: &str, id: &str, name: &str) -> Model {
        serde_json::from_value(serde_json::json!({
            "id": id, "name": name, "api": "openai-completions", "provider": provider,
            "baseUrl": "", "reasoning": false, "input": [], "cost": {
                "input": 0, "output": 0, "cacheRead": 0, "cacheWrite": 0
            },
            "contextWindow": 100_000, "maxTokens": 8192
        }))
        .unwrap()
    }

    fn catalog() -> Vec<Model> {
        vec![
            model("anthropic", "claude-sonnet-4-5", "Sonnet"),
            model("anthropic", "claude-sonnet-4-5-20250929", "Sonnet dated"),
            model("prime-inference", "z-ai/glm-5.3", "GLM"),
            model("openrouter", "openai/gpt-4o", "GPT-4o"),
        ]
    }

    #[test]
    fn failover_candidates_order_by_catalog_after_current() {
        let mut catalog = catalog();
        catalog.push(model("zai", "z-ai/glm-5.3", "GLM via zai"));
        catalog.push(model("openrouter", "z-ai/glm-5.3", "GLM via openrouter"));
        // The prime-inference entry (provider at catalog position 2)
        // fails over to the providers after it in catalog order
        // (openrouter's provider first appears at position 3, zai at 4).
        let current = model("prime-inference", "z-ai/glm-5.3", "GLM");
        let candidates = failover_candidates(&current, &catalog);
        assert_eq!(
            candidates
                .iter()
                .map(|model| model.provider.as_str())
                .collect::<Vec<_>>(),
            vec!["openrouter", "zai"]
        );
        // A later provider wraps to the front of the catalog.
        let current = model("openrouter", "z-ai/glm-5.3", "GLM");
        let candidates = failover_candidates(&current, &catalog);
        assert_eq!(
            candidates
                .iter()
                .map(|model| model.provider.as_str())
                .collect::<Vec<_>>(),
            vec!["zai", "prime-inference"]
        );
        // No other provider serves the model: no candidates, no failover.
        let current = model("anthropic", "claude-sonnet-4-5", "Sonnet");
        assert!(failover_candidates(&current, &catalog).is_empty());
        // The current provider itself is never a candidate, even when the
        // catalog carries a second entry for it.
        let current = model("zai", "z-ai/glm-5.3", "GLM");
        let candidates = failover_candidates(&current, &catalog);
        assert!(candidates.iter().all(|model| model.provider != "zai"));
    }

    #[test]
    fn exact_and_fuzzy_matching() {
        let catalog = catalog();
        let exact = find_exact_model_reference_match("anthropic/claude-sonnet-4-5", &catalog);
        assert_eq!(exact.map(|m| m.id.as_str()), Some("claude-sonnet-4-5"));
        // Bare id matches uniquely.
        assert_eq!(
            fuzzy_exact("claude-sonnet", &catalog).map(|m| m.id.as_str()),
            Some("claude-sonnet-4-5")
        );
        // Aliases beat dated versions in fuzzy matching.
        let fuzzy = fuzzy_match_model("claude-sonnet", &catalog);
        assert_eq!(fuzzy.map(|m| m.id.as_str()), Some("claude-sonnet-4-5"));
    }

    #[test]
    fn scoped_patterns_and_thinking_levels() {
        let catalog = catalog();
        let patterns = vec!["claude-sonnet".to_string(), "z-ai/glm-5.3:high".to_string()];
        let scoped = resolve_model_scope_from_models(&patterns, &catalog);
        assert_eq!(scoped.len(), 2);
        assert_eq!(scoped[0].model.id, "claude-sonnet-4-5");
        assert!(scoped[0].thinking_level.is_none());
        assert_eq!(scoped[1].thinking_level, Some(ModelThinkingLevel::High));
    }

    #[test]
    fn cli_provider_model_resolution() {
        let catalog = catalog();
        let resolved = resolve_cli_model(Some("anthropic"), "claude-sonnet-4-5", &catalog);
        assert!(resolved.error.is_none());
        assert_eq!(
            resolved.model.as_ref().map(|m| m.id.as_str()),
            Some("claude-sonnet-4-5")
        );

        let inferred = resolve_cli_model(None, "anthropic/claude-sonnet-4-5", &catalog);
        assert!(inferred.error.is_none());
        assert_eq!(
            inferred.model.as_ref().map(|m| m.provider.as_str()),
            Some("anthropic")
        );

        let unknown = resolve_cli_model(Some("nope"), "x", &catalog);
        assert!(unknown.error.unwrap().contains("Unknown provider"));

        let missing = resolve_cli_model(Some("anthropic"), "missing-model", &catalog);
        // Falls back to the provider template with a warning.
        assert_eq!(
            missing.model.as_ref().map(|m| m.id.as_str()),
            Some("missing-model")
        );
        assert!(missing.warning.unwrap().contains("Using custom model id"));
    }

    #[test]
    fn openrouter_slash_ids_resolve_without_provider_inference() {
        let catalog = catalog();
        let resolved = resolve_cli_model(None, "openai/gpt-4o", &catalog);
        assert!(resolved.error.is_none());
        assert_eq!(
            resolved.model.as_ref().map(|m| m.provider.as_str()),
            Some("openrouter")
        );
    }

    #[test]
    fn fallback_model_prefers_private_template_for_private_ids() {
        let mut catalog = catalog();
        catalog.extend(private_prime_inference_models());
        let fallback = build_fallback_model("prime-inference", "internal/glm-5.9-turbo", &catalog);
        let fallback = fallback.expect("private template exists");
        assert_eq!(fallback.id, "internal/glm-5.9-turbo");
        // Inherited the private template's compat (max_tokens field).
        assert!(fallback.compat.is_some());
        // Inherited the private template's ZERO pricing: an unknown
        // internal id must never bill the public provider default's rate.
        assert_eq!(fallback.cost.input.0, 0.0);
        assert_eq!(fallback.cost.output.0, 0.0);
    }

    /// Port of the TS regression (#2459): Prime Inference rejects
    /// `enable_thinking` with a 400, so a fallback model — public or
    /// private — must never inherit the zai thinking format from its
    /// template.
    #[test]
    fn fallback_models_never_inherit_the_zai_thinking_format() {
        use eukhe_types::ai::{CompatKind, ModelCompat, ThinkingFormat};
        let mut catalog: Vec<Model> = vec![eukhe_models::transports::compiled_models()
            .iter()
            .find(|model| model.provider == "prime-inference" && model.id == "z-ai/glm-5.3")
            .expect("the compiled prime-inference default")
            .clone()];
        catalog.extend(private_prime_inference_models());
        for model_id in ["z-ai/glm-9", "internal/glm-5.9-turbo"] {
            let fallback = build_fallback_model("prime-inference", model_id, &catalog)
                .unwrap_or_else(|| panic!("{model_id} has a fallback template"));
            let Some(Ok(CompatKind::OpenAiCompletions(compat))) =
                fallback.compat.as_ref().map(ModelCompat::kind)
            else {
                panic!("{model_id}: fallback inherits a compat object");
            };
            assert_ne!(
                compat.thinking_format,
                Some(ThinkingFormat::Zai),
                "{model_id}: fallback must not inherit the zai thinking format"
            );
        }
    }

    #[test]
    fn initial_model_prefers_cli_flags() {
        let catalog = catalog();
        let options = InitialModelOptions {
            cli_provider: Some("anthropic"),
            cli_model: Some("claude-sonnet-4-5"),
            scoped_models: &[],
            is_continuing: false,
            default_provider: Some("openrouter"),
            default_model_id: Some("openai/gpt-4o"),
            all_models: &catalog,
            available_models: &catalog,
        };
        let model = find_initial_model(&options).expect("flagged model resolves");
        assert_eq!(model.provider, "anthropic");
        assert_eq!(model.id, "claude-sonnet-4-5");
    }

    #[test]
    fn initial_model_saved_default_wins_over_featured_default() {
        let catalog = catalog();
        let options = InitialModelOptions {
            cli_provider: None,
            cli_model: None,
            scoped_models: &[],
            is_continuing: false,
            default_provider: Some("anthropic"),
            default_model_id: Some("claude-sonnet-4-5"),
            all_models: &catalog,
            available_models: &catalog,
        };
        let model = find_initial_model(&options).expect("saved default resolves");
        assert_eq!(model.provider, "anthropic");
        assert_eq!(model.id, "claude-sonnet-4-5");
    }

    #[test]
    fn initial_model_rebuilds_missing_saved_id_on_template() {
        let catalog = catalog();
        let options = InitialModelOptions {
            cli_provider: None,
            cli_model: None,
            scoped_models: &[],
            is_continuing: false,
            default_provider: Some("anthropic"),
            default_model_id: Some("claude-future-model"),
            all_models: &catalog,
            available_models: &catalog,
        };
        let model = find_initial_model(&options).expect("template rebuild resolves");
        assert_eq!(model.provider, "anthropic");
        assert_eq!(model.id, "claude-future-model");
    }

    #[test]
    fn initial_model_falls_back_to_featured_then_first_available() {
        let catalog = catalog();
        // The featured default (prime-inference glm-5.3) wins when present.
        let options = InitialModelOptions {
            cli_provider: None,
            cli_model: None,
            scoped_models: &[],
            is_continuing: false,
            default_provider: None,
            default_model_id: None,
            all_models: &catalog,
            available_models: &catalog,
        };
        let model = find_initial_model(&options).expect("featured default resolves");
        assert_eq!(model.provider, "prime-inference");
        assert_eq!(model.id, "z-ai/glm-5.3");
        // Without it, the first available model takes over.
        let available: Vec<Model> = catalog
            .iter()
            .filter(|model| model.provider == "anthropic")
            .cloned()
            .collect();
        let fallback = InitialModelOptions {
            available_models: &available,
            ..options
        };
        let model = find_initial_model(&fallback).expect("first available resolves");
        assert_eq!(model.provider, "anthropic");
        assert_eq!(model.id, "claude-sonnet-4-5");
        // An empty available catalog resolves to nothing.
        let empty = InitialModelOptions {
            available_models: &[],
            ..options
        };
        assert_eq!(find_initial_model(&empty), None);
    }

    #[test]
    fn initial_model_scope_prefers_saved_default_in_scope() {
        let catalog = catalog();
        let scoped = resolve_model_scope_from_models(
            &["claude-sonnet".to_string(), "glm".to_string()],
            &catalog,
        );
        let options = InitialModelOptions {
            cli_provider: None,
            cli_model: None,
            scoped_models: &scoped,
            is_continuing: false,
            default_provider: Some("prime-inference"),
            default_model_id: Some("z-ai/glm-5.3"),
            all_models: &catalog,
            available_models: &catalog,
        };
        let model = find_initial_model(&options).expect("scoped model resolves");
        assert_eq!(model.provider, "prime-inference");
        // The saved default is in scope and wins over scoped order.
        assert_eq!(model.id, "z-ai/glm-5.3");
        // A continued session skips the scope entirely.
        let continued = InitialModelOptions {
            is_continuing: true,
            ..options
        };
        let model = find_initial_model(&continued).expect("saved default resolves");
        assert_eq!(model.provider, "prime-inference");
        assert_eq!(model.id, "z-ai/glm-5.3");
    }
}
