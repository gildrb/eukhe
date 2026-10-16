use crate::fuzzy::FuzzyQuery;
use eukhe_types::ai::Model;
/// Match quality for the scored search (TS `ModelSearchMatchQuality`;
/// lower sorts first).
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub(super) enum MatchQuality {
    ExactShortId,
    ExactFullId,
    PrefixOrToken,
    Fuzzy,
}

/// One scored search match.
pub(super) struct SearchMatch {
    pub(super) quality: MatchQuality,
    pub(super) score: f64,
}

/// TS `normalizeModelSearchText`: lowercase, drop separator runs.
fn normalize_search_text(value: &str) -> Vec<char> {
    value
        .to_lowercase()
        .chars()
        .filter(|c| !matches!(c, ' ' | '\t' | '-' | '_' | '.' | ':' | '/'))
        .collect()
}

/// One model's normalized search fields (TS `getModelSearchFields`),
/// built once per catalog load so a keystroke only scores.
#[derive(Debug)]
pub(super) struct SearchFields {
    /// The short id, the id, `provider/id`, the name, and the provider.
    fields: [Vec<char>; 5],
    /// Every field's `' '`/`'/'`/`'_'`/`'-'` pieces, non-empty.
    tokens: Vec<Vec<char>>,
}

impl SearchFields {
    pub(super) fn new(model: &Model) -> Self {
        let short_id = model.id.rsplit('/').next().unwrap_or(&model.id);
        let full_id = format!("{}/{}", model.provider, model.id);
        let raw = [
            short_id,
            model.id.as_str(),
            full_id.as_str(),
            model.name.as_str(),
            model.provider.as_str(),
        ];
        SearchFields {
            fields: raw.map(normalize_search_text),
            tokens: raw
                .iter()
                .flat_map(|field| field.split([' ', '/', '_', '-']).map(normalize_search_text))
                .filter(|token| !token.is_empty())
                .collect(),
        }
    }
}

/// A normalized search query, built once per keystroke.
pub(super) struct SearchQuery {
    normalized: Vec<char>,
    tokens: Vec<FuzzyQuery>,
}

impl SearchQuery {
    /// `None` when nothing searchable remains after normalization.
    pub(super) fn new(query: &str) -> Option<Self> {
        let normalized = normalize_search_text(query);
        let tokens: Vec<FuzzyQuery> = query
            .split_whitespace()
            .map(normalize_search_text)
            .filter(|token| !token.is_empty())
            .map(FuzzyQuery::new)
            .collect();
        (!normalized.is_empty() && !tokens.is_empty()).then_some(SearchQuery { normalized, tokens })
    }
}

/// TS `scoreModelSearch`.
pub(super) fn score_model_search(
    fields: &SearchFields,
    query: &SearchQuery,
) -> Option<SearchMatch> {
    let [short_id, id, full_id, ..] = &fields.fields;
    if *short_id == query.normalized {
        return Some(SearchMatch {
            quality: MatchQuality::ExactShortId,
            score: 0.0,
        });
    }
    if *id == query.normalized || *full_id == query.normalized {
        return Some(SearchMatch {
            quality: MatchQuality::ExactFullId,
            score: 0.0,
        });
    }
    // TS `getBestFuzzyScore`: every token must fuzzy-match some field;
    // the score is the sum of each token's best field.
    let mut score = 0.0;
    for token in &query.tokens {
        score += fields
            .fields
            .iter()
            .filter_map(|field| token.score(field))
            .reduce(f64::min)?;
    }
    let is_prefix_or_token = query.tokens.iter().all(|token| {
        let token = token.chars();
        fields.fields.iter().any(|field| field.starts_with(token))
            || fields.tokens.iter().any(|field| field.starts_with(token))
    });
    Some(SearchMatch {
        quality: if is_prefix_or_token {
            MatchQuality::PrefixOrToken
        } else {
            MatchQuality::Fuzzy
        },
        score,
    })
}
