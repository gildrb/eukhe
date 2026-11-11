//! The built-in catalog model a models.json model id names: a custom
//! model served through a local server, a proxy or a reseller
//! (`qwen3.8-27b`, `[Kiro] claude-opus-4-8`, `gpt-5.4:cloud`,
//! `vendor/claude-sonnet-4-6-thinking`) takes the limits its definition
//! leaves out from the catalog model of that id.

use std::collections::HashMap;
use std::sync::LazyLock;

use fancy_regex::Regex;

use super::registry::ModelRegistry;

/// The limits of a reference model.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct ReferenceLimits {
    pub(crate) context_window: u64,
    pub(crate) max_tokens: u64,
}

/// The reference index: the reference of each lowercased model id,
/// and of the longest model-like segment after the last `/` of each id.
struct ReferenceIndex {
    exact: HashMap<String, ReferenceLimits>,
    suffix_alias: HashMap<String, ReferenceLimits>,
}

/// Trailing markers a reseller appends without changing the model, each as
/// `-marker` and `:marker`.
const TRAILING_MARKERS: &[&str] = &[
    "customtools",
    "cloud",
    "exacto",
    "nitro",
    "original",
    "optimized",
    "nvfp4",
    "fp8",
    "fp4",
    "bf16",
    "int8",
    "int4",
    "thinking",
    "minimal",
    "low",
    "medium",
    "high",
    "xhigh",
    "free",
    "search",
];

/// Whole suffixes stripped the same way (billing, effort and routing
/// variants).
const TRAILING_SUFFIXES: &[&str] = &[
    "-free",
    "-contributor",
    "-thinking",
    "-extra-high",
    "-none",
    "-minimal",
    "-medium",
    "-xhigh",
    "-high",
    "-low",
    "-max",
    "-wm",
];

/// The prefixes of a model-like segment.
const FAMILY_PREFIXES: &[&str] = &[
    "claude", "gemini", "gpt", "grok", "glm", "qwen", "deepseek", "kimi", "mimo", "doubao",
    "ernie", "gemma", "minimax", "step", "command", "jamba", "llama", "o1", "o3", "o4", "o5",
];

static LEADING_BRACKETED_AFFIX: LazyLock<Regex> = LazyLock::new(|| {
    Regex::new(r"^(?:\s*(?:\[|【)[^\]】]+(?:\]|】)\s*)+").expect("a valid pattern")
});
static TRAILING_BRACKETED_AFFIX: LazyLock<Regex> = LazyLock::new(|| {
    Regex::new(r"(?:\s*(?:\[|【)[^\]】]+(?:\]|】)\s*)+$").expect("a valid pattern")
});

static INDEX: LazyLock<ReferenceIndex> = LazyLock::new(|| {
    build_index(
        ModelRegistry::built_in_catalog_models()
            .iter()
            .map(|model| {
                (
                    model.id.as_str(),
                    limits_of(model.context_window, model.max_tokens),
                )
            }),
    )
});

const fn limits_of(context_window: u64, max_tokens: u64) -> ReferenceLimits {
    ReferenceLimits {
        context_window,
        max_tokens,
    }
}

/// Whether `candidate` replaces `existing` as a reference: the larger
/// window wins, then the larger max; on equal limits the first stays.
fn replaces(existing: Option<&ReferenceLimits>, candidate: ReferenceLimits) -> bool {
    existing.is_none_or(|existing| {
        (candidate.context_window, candidate.max_tokens)
            > (existing.context_window, existing.max_tokens)
    })
}

/// The reference index of `models`: each id exactly, and each id's
/// longest model-like segment after its last `/` as a suffix alias.
fn build_index<'a>(models: impl Iterator<Item = (&'a str, ReferenceLimits)>) -> ReferenceIndex {
    let mut exact: HashMap<String, ReferenceLimits> = HashMap::new();
    let mut suffix_alias: HashMap<String, ReferenceLimits> = HashMap::new();
    let models: Vec<(&str, ReferenceLimits)> = models.collect();
    for (id, limits) in &models {
        let key = id.trim().to_lowercase();
        if replaces(exact.get(&key), *limits) {
            exact.insert(key, *limits);
        }
    }
    for (id, _) in &models {
        let Some((_, suffix)) = id.rsplit_once('/') else {
            continue;
        };
        let (Some(alias), Some(limits)) = (
            model_like_segments(suffix).into_iter().next(),
            exact.get(&id.trim().to_lowercase()),
        ) else {
            continue;
        };
        if replaces(suffix_alias.get(&alias), *limits) {
            suffix_alias.insert(alias, *limits);
        }
    }
    ReferenceIndex {
        exact,
        suffix_alias,
    }
}

/// `value` with its whitespace runs collapsed to single spaces and trimmed.
fn normalize_whitespace(value: &str) -> String {
    value.split_whitespace().collect::<Vec<_>>().join(" ")
}

/// The model-like segments of an id: the runs of `[a-z0-9.:-]` of the
/// lowercased id that start with a model family and hold a digit, longest
/// first (ties: the smaller segment).
fn model_like_segments(model_id: &str) -> Vec<String> {
    let lowered = normalize_whitespace(model_id).to_lowercase();
    let mut segments: Vec<String> = Vec::new();
    for segment in lowered
        .split(|c: char| !(c.is_ascii_lowercase() || c.is_ascii_digit() || ".:-".contains(c)))
    {
        if FAMILY_PREFIXES
            .iter()
            .any(|prefix| segment.starts_with(prefix))
            && segment.bytes().any(|byte| byte.is_ascii_digit())
            && !segments.iter().any(|seen| seen == segment)
        {
            segments.push(segment.to_owned());
        }
    }
    segments.sort_by(|left, right| right.len().cmp(&left.len()).then_with(|| left.cmp(right)));
    segments
}

/// The id without its bracketed affixes (`[Kiro] claude-opus-4-8`), most
/// stripped first.
fn bracket_stripped(model_id: &str) -> Vec<String> {
    if !model_id.contains(['[', ']', '【', '】']) {
        return Vec::new();
    }
    let normalized = normalize_whitespace(model_id);
    let strip = |pattern: &Regex, value: &str| pattern.replace(value, "").into_owned();
    let stripped_leading = strip(&LEADING_BRACKETED_AFFIX, &normalized);
    let mut candidates: Vec<String> = Vec::new();
    for candidate in [
        normalize_whitespace(&strip(&TRAILING_BRACKETED_AFFIX, &stripped_leading)),
        normalize_whitespace(&stripped_leading),
        normalize_whitespace(&strip(&TRAILING_BRACKETED_AFFIX, &normalized)),
    ] {
        if !candidate.is_empty() && candidate != normalized && !candidates.contains(&candidate) {
            candidates.push(candidate);
        }
    }
    candidates
}

/// The id without its longest trailing marker or suffix; `None` when it
/// has none or is nothing else.
fn strip_trailing_marker(candidate: &str) -> Option<&str> {
    let lower = candidate.to_lowercase();
    let marker = TRAILING_MARKERS
        .iter()
        .filter(|marker| {
            lower
                .strip_suffix(*marker)
                .is_some_and(|rest| rest.ends_with(['-', ':']))
        })
        .map(|marker| marker.len() + 1);
    let suffix = TRAILING_SUFFIXES
        .iter()
        .filter(|suffix| lower.ends_with(*suffix))
        .map(|suffix| suffix.len());
    let length = marker.chain(suffix).max()?;
    (length < candidate.len() && candidate.is_char_boundary(candidate.len() - length))
        .then(|| &candidate[..candidate.len() - length])
}

/// The ids a proxied or affixed model id may be catalogued under, least
/// stripped first.
fn candidate_ids(model_id: &str) -> Vec<String> {
    let mut candidates: Vec<String> = Vec::new();
    let mut queue = vec![model_id.to_owned()];
    let mut index = 0;
    while index < queue.len() {
        let candidate = queue[index].trim().to_owned();
        index += 1;
        if candidate.is_empty() || candidates.contains(&candidate) {
            continue;
        }
        queue.extend(bracket_stripped(&candidate));
        queue.extend(model_like_segments(&candidate));
        let lowered = candidate.to_lowercase();
        for suffix in [":cloud", "-cloud"] {
            if lowered.ends_with(suffix)
                && candidate.is_char_boundary(candidate.len() - suffix.len())
            {
                queue.push(candidate[..candidate.len() - suffix.len()].to_owned());
            }
        }
        if let Some((_, bare)) = candidate.rsplit_once('/') {
            queue.push(bare.to_owned());
        }
        if candidate.contains(':') {
            queue.push(candidate.replace(':', "-"));
        }
        if lowered != candidate {
            queue.push(lowered);
        }
        if let Some(stripped) = strip_trailing_marker(&candidate) {
            queue.push(stripped.to_owned());
        }
        candidates.push(candidate);
    }
    candidates
}

/// The limits of the first candidate id of `model_id` that `index` holds,
/// exactly or as a suffix alias.
fn resolve(model_id: &str, index: &ReferenceIndex) -> Option<ReferenceLimits> {
    // A gateway wire id (`@provider/model`) is opaque: stripping it would
    // name an unrelated catalog model.
    if model_id.starts_with('@') {
        return None;
    }
    candidate_ids(model_id).iter().find_map(|candidate| {
        let key = candidate.trim().to_lowercase();
        index
            .exact
            .get(&key)
            .or_else(|| index.suffix_alias.get(&key))
            .copied()
    })
}

/// The limits of the built-in catalog model that `model_id` names; `None`
/// when it names none.
pub(crate) fn limits(model_id: &str) -> Option<ReferenceLimits> {
    resolve(model_id, &INDEX)
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A small catalog: one id under two providers, a namespaced id, and a
    /// marker-suffixed id.
    fn index() -> ReferenceIndex {
        build_index(
            [
                ("claude-opus-4-8", limits_of(200_000, 64_000)),
                ("claude-opus-4-8", limits_of(1_000_000, 128_000)),
                ("qwen/qwen3.8-27b", limits_of(262_144, 65_536)),
                ("alibaba/qwen3.8-27b", limits_of(262_144, 81_920)),
                ("gpt-5.4", limits_of(400_000, 128_000)),
            ]
            .into_iter(),
        )
    }

    /// An id resolves through its affixes to the catalog model with the
    /// largest limits; an opaque gateway id and an unknown id resolve to
    /// nothing.
    #[test]
    fn a_custom_id_takes_the_limits_of_the_catalog_model_it_names() {
        let index = index();
        let resolved = |id: &str| resolve(id, &index);
        assert_eq!(
            [
                resolved("claude-opus-4-8"),
                resolved("[Kiro] claude-opus-4-8"),
                resolved("vendor/Claude-Opus-4-8-thinking"),
                resolved("qwen3.8-27b"),
                resolved("gpt-5.4:cloud"),
                resolved("@modal/gpt-5.4"),
                resolved("my-own-model"),
            ],
            [
                Some(limits_of(1_000_000, 128_000)),
                Some(limits_of(1_000_000, 128_000)),
                Some(limits_of(1_000_000, 128_000)),
                Some(limits_of(262_144, 81_920)),
                Some(limits_of(400_000, 128_000)),
                None,
                None,
            ]
        );
    }
}
