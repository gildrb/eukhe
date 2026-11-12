//! Model identity: classifies a wire model id leniently into `(class,
//! family, revision)`, with an anchored glob matcher for the rule patterns.
//!
//! The rules are `taxonomy.json`, the identity part of the compiled compat
//! rules (`rules.json`, generated from `rules/classes/*.kdl`) at reference
//! commit c28b3e3, extracted with
//!
//! ```text
//! jq '{classes: [.taxonomy.classes[] | .overrides |= map(del(.rationale, .provenance, .expiresAtMs))],
//!      collapse: (.taxonomy.collapse | {effortFamilies, lanes, suffixes})}' rules.json
//! ```
//!
//! Every class is kept: a model only lands in a class when no other class
//! matches it better. Override expiry is dropped because classification
//! here has no observation time, which keeps every override active.
//! Only the lenient path exists: an ambiguous class resolves to `unknown`,
//! an ambiguous family or pattern override to none.

use std::sync::LazyLock;

use serde::Deserialize;

use super::revision::{Revision, parse_revision, parse_revision_prefix};

/// A model's structured identity; `class` is `"unknown"` when no class
/// matches.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct ModelIdentity {
    pub(crate) class: &'static str,
    pub(crate) family: Option<&'static str>,
    pub(crate) revision: Option<Revision>,
}

pub(crate) const UNKNOWN_CLASS: &str = "unknown";

#[derive(Deserialize)]
struct Rules {
    classes: Vec<Class>,
    collapse: Collapse,
}

#[derive(Deserialize)]
#[serde(rename_all = "camelCase")]
struct Class {
    id: String,
    matchers: Vec<Matcher>,
    families: Vec<Family>,
    revision_prefixes: Vec<RevisionPrefix>,
    skip_bare: Vec<String>,
    overrides: Vec<IdentityOverride>,
}

#[derive(Clone, Copy, Deserialize)]
#[serde(rename_all = "lowercase")]
enum MatcherKind {
    Exact,
    Bounded,
    Namespace,
    Prefix,
    Glob,
}

impl MatcherKind {
    /// `exact(4) > bounded(3) > namespace(2) > prefix(1) > glob(0)`.
    const fn rank(self) -> usize {
        match self {
            Self::Exact => 4,
            Self::Bounded => 3,
            Self::Namespace => 2,
            Self::Prefix => 1,
            Self::Glob => 0,
        }
    }
}

#[derive(Deserialize)]
struct Matcher {
    kind: MatcherKind,
    token: String,
    #[serde(default)]
    bounded: bool,
}

#[derive(Deserialize)]
struct Family {
    id: String,
    glob: String,
    priority: i32,
}

#[derive(Deserialize)]
struct RevisionPrefix {
    prefix: String,
    #[serde(default)]
    anywhere: bool,
}

#[derive(Deserialize)]
struct IdentityOverride {
    /// Exact (case-insensitive) bare model id; otherwise `glob` applies.
    model: Option<String>,
    glob: Option<String>,
    provider: Option<String>,
    logical: Option<String>,
    class: Option<String>,
    family: Option<String>,
    revision: Option<String>,
}

#[derive(Deserialize)]
#[serde(rename_all = "camelCase")]
struct Collapse {
    effort_families: Vec<EffortFamily>,
    lanes: Vec<Lane>,
    suffixes: Vec<SuffixRule>,
}

#[derive(Deserialize)]
struct EffortFamily {
    provider: String,
    logical: String,
    aliases: Vec<String>,
}

#[derive(Deserialize)]
#[serde(rename_all = "camelCase")]
struct Lane {
    suffix: String,
    providers: Vec<String>,
    bare_prefix: Option<String>,
}

#[derive(Deserialize)]
#[serde(rename_all = "camelCase")]
struct SuffixRule {
    suffix: String,
    /// The effort tier the suffix names; only its presence matters here.
    effort: Option<String>,
    /// The suffix marks a thinking variant (`X-thinking` of `X`).
    #[serde(default)]
    thinking: bool,
    except_bare_prefix: Option<String>,
}

static RULES: LazyLock<Rules> = LazyLock::new(|| {
    serde_json::from_str(include_str!("taxonomy.json"))
        .expect("taxonomy.json is the checked-in model identity rule set")
});

/// The part of an id after its last `/`.
pub(crate) fn bare_of(id: &str) -> &str {
    id.rfind('/').map_or(id, |slash| &id[slash + 1..])
}

/// Anchored `*`-wildcard match: `*` spans any substring, the literal text
/// stays anchored in order. Both sides are pre-lowercased.
pub(crate) fn glob_match(pattern: &str, value: &str) -> bool {
    let Some((head, rest)) = pattern.split_once('*') else {
        return value == pattern;
    };
    let Some(mut remainder) = value.strip_prefix(head) else {
        return false;
    };
    let (middle, last) = rest.rsplit_once('*').unwrap_or(("", rest));
    for segment in middle.split('*').filter(|segment| !segment.is_empty()) {
        let Some(found) = remainder.find(segment) else {
            return false;
        };
        remainder = &remainder[found + segment.len()..];
    }
    last.is_empty() || remainder.ends_with(last)
}

/// `value` is `token`, or starts with it followed by `-`, `_`, `.`, `:` or a
/// digit.
fn bounded_match(value: &str, token: &str) -> bool {
    value == token
        || value.strip_prefix(token).is_some_and(|tail| {
            tail.bytes()
                .next()
                .is_some_and(|next| matches!(next, b'-' | b'_' | b'.' | b':' | b'0'..=b'9'))
        })
}

fn matcher_matches(matcher: &Matcher, lower: &str, bare: &str) -> bool {
    match matcher.kind {
        MatcherKind::Exact => bare == matcher.token,
        MatcherKind::Bounded => bounded_match(bare, &matcher.token),
        MatcherKind::Namespace => {
            let separators: &[char] = if matcher.bounded {
                &['/', '.', ':']
            } else {
                &['/']
            };
            lower
                .split(separators)
                .filter(|part| !part.is_empty())
                .any(|part| {
                    if matcher.bounded {
                        bounded_match(part, &matcher.token)
                    } else {
                        part == matcher.token
                    }
                })
        }
        MatcherKind::Prefix => bare.starts_with(matcher.token.as_str()),
        MatcherKind::Glob => glob_match(&matcher.token, bare),
    }
}

fn non_wildcard_bytes(glob: &str) -> usize {
    glob.bytes().filter(|&byte| byte != b'*').count()
}

/// The best-ranked family whose glob matches `subject`, unless two
/// different families tie for it.
fn rank_families(class: &'static Class, subject: &str) -> Result<Option<&'static str>, ()> {
    let mut winner: Option<((i32, usize), &'static str)> = None;
    let mut tied = false;
    for family in &class.families {
        if !glob_match(&family.glob, subject) {
            continue;
        }
        let rank = (family.priority, non_wildcard_bytes(&family.glob));
        match winner {
            Some((held, id)) if held == rank && id != family.id => tied = true,
            Some((held, _)) if held >= rank => {}
            _ => {
                winner = Some((rank, family.id.as_str()));
                tied = false;
            }
        }
    }
    if tied {
        Err(())
    } else {
        Ok(winner.map(|(_, id)| id))
    }
}

/// A Bedrock-style `vendor.model` id with the class namespace stripped.
fn strip_class_namespace<'a>(class: &Class, bare: &'a str) -> Option<&'a str> {
    let separator = bare.find(['.', ':'])?;
    if separator == 0 || separator == bare.len() - 1 {
        return None;
    }
    let namespace = &bare[..separator];
    class
        .matchers
        .iter()
        .any(|matcher| matcher.token == namespace)
        .then(|| &bare[separator + 1..])
}

fn classify_family(class: &'static Class, bare: &str) -> Option<&'static str> {
    if let Ok(family) = rank_families(class, bare) {
        return family;
    }
    // A Bedrock-style `vendor.model` id names the product after the class
    // namespace; only ambiguities are rescored.
    strip_class_namespace(class, bare)
        .and_then(|scoped| rank_families(class, scoped).ok().flatten())
}

fn extract_revision(class: &Class, bare: &str) -> Option<Revision> {
    if class.skip_bare.iter().any(|skip| skip == bare) {
        return None;
    }
    for rule in &class.revision_prefixes {
        let tail = if rule.anywhere {
            bare.find(rule.prefix.as_str())
                .map(|start| &bare[start + rule.prefix.len()..])
        } else {
            bare.strip_prefix(rule.prefix.as_str())
        };
        let Some(tail) = tail else {
            continue;
        };
        let digit = tail.find(|c: char| c.is_ascii_digit())?;
        // The parsed triple is the revision; formatting and reparsing it
        // would give the same one.
        return parse_revision_prefix(&tail[digit..]);
    }
    None
}

fn find_class(id: &str) -> Option<&'static Class> {
    RULES.classes.iter().find(|class| class.id == id)
}

fn unknown() -> ModelIdentity {
    ModelIdentity {
        class: UNKNOWN_CLASS,
        family: None,
        revision: None,
    }
}

/// Class, family and revision ranks of a logical id.
fn classify_ranks(model: &str) -> ModelIdentity {
    let lower = model.trim().to_lowercase();
    let bare = bare_of(&lower);
    let mut winner: Option<((usize, usize), &'static Class)> = None;
    let mut tied = false;
    for class in &RULES.classes {
        for matcher in &class.matchers {
            if !matcher_matches(matcher, &lower, bare) {
                continue;
            }
            let rank = (matcher.kind.rank(), matcher.token.len());
            match winner {
                Some((held, holder)) if held == rank && holder.id != class.id => tied = true,
                Some((held, _)) if held >= rank => {}
                _ => {
                    winner = Some((rank, class));
                    tied = false;
                }
            }
        }
    }
    match winner {
        Some((_, class)) if !tied => ModelIdentity {
            class: class.id.as_str(),
            family: classify_family(class, bare),
            revision: extract_revision(class, bare),
        },
        _ => unknown(),
    }
}

/// Family and revision of `model` inside the class `class_id`.
fn ranks_in_class(class_id: &str, model: &str) -> (Option<&'static str>, Option<Revision>) {
    let Some(class) = find_class(class_id) else {
        return (None, None);
    };
    let lower = model.trim().to_lowercase();
    let bare = bare_of(&lower);
    (classify_family(class, bare), extract_revision(class, bare))
}

/// The best pattern override scoped to `provider` (`None`: unscoped ones),
/// `Err` when two tie.
fn rank_pattern_overrides(
    provider: Option<&str>,
    bare_model: &str,
) -> Result<Option<&'static IdentityOverride>, ()> {
    let mut winner: Option<(usize, &'static IdentityOverride)> = None;
    let mut tied = false;
    let patterns = RULES
        .classes
        .iter()
        .flat_map(|class| &class.overrides)
        .filter_map(|o| o.model.is_none().then_some(o).zip(o.glob.as_deref()));
    for (candidate, glob) in patterns {
        let scope = candidate.provider.as_deref().map(str::to_lowercase);
        if scope.as_deref() != provider || !glob_match(glob, bare_model) {
            continue;
        }
        let specificity = non_wildcard_bytes(glob);
        match winner {
            Some((held, _)) if held == specificity => tied = true,
            Some((held, _)) if held > specificity => {}
            _ => {
                winner = Some((specificity, candidate));
                tied = false;
            }
        }
    }
    if tied {
        Err(())
    } else {
        Ok(winner.map(|(_, candidate)| candidate))
    }
}

/// The reviewed identity override for a bare wire id: exact model first
/// (provider-scoped, then unscoped), then the most specific glob (scoped,
/// else unscoped).
fn find_identity_override(provider: &str, bare_model: &str) -> Option<&'static IdentityOverride> {
    let lower_provider = provider.to_lowercase();
    let lower_bare = bare_model.to_lowercase();
    let exact = || {
        RULES
            .classes
            .iter()
            .flat_map(|class| &class.overrides)
            .filter(|o| {
                o.model
                    .as_deref()
                    .is_some_and(|m| m.to_lowercase() == lower_bare)
            })
    };
    // The first declaration wins within each bucket.
    let scoped = exact().find(|o| {
        o.provider
            .as_deref()
            .is_some_and(|p| p.to_lowercase() == lower_provider)
    });
    if let Some(found) = scoped.or_else(|| exact().find(|o| o.provider.is_none())) {
        return Some(found);
    }
    match rank_pattern_overrides(Some(&lower_provider), &lower_bare) {
        Ok(None) => rank_pattern_overrides(None, &lower_bare).ok().flatten(),
        ranked => ranked.ok().flatten(),
    }
}

/// The longest declared suffix `subject` (a lowercased id) ends in, effort
/// suffixes only when `effort_only`; the first of equally long ones wins.
fn longest_suffix_rule(subject: &str, effort_only: bool) -> Option<&'static SuffixRule> {
    let subject_bare = bare_of(subject);
    RULES
        .collapse
        .suffixes
        .iter()
        .filter(|rule| !effort_only || rule.effort.is_some())
        .filter(|rule| subject.ends_with(rule.suffix.as_str()))
        .filter(|rule| {
            rule.except_bare_prefix
                .as_deref()
                .is_none_or(|except| !subject_bare.starts_with(except))
        })
        .fold(None, |best: Option<&SuffixRule>, rule| match best {
            Some(held) if held.suffix.len() >= rule.suffix.len() => Some(held),
            _ => Some(rule),
        })
}

/// The reviewed effort family that lists `lower` (a lowercased id) as an
/// alias on `lower_provider`.
fn effort_family(lower_provider: &str, lower: &str) -> Option<&'static EffortFamily> {
    RULES.collapse.effort_families.iter().find(|family| {
        family.provider == lower_provider && family.aliases.iter().any(|alias| alias == lower)
    })
}

/// `model` up to byte `end` of its lowercased form; a non-ASCII id whose
/// lowercase changes length falls back to the lowercased bytes.
fn id_prefix<'a>(model: &'a str, lower: &str, end: usize) -> std::borrow::Cow<'a, str> {
    use std::borrow::Cow;
    model
        .get(..end)
        .filter(|_| model.len() == lower.len())
        .map_or_else(|| Cow::Owned(lower[..end].to_owned()), Cow::Borrowed)
}

/// The logical model a thinking-variant id names: `X` for `X-thinking`
/// when the longest declared suffix of the id marks a thinking variant.
/// `None` for a reviewed effort-family alias, an effort suffix or no
/// suffix. A selector naming a retired thinking variant resolves to it.
#[must_use]
pub fn thinking_variant_logical_id<'a>(
    provider: &str,
    model: &'a str,
) -> Option<std::borrow::Cow<'a, str>> {
    let lower = model.to_lowercase();
    if effort_family(&provider.to_lowercase(), &lower).is_some() {
        return None;
    }
    let rule = longest_suffix_rule(&lower, false).filter(|rule| rule.thinking)?;
    Some(id_prefix(model, &lower, lower.len() - rule.suffix.len()))
}

/// The logical id after collapsing a declared thinking or effort suffix
/// (the effort it names does not change identity).
fn collapse_variant_id<'a>(provider: &str, model: &'a str) -> std::borrow::Cow<'a, str> {
    use std::borrow::Cow;
    let collapse = &RULES.collapse;
    let lower = model.to_lowercase();
    let lower_provider = provider.to_lowercase();
    if let Some(family) = effort_family(&lower_provider, &lower) {
        return Cow::Owned(family.logical.clone());
    }
    let prefix = |end: usize| id_prefix(model, &lower, end);
    if let Some(rule) = longest_suffix_rule(&lower, false) {
        return prefix(lower.len() - rule.suffix.len());
    }
    for lane in &collapse.lanes {
        if !lane.providers.contains(&lower_provider) || !lower.ends_with(lane.suffix.as_str()) {
            continue;
        }
        let trimmed = &lower[..lower.len() - lane.suffix.len()];
        if lane
            .bare_prefix
            .as_deref()
            .is_some_and(|bare_prefix| !bare_of(trimmed).starts_with(bare_prefix))
        {
            continue;
        }
        // The lane wraps effort tiers only; thinking variants never lane.
        let Some(rule) = longest_suffix_rule(trimmed, true) else {
            continue;
        };
        let base = prefix(trimmed.len() - rule.suffix.len());
        if base.is_empty() || base.ends_with('/') {
            continue;
        }
        let lane_tail = model
            .get(trimmed.len()..)
            .unwrap_or(&lower[trimmed.len()..]);
        return Cow::Owned(format!("{base}{lane_tail}"));
    }
    Cow::Borrowed(model)
}

/// Lenient classification of `model_id` on `provider`: reviewed
/// override first, then suffix collapse, then class/family/revision ranks
/// over the logical id.
pub(crate) fn classify_model(provider: &str, model_id: &str) -> ModelIdentity {
    let trimmed = model_id.trim();
    if let Some(found) = find_identity_override(provider, bare_of(trimmed)) {
        let logical = found.logical.as_deref().unwrap_or(trimmed);
        let class = match found.class.as_deref() {
            Some(class) => find_class(class).map_or(UNKNOWN_CLASS, |class| class.id.as_str()),
            None => classify_ranks(logical).class,
        };
        let (family, revision) = ranks_in_class(class, logical);
        return ModelIdentity {
            class,
            family: found.family.as_deref().or(family),
            revision: match found.revision.as_deref() {
                // An unparsable pinned revision compares like an absent one.
                Some(pinned) => parse_revision(pinned),
                None => revision,
            },
        };
    }
    if trimmed.len() == model_id.len() {
        classify_ranks(&collapse_variant_id(provider, trimmed))
    } else {
        classify_ranks(trimmed)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn identity(
        class: &'static str,
        family: Option<&'static str>,
        revision: Option<Revision>,
    ) -> ModelIdentity {
        ModelIdentity {
            class,
            family,
            revision,
        }
    }

    // Identity cases (the logical id, effort and thinking-variant facts are
    // not kept here).
    #[test]
    fn extracts_dashed_revisions_and_classifies_namespaced_ids_by_bare_name() {
        let opus = identity("anthropic", Some("opus"), Some([4, 6, 0]));
        assert_eq!(classify_model("anthropic", "claude-opus-4-6"), opus);
        assert_eq!(
            classify_model("openrouter", "anthropic/claude-opus-4-6"),
            opus
        );
    }

    #[test]
    fn class_namespace_does_not_compete_with_the_product_family() {
        assert_eq!(
            classify_model("litellm", "mistral.mixtral-8x7b-instruct-v0:1"),
            identity("mistral", Some("mixtral"), None)
        );
        assert_eq!(
            classify_model("litellm", "mistral.mistral-large-2402-v1:0"),
            identity("mistral", Some("mistral"), None)
        );
    }

    #[test]
    fn bare_o_series_names_carry_no_revision() {
        assert_eq!(
            classify_model("openai", "o3"),
            identity("openai", Some("o-series"), None)
        );
        assert_eq!(
            classify_model("openai", "o3-mini"),
            identity("openai", Some("o-series"), Some([3, 0, 0]))
        );
    }

    #[test]
    fn deepseek_v4_revisions_ignore_suffixes_and_flash_aliases_resolve_to_v4_1() {
        let flash = |revision| identity("deepseek", Some("flash"), revision);
        assert_eq!(
            classify_model("opencode-zen", "deepseek-v4-flash-free"),
            flash(Some([4, 0, 0]))
        );
        assert_eq!(
            classify_model("openrouter", "deepseek/deepseek-v4-flash-0731"),
            flash(Some([4, 0, 0]))
        );
        assert_eq!(
            classify_model("cline-pass", "deepseek-v4.1-flash"),
            flash(Some([4, 1, 0]))
        );
        for provider in ["deepseek", "opencode-go"] {
            assert_eq!(
                classify_model(provider, "deepseek-flash"),
                flash(Some([4, 1, 0]))
            );
        }
        assert_eq!(classify_model("custom", "deepseek-flash"), flash(None));
        assert_eq!(
            classify_model("deepseek", "deepseek-r1"),
            identity("deepseek", Some("r1"), None)
        );
    }

    #[test]
    fn bounded_matchers_do_not_fire_on_substrings() {
        assert_eq!(
            classify_model("test", "anthropicology").class,
            UNKNOWN_CLASS
        );
        assert_eq!(classify_model("test", "deepseeker").class, UNKNOWN_CLASS);
    }

    #[test]
    fn gpt_oss_outranks_the_gpt_prefix() {
        assert_eq!(classify_model("openai", "gpt-oss-120b").class, "gpt-oss");
    }

    #[test]
    fn zai_vendor_prefixed_bare_ids_classify_as_glm() {
        assert_eq!(
            classify_model("mistral", "zai-glm-5-2"),
            identity("glm", None, Some([5, 2, 0]))
        );
        assert_eq!(
            classify_model("cerebras", "zai-glm-4.7"),
            identity("glm", None, Some([4, 7, 0]))
        );
    }

    #[test]
    fn kimi_k3_skus_and_selectors_retain_k3_identity() {
        let k3 = identity("kimi", Some("k3"), None);
        for (provider, model) in [
            ("", "k3"),
            ("", "kimi-code/k3"),
            ("", "kimi-coding/k3"),
            ("kimi-code", "k3"),
            ("kimi-coding", "K3"),
            ("", "k3-256k"),
            ("", "K3-256K"),
            ("", "kimi-code/k3-256k"),
            ("", "kimi-coding/K3-256K"),
            ("kimi-code", "k3-256k"),
            ("kimi-coding", "K3-256K"),
        ] {
            assert_eq!(classify_model(provider, model), k3, "{provider}/{model}");
        }
        for (provider, model) in [
            ("", "k3.1-pro"),
            ("kimi-code", "k3.1-pro"),
            ("kimi-code", "k3.1-pro-highspeed"),
        ] {
            assert_eq!(
                classify_model(provider, model),
                identity("kimi", Some("k3"), Some([3, 1, 0])),
                "{provider}/{model}"
            );
        }
        for model in [
            "k30",
            "k3-custom",
            "k3anthropic",
            "k3-256",
            "k3-256kb",
            "k3-256k-custom",
            "kimi-code/k3-256kb",
        ] {
            assert_eq!(
                classify_model("", model),
                identity(UNKNOWN_CLASS, None, None),
                "{model}"
            );
        }
        assert_eq!(classify_model("moonshot", "kimi-k3"), k3);
    }

    #[test]
    fn variant_suffixes_collapse_to_the_logical_id() {
        assert_eq!(
            collapse_variant_id("vercel-ai-gateway", "glm-4.6-thinking"),
            "glm-4.6"
        );
        assert_eq!(
            classify_model("vercel-ai-gateway", "glm-4.6-thinking").class,
            "glm"
        );
        // qwen3.6-max is a product SKU, not an effort variant.
        assert_eq!(
            collapse_variant_id("alibaba-token-plan", "qwen3.6-max"),
            "qwen3.6-max"
        );
        assert_eq!(collapse_variant_id("openai", "gpt-5.5-High"), "gpt-5.5");
        // Cursor's effort lane: the effort sits before the `-fast` lane token.
        assert_eq!(
            collapse_variant_id("cursor", "gpt-5.5-high-fast"),
            "gpt-5.5-fast"
        );
        assert_eq!(
            collapse_variant_id("openai", "gpt-5.5-high-fast"),
            "gpt-5.5-high-fast"
        );
    }

    /// Only a thinking suffix names a thinking variant; the logical id
    /// keeps the selector's spelling.
    #[test]
    fn thinking_variants_name_their_logical_model() {
        assert_eq!(
            thinking_variant_logical_id("vercel-ai-gateway", "alibaba/Qwen3-Max-Thinking")
                .as_deref(),
            Some("alibaba/Qwen3-Max")
        );
        assert_eq!(thinking_variant_logical_id("openai", "gpt-5.5-high"), None);
        assert_eq!(
            thinking_variant_logical_id("vercel-ai-gateway", "alibaba/qwen3-max"),
            None
        );
    }

    #[test]
    fn reviewed_overrides_pin_identity() {
        assert_eq!(
            classify_model("openai", "daybreak-blue-latest"),
            identity(UNKNOWN_CLASS, None, Some([5, 6, 0]))
        );
        assert_eq!(
            classify_model("openai", "gpt-daybreak-blue-latest").revision,
            Some([5, 6, 0])
        );
        assert_eq!(classify_model("kilo", "qwq-32b").class, "qwen");
        for (model, revision) in [
            ("Bonsai-27B", [3, 6, 0]),
            ("PrismML/Ternary-Bonsai-27B-q2_0", [3, 6, 0]),
            ("local/prefix-Ternary-BONSAI-2-27B-Q5_K_S.gguf", [3, 8, 0]),
        ] {
            assert_eq!(
                classify_model("custom-local", model),
                identity("qwen", None, Some(revision))
            );
        }
        for model in [
            "bonsai-270b",
            "bonsai-2-270b",
            "ternary-bonsai-270b-q4_k_m.gguf",
            "namespace/bonsai-7b",
        ] {
            assert_eq!(
                classify_model("llama.cpp", model),
                identity(UNKNOWN_CLASS, None, None),
                "{model}"
            );
        }
    }

    #[test]
    fn bedrock_dotted_ids_keep_their_vendor() {
        for id in ["us.xai.grok-4.6", "global.xai.grok-4.6", "xai.grok-4.6"] {
            assert_eq!(
                classify_model("amazon-bedrock", id),
                identity("xai", Some("grok"), Some([4, 6, 0])),
                "{id}"
            );
        }
        assert_eq!(
            classify_model("sambanova", "Meta-Llama-3.3-70B-Instruct"),
            identity("meta", Some("llama"), None)
        );
    }

    #[test]
    fn glob_matching_is_anchored() {
        assert!(glob_match("*opus*", "claude-opus-4-6"));
        assert!(glob_match("gpt-*", "gpt-5"));
        assert!(!glob_match("gpt-*", "chatgpt-5"));
        assert!(glob_match("o1", "o1"));
        assert!(!glob_match("o1", "o1-mini"));
        assert!(glob_match("*k3.1-pro", "kimi-k3.1-pro"));
        assert!(!glob_match("*k3.1-pro", "k3.1-pro-highspeed"));
        assert!(glob_match("a*b*c", "abc"));
        assert!(!glob_match("a*bc*c", "abc"));
    }
}
