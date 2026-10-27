//! Outbound anonymization (`privacy.anonymizeRemote`): when the session's
//! model sits behind a non-loopback endpoint, every text the request
//! carries is scrubbed first.
//!
//! Two kinds of pseudonym:
//!
//! - Mapped (`CLASS_<n>`, one index space per class): the phrases of
//!   `privacy.terms` (free-text names, `PERSON`), home-dir names
//!   (`HOME`), emails (`EMAIL`), whole absolute paths (`PATH`) and
//!   domains (`DOMAIN`). The map is in memory and append-only: the same
//!   original keeps its index for the daemon's life, and
//!   [`Scrubber::unredact`] maps a token back, so a remote model's tool
//!   call that names `PATH_3` executes against the real path. The chat
//!   memory in `~/.eukhe` is never touched - the scrub runs on the
//!   outbound copy only.
//! - Hashed (`CLASS_<6 hex of the value's SHA-256>`, irreversible): API
//!   keys and tokens, PEM blocks, IBANs, government IDs, phone numbers,
//!   IP addresses, credit cards. What must never come back is hashed;
//!   what a tool may need back is mapped.
//!
//! This is content rewriting on the request path (string in, string
//! out), not decision logic: it stays Rust on purpose. Patterns use
//! `regex-lite` (no look-around). A match that already holds a
//! pseudonym token is left alone, so scrubbing scrubbed text changes
//! nothing.

use eukhe_types::pi_ai::{
    AssistantContentBlock, Message, SystemContent, UserContent, UserContentBlock,
};
use sha2::{Digest, Sha256};
use std::sync::{LazyLock, Mutex};

/// Whether the model's endpoint leaves the machine: loopback hosts
/// (`localhost`, `127.0.0.0/8`, `::1`) are local, everything else is
/// remote.
#[must_use]
pub fn is_local(base_url: &str) -> bool {
    let rest = base_url
        .split_once("://")
        .map_or(base_url, |(_, rest)| rest);
    let authority = rest.split(['/', '?', '#']).next().unwrap_or(rest);
    let host = authority
        .rsplit_once('@')
        .map_or(authority, |(_, host)| host);
    // A bracketed IPv6 keeps its brackets through the port strip.
    let host = if let Some(inner) = host.strip_prefix('[') {
        inner.split(']').next().unwrap_or(inner)
    } else {
        host.split(':').next().unwrap_or(host)
    };
    let host = host.to_ascii_lowercase();
    host == "localhost" || host.starts_with("127.") || host == "::1"
}

/// A stable hashed pseudonym for `value` in `class`: `CLASS_<6 hex>`.
fn pseudonym(class: &str, value: &str) -> String {
    let digest = Sha256::digest(value.as_bytes());
    format!(
        "{}_{:02x}{:02x}{:02x}",
        class, digest[0], digest[1], digest[2]
    )
}

// The mapped classes
// ------------------

/// One mapped assignment: a class, the original, its index.
struct Mapping {
    class: &'static str,
    original: String,
    index: u32,
}

/// The in-memory map of the mapped classes: append-only, one index space
/// per class, stable for the daemon's life.
static MAP: LazyLock<Mutex<Vec<Mapping>>> = LazyLock::new(|| Mutex::new(Vec::new()));

/// The mapped token of `original` in `class` (`PERSON_1`): the existing
/// index when the map holds one, the next free index otherwise.
fn mapped(class: &'static str, original: &str) -> String {
    let mut map = MAP
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    if let Some(found) = map
        .iter()
        .find(|entry| entry.class == class && entry.original == original)
    {
        return format!("{}_{}", class, found.index);
    }
    let index = map
        .iter()
        .filter(|entry| entry.class == class)
        .map(|entry| entry.index)
        .max()
        .map_or(1, |max| max + 1);
    map.push(Mapping {
        class,
        original: original.to_owned(),
        index,
    });
    format!("{class}_{index}")
}

/// The original of a mapped token (`PERSON_1`), when the map holds one.
fn original_of(token: &str) -> Option<String> {
    let map = MAP
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    let (class, index) = token.split_once('_')?;
    let index = index.parse::<u32>().ok()?;
    map.iter()
        .find(|entry| entry.class == class && entry.index == index)
        .map(|entry| entry.original.clone())
}

/// The token grammar of the mapped classes: `CLASS_<digits>`.
static TOKEN_RE: LazyLock<regex_lite::Regex> = LazyLock::new(|| {
    regex_lite::Regex::new("(?:PERSON|HOME|EMAIL|PATH|DOMAIN)_[0-9]+")
        .expect("the token grammar compiles")
});

/// Whether `text` is one mapped token.
fn is_token(text: &str) -> bool {
    TOKEN_RE.is_match(text)
}

/// Whether `text` holds a mapped token anywhere.
fn holds_token(text: &str) -> bool {
    TOKEN_RE.is_match(text)
}

// The terms
// ---------
/// One phrase of `privacy.terms` as a word-bounded pattern.
#[derive(Clone)]
struct TermRule {
    regex: regex_lite::Regex,
}

/// The compiled term rules, cached for the terms they were built from:
/// longest first, so "Gil Rodrigues" wins over "Gil", each escaped and
/// word-bounded, case-sensitive.
type TermCache = Option<(Vec<String>, Vec<TermRule>)>;
static TERM_RULES: LazyLock<Mutex<TermCache>> = LazyLock::new(|| Mutex::new(None));

fn term_rules(terms: &[String]) -> Vec<TermRule> {
    let mut cached = TERM_RULES
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    if let Some((held, rules)) = cached.as_ref() {
        if held == terms {
            return rules.clone();
        }
    }
    let mut sorted = terms.to_vec();
    sorted.sort_by_key(|term| std::cmp::Reverse(term.chars().count()));
    let rules: Vec<TermRule> = sorted
        .iter()
        .filter(|term| !term.trim().is_empty())
        .map(|term| TermRule {
            regex: regex_lite::Regex::new(&format!(r"\b{term}\b", term = regex_lite::escape(term)))
                .expect("a term pattern compiles"),
        })
        .collect();
    *cached = Some((terms.to_vec(), rules.clone()));
    rules
}

// The scrubber
// ------------

/// Scrubs one request's text: the mapped classes first (terms, home
/// names, emails, paths, domains), then the hashed classes (keys, IDs,
/// phones, IPs, cards).
#[derive(Clone)]
pub struct Scrubber {
    terms: Vec<TermRule>,
}

/// The hashed pattern passes, after the mapped ones: order matters only
/// between them and the mapped passes.
static HASHED_PASSES: LazyLock<Vec<(regex_lite::Regex, &'static str)>> = LazyLock::new(|| {
    HASHED_PATTERN_PASSES
        .iter()
        .map(|pass| {
            (
                regex_lite::Regex::new(pass.pattern).expect("a scrub pattern compiles"),
                pass.class,
            )
        })
        .collect()
});

const HASHED_PATTERN_PASSES: &[Pass] = &[
    // PEM blocks: a private key or certificate travels whole.
    Pass {
        pattern: "-----BEGIN [A-Z ]+-----[\\s\\S]*?-----END [A-Z ]+-----",
        class: "KEY",
    },
    // Bearer and basic credentials.
    Pass {
        pattern: "(?i)bearer [a-z0-9._~+/=-]{8,}",
        class: "KEY",
    },
    // Tokens with a known vendor prefix.
    Pass {
        pattern: "(?i)\\b(sk-proj-[A-Za-z0-9_-]{10,}|sk-[A-Za-z0-9_-]{16,}|ghp_[A-Za-z0-9]{20,}|gho_[A-Za-z0-9]{20,}|github_pat_[A-Za-z0-9_]{20,}|xox[abprs]-[A-Za-z0-9-]{10,}|AKIA[0-9A-Z]{16}|AIza[0-9A-Za-z_-]{35}|glpat-[A-Za-z0-9_-]{16,}|dop_v1_[a-f0-9]{40,}|shpat_[A-Za-z0-9]{20,}|npm_[A-Za-z0-9]{30,})",
        class: "KEY",
    },
    // IBAN: country code, two check digits, 10 to 30 alphanumerics.
    Pass {
        pattern: "\\b[A-Z]{2}[0-9]{2}[A-Z0-9]{10,30}\\b",
        class: "IBAN",
    },
    // US social security number.
    Pass {
        pattern: "\\b[0-9]{3}-[0-9]{2}-[0-9]{4}\\b",
        class: "ID",
    },
    // Phone numbers: a leading plus, or a dashed local shape. Tight on
    // purpose: dates and versions must not match.
    Pass {
        pattern: "\\+[0-9][0-9 ().-]{6,20}[0-9]\\b|\\b[0-9]{3}-[0-9]{3}-[0-9]{4}\\b",
        class: "PHONE",
    },
    // IPv6: the full 8-group form, or any compressed form (it holds
    // `::`). A plain `hh:mm:ss` time has no `::` and stays readable.
    Pass {
        pattern: "\\b(?:[0-9A-Fa-f]{1,4}:){7}[0-9A-Fa-f]{1,4}\\b|(?:[0-9A-Fa-f]{1,4}:)*::(?:[0-9A-Fa-f]{1,4}:)*[0-9A-Fa-f]{0,4}",
        class: "IP",
    },
    Pass {
        pattern: "\\b(?:[0-9]{1,3}\\.){3}[0-9]{1,3}\\b",
        class: "IP",
    },
];

/// One pattern pass: every match of `pattern` becomes a pseudonym of
/// `class`, keyed by the match text.
struct Pass {
    pattern: &'static str,
    class: &'static str,
}

// The mapped patterns (class, pattern with one replace group; the guard
// holds when a match already carries a token).

/// The home root and its first segment.
static HOME_RE: LazyLock<regex_lite::Regex> = LazyLock::new(|| {
    regex_lite::Regex::new("(/(?:home|Users)/)([A-Za-z0-9._-]+)").expect("compiles")
});

/// An email.
static EMAIL_RE: LazyLock<regex_lite::Regex> = LazyLock::new(|| {
    regex_lite::Regex::new("[A-Za-z0-9._%+-]+@[A-Za-z0-9.-]+\\.[A-Za-z]{2,}").expect("compiles")
});

/// An absolute path: two segments or more, so a lone `/` never matches.
static PATH_RE: LazyLock<regex_lite::Regex> = LazyLock::new(|| {
    regex_lite::Regex::new(
        "/(?:home|Users|root|mnt|media|srv|opt|var|etc|usr|private)(?:/[A-Za-z0-9._-]+)+",
    )
    .expect("compiles")
});

/// A URL's host: the scheme and path stay readable.
static URL_HOST_RE: LazyLock<regex_lite::Regex> = LazyLock::new(|| {
    regex_lite::Regex::new("(?i)(https?://)([a-z0-9][a-z0-9.-]*\\.[a-z]{2,})").expect("compiles")
});

/// A bare domain.
static DOMAIN_RE: LazyLock<regex_lite::Regex> = LazyLock::new(|| {
    regex_lite::Regex::new(
        "\\b[a-z0-9][a-z0-9.-]*\\.(?:com|org|net|io|dev|ai|de|eu|sh|app|co|xyz|me|info)\\b",
    )
    .expect("compiles")
});

impl Scrubber {
    /// The scrubber for `terms` (`privacy.terms`): every phrase becomes a
    /// `PERSON_<n>` token at word boundaries.
    #[must_use]
    pub fn new(terms: &[String]) -> Self {
        Self {
            terms: term_rules(terms),
        }
    }

    /// Scrub one string: the mapped classes, then the hashed ones. A
    /// match that already holds a token is left as it is, so scrubbing
    /// scrubbed text changes nothing.
    #[must_use]
    pub fn scrub_str(&self, input: &str) -> String {
        // Terms first: a name inside a path or email must not survive.
        let mut text = input.to_string();
        for rule in &self.terms {
            text = rule
                .regex
                .replace_all(&text, |caps: &regex_lite::Captures| {
                    mapped("PERSON", caps.get(0).map_or("", |m| m.as_str()))
                })
                .into_owned();
        }
        // Home names: the root stays, the segment becomes HOME_<n>.
        text = HOME_RE
            .replace_all(&text, |caps: &regex_lite::Captures| {
                let root = caps.get(1).map_or("", |m| m.as_str());
                let segment = caps.get(2).map_or("", |m| m.as_str());
                if is_token(segment) {
                    format!("{root}{segment}")
                } else {
                    format!("{root}{}", mapped("HOME", segment))
                }
            })
            .into_owned();
        // Emails before domains: the domain passes would mangle them.
        text = EMAIL_RE
            .replace_all(&text, |caps: &regex_lite::Captures| {
                mapped("EMAIL", caps.get(0).map_or("", |m| m.as_str()))
            })
            .into_owned();
        // Whole absolute paths whose text holds no token yet.
        text = PATH_RE
            .replace_all(&text, |caps: &regex_lite::Captures| {
                let whole = caps.get(0).map_or("", |m| m.as_str());
                if holds_token(whole) {
                    whole.to_string()
                } else {
                    mapped("PATH", whole)
                }
            })
            .into_owned();
        // Domains: the scheme stays, the host becomes DOMAIN_<n>.
        text = URL_HOST_RE
            .replace_all(&text, |caps: &regex_lite::Captures| {
                let scheme = caps.get(1).map_or("", |m| m.as_str());
                let host = caps.get(2).map_or("", |m| m.as_str());
                if is_token(host) {
                    format!("{scheme}{host}")
                } else {
                    format!("{scheme}{}", mapped("DOMAIN", host))
                }
            })
            .into_owned();
        text = DOMAIN_RE
            .replace_all(&text, |caps: &regex_lite::Captures| {
                let whole = caps.get(0).map_or("", |m| m.as_str());
                if is_token(whole) {
                    whole.to_string()
                } else {
                    mapped("DOMAIN", whole)
                }
            })
            .into_owned();
        // The hashed classes.
        for (regex, class) in HASHED_PASSES.iter() {
            text = regex
                .replace_all(&text, |caps: &regex_lite::Captures| {
                    pseudonym(class, caps.get(0).map_or("", |m| m.as_str()))
                })
                .into_owned();
        }
        scrub_cards(&text)
    }

    /// Map every pseudonym token of the mapped classes back to its
    /// original; a token the map does not hold stays as it is. Hashed
    /// pseudonyms never come back.
    #[must_use]
    pub fn unredact(&self, input: &str) -> String {
        TOKEN_RE
            .replace_all(input, |caps: &regex_lite::Captures| {
                let token = caps.get(0).map_or("", |m| m.as_str());
                original_of(token).unwrap_or_else(|| token.to_owned())
            })
            .into_owned()
    }

    /// Scrub the text fields of one request's messages. Images are
    /// untouched; tool call arguments are scrubbed per string value.
    #[must_use]
    pub fn scrub_messages(&self, messages: Vec<Message>) -> Vec<Message> {
        messages
            .into_iter()
            .map(|message| match message {
                Message::System(mut system) => {
                    system.content = match system.content {
                        SystemContent::Text(text) => SystemContent::Text(self.scrub_str(&text)),
                        SystemContent::Blocks(blocks) => SystemContent::Blocks(
                            blocks
                                .into_iter()
                                .map(|mut block| {
                                    block.text = self.scrub_str(&block.text);
                                    block
                                })
                                .collect(),
                        ),
                    };
                    Message::System(system)
                }
                Message::User(mut user) => {
                    user.content = match user.content {
                        UserContent::Text(text) => UserContent::Text(self.scrub_str(&text)),
                        UserContent::Blocks(blocks) => UserContent::Blocks(
                            blocks
                                .into_iter()
                                .map(|block| match block {
                                    UserContentBlock::Text(mut text) => {
                                        text.text = self.scrub_str(&text.text);
                                        UserContentBlock::Text(text)
                                    }
                                    other @ UserContentBlock::Image(_) => other,
                                })
                                .collect(),
                        ),
                    };
                    Message::User(user)
                }
                Message::Assistant(mut assistant) => {
                    for block in &mut assistant.content {
                        match block {
                            AssistantContentBlock::Text(text) => {
                                text.text = self.scrub_str(&text.text);
                            }
                            AssistantContentBlock::Thinking(thinking) => {
                                thinking.thinking = self.scrub_str(&thinking.thinking);
                            }
                            AssistantContentBlock::ToolCall(call) => {
                                call.arguments = self.scrub_map(call.arguments.clone());
                            }
                        }
                    }
                    Message::Assistant(assistant)
                }
                Message::ToolResult(mut result) => {
                    result.content = result
                        .content
                        .into_iter()
                        .map(|block| match block {
                            UserContentBlock::Text(mut text) => {
                                text.text = self.scrub_str(&text.text);
                                UserContentBlock::Text(text)
                            }
                            other @ UserContentBlock::Image(_) => other,
                        })
                        .collect();
                    result.details = result.details.map(|details| self.scrub_json(details));
                    Message::ToolResult(result)
                }
            })
            .collect()
    }

    /// Scrub every string in a JSON tree (keys stay).
    #[must_use]
    pub fn scrub_json(&self, value: serde_json::Value) -> serde_json::Value {
        match value {
            serde_json::Value::String(text) => serde_json::Value::String(self.scrub_str(&text)),
            serde_json::Value::Array(items) => serde_json::Value::Array(
                items
                    .into_iter()
                    .map(|item| self.scrub_json(item))
                    .collect(),
            ),
            serde_json::Value::Object(map) => serde_json::Value::Object(
                map.into_iter()
                    .map(|(key, value)| (key, self.scrub_json(value)))
                    .collect(),
            ),
            other => other,
        }
    }

    /// Scrub a tool call's arguments: each string value is rewritten,
    /// other values are scrubbed as JSON.
    fn scrub_map(&self, map: eukhe_types::JsonMap) -> eukhe_types::JsonMap {
        map.into_iter()
            .map(|(key, value)| {
                let value = match value {
                    serde_json::Value::String(text) => {
                        serde_json::Value::String(self.scrub_str(&text))
                    }
                    other => self.scrub_json(other),
                };
                (key, value)
            })
            .collect()
    }

    /// Map the pseudonym tokens of a tool call's arguments back, so a
    /// remote model's call executes against the real strings.
    #[must_use]
    pub fn unredact_arguments(&self, arguments: &eukhe_types::JsonMap) -> eukhe_types::JsonMap {
        arguments
            .iter()
            .map(|(key, value)| {
                let value = unredact_json(value, &self.unredact_fn());
                (key.clone(), value)
            })
            .collect()
    }

    fn unredact_fn(&self) -> impl Fn(&str) -> String + '_ {
        move |text: &str| self.unredact(text)
    }
}

/// Map the tokens of every string in a JSON tree back (keys stay).
fn unredact_json(
    value: &serde_json::Value,
    unredact: &dyn Fn(&str) -> String,
) -> serde_json::Value {
    match value {
        serde_json::Value::String(text) => serde_json::Value::String(unredact(text)),
        serde_json::Value::Array(items) => serde_json::Value::Array(
            items
                .iter()
                .map(|item| unredact_json(item, unredact))
                .collect(),
        ),
        serde_json::Value::Object(map) => serde_json::Value::Object(
            map.iter()
                .map(|(key, value)| (key.clone(), unredact_json(value, unredact)))
                .collect(),
        ),
        other => other.clone(),
    }
}

/// Credit cards: a 13 to 19 digit run with spaces or dashes that passes
/// the Luhn check. The Luhn keeps dates, versions and phone fragments out.
fn scrub_cards(text: &str) -> String {
    let regex = regex_lite::Regex::new("\\b[0-9](?:[0-9 -]{11,23})[0-9]\\b").expect("compiles");
    regex
        .replace_all(text, |caps: &regex_lite::Captures| {
            let raw = caps.get(0).map_or("", |m| m.as_str());
            let digits: String = raw.chars().filter(char::is_ascii_digit).collect();
            if (13..=19).contains(&digits.len()) && luhn(&digits) {
                pseudonym("CARD", raw)
            } else {
                raw.to_string()
            }
        })
        .into_owned()
}

/// The Luhn check sum of a digit run.
fn luhn(digits: &str) -> bool {
    let sum = digits
        .chars()
        .rev()
        .filter_map(|c| c.to_digit(10))
        .enumerate()
        .map(|(index, digit)| {
            if index % 2 == 1 {
                let doubled = digit * 2;
                doubled / 10 + doubled % 10
            } else {
                digit
            }
        })
        .sum::<u32>();
    sum % 10 == 0
}

#[cfg(test)]
mod tests {
    use super::*;

    fn scrubber() -> Scrubber {
        Scrubber::new(&["Gil Rodrigues".to_owned()])
    }

    #[test]
    fn loopback_endpoints_are_local_and_others_are_not() {
        assert!(is_local("http://127.0.0.1:18020/v1"));
        assert!(is_local("http://localhost:8080"));
        assert!(is_local("http://[::1]:9000"));
        assert!(!is_local("https://api.anthropic.com"));
        assert!(!is_local("https://openrouter.ai/api/v1"));
    }

    #[test]
    fn every_class_gets_a_stable_pseudonym() {
        let email = scrubber().scrub_str("write to gil@example.com about the invoice");
        let expected = "write to EMAIL_1 about the invoice";
        assert_eq!(email, expected);
        // The same input twice: the same token.
        assert_eq!(
            scrubber().scrub_str("gil@example.com"),
            scrubber().scrub_str("gil@example.com")
        );
        // A different input: a different token.
        assert_ne!(
            scrubber().scrub_str("gil@example.com"),
            scrubber().scrub_str("sam@example.com")
        );
    }

    #[test]
    fn terms_scrub_names_and_only_at_boundaries() {
        let out = scrubber().scrub_str("ask Gil Rodrigues, not Gilbert");
        assert_eq!(out, "ask PERSON_1, not Gilbert");
        // A term inside a longer word does not match.
        let inside = Scrubber::new(&["Gil".to_owned()]).scrub_str("Gilbert stays");
        assert_eq!(inside, "Gilbert stays");
    }

    #[test]
    fn keys_tokens_and_cards_are_scrubbed() {
        let out = scrubber()
            .scrub_str("sk-abcdefghijklmnopqrstuvwx and AKIAIOSFODNN7EXAMPLE on the account");
        assert!(!out.contains("sk-abcdefghijklmnopqrstuvwx"));
        assert!(!out.contains("AKIAIOSFODNN7EXAMPLE"));
        assert!(out.contains("KEY_"));
        let card = scrubber().scrub_str("pay with 4111 1111 1111 1111 today");
        assert!(!card.contains("4111"));
        assert!(card.contains("CARD_"));
        // A date is not a card.
        let date = scrubber().scrub_str("on 2026-10-27 and 2026-11-01 we ship");
        assert_eq!(date, "on 2026-10-27 and 2026-11-01 we ship");
    }

    #[test]
    fn paths_ips_domains_and_homes_are_scrubbed() {
        let out = scrubber().scrub_str(
            "the log at /home/gilrodrigues/Repos/eukhe/target and /var/log/syslog says 10.0.0.7 refused https://api.anthropic.com/v1",
        );
        assert!(!out.contains("/home/gilrodrigues"));
        assert!(!out.contains("gilrodrigues"));
        assert!(out.contains("/home/HOME_"));
        // A home path keeps its shape; a non-home path maps whole.
        assert!(out.contains("PATH_"));
        assert!(!out.contains("/var/log/syslog"));
        assert!(!out.contains("10.0.0.7"));
        assert!(!out.contains("api.anthropic.com"));
        assert!(out.contains("IP_"));
        assert!(out.contains("DOMAIN_"));
    }

    #[test]
    fn phone_numbers_are_scrubbed_but_dates_survive() {
        let out = scrubber().scrub_str("call +49 172 4510 5432 or 0172-451-0543 on 2026-10-27");
        assert!(!out.contains("5432 or"));
        assert!(out.contains("PHONE_"));
        assert!(out.contains("2026-10-27"));
    }

    #[test]
    fn scrubbing_scrubbed_text_changes_nothing() {
        let text = "Gil Rodrigues works in /home/gilrodrigues/x, mail gil@example.com, https://api.anthropic.com/v1, key sk-abcdefghijklmnopqrstuvwx";
        let once = scrubber().scrub_str(text);
        let twice = scrubber().scrub_str(&once);
        assert_eq!(once, twice);
    }

    #[test]
    fn unredact_maps_tokens_back_and_never_hashed_ones() {
        let text = "Gil Rodrigues reads /var/log/syslog and /home/gilrodrigues/x, mail gil@example.com, key sk-abcdefghijklmnopqrstuvwx";
        let scrubbed = scrubber().scrub_str(text);
        let back = scrubber().unredact(&scrubbed);
        assert!(back.contains("Gil Rodrigues"));
        assert!(back.contains("/var/log/syslog"));
        assert!(back.contains("/home/gilrodrigues/x"));
        assert!(back.contains("gil@example.com"));
        // The key never comes back.
        assert!(!back.contains("sk-abcdefghijklmnopqrstuvwx"));
        assert!(back.contains("KEY_"));
    }

    #[test]
    fn tool_arguments_map_back_through_the_map() {
        let scrubbed = scrubber().scrub_str("cat /home/gilrodrigues/notes/day.md");
        let mut arguments = eukhe_types::JsonMap::new();
        arguments.insert("script".to_owned(), serde_json::Value::String(scrubbed));
        let back = scrubber().unredact_arguments(&arguments);
        assert_eq!(
            back.get("script").and_then(|value| value.as_str()),
            Some("cat /home/gilrodrigues/notes/day.md")
        );
    }

    #[test]
    fn messages_of_every_role_are_scrubbed() {
        let messages: Vec<Message> = serde_json::from_value(serde_json::json!([
            { "role": "system", "content": "workspace /home/gil/work", "timestamp": 0 },
            { "role": "user", "content": "my key is ghp_AAAABBBBCCCCDDDDEEEE", "timestamp": 0 },
            { "role": "assistant", "content": [
                { "type": "toolCall", "id": "t1", "name": "bash",
                  "arguments": { "script": "cat /home/gil/.ssh/id_ed25519" } },
            ],
              "api": "anthropic", "provider": "anthropic", "model": "m", "timestamp": 0,
              "usage": { "input": 0, "output": 0, "cacheRead": 0, "cacheWrite": 0, "totalTokens": 0,
                         "cost": { "input": 0, "output": 0, "cacheRead": 0, "cacheWrite": 0, "total": 0 } },
              "stopReason": "stop" },
            { "role": "toolResult", "toolCallId": "t1", "toolName": "bash", "isError": false,
              "content": [ { "type": "text", "text": " mailed sam@example.org the file" } ],
              "timestamp": 0 },
        ]))
        .expect("the wire shapes");
        let scrubbed = format!("{:?}", scrubber().scrub_messages(messages));
        assert!(!scrubbed.contains("/home/gil"));
        assert!(!scrubbed.contains("ghp_AAAABBBBCCCCDDDDEEEE"));
        assert!(!scrubbed.contains("sam@example.org"));
        assert!(scrubbed.contains("HOME_"));
        assert!(scrubbed.contains("KEY_"));
        assert!(scrubbed.contains("EMAIL_"));
    }
}
