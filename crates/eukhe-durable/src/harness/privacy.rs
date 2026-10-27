//! Outbound anonymization (`privacy.anonymizeRemote`): when the session's
//! model sits behind a non-loopback endpoint, every text the request
//! carries is scrubbed first. Emails, phone numbers, payment instruments,
//! government IDs, API keys and tokens, IP addresses, absolute paths,
//! hostnames and domains become stable pseudonyms
//! (`CLASS_<6 hex of the value's SHA-256>`): the same input always gets
//! the same pseudonym, no map is stored, and the chat memory in
//! `~/.eukhe` is never touched — the scrub runs on the outbound copy, so
//! the agent remembers everything and the provider sees pseudonyms.
//!
//! This is content rewriting on the request path (string in, string out),
//! not decision logic: it stays Rust on purpose. Patterns use
//! `regex-lite` (no look-around); anything a pattern cannot see (a free
//! text name, a hostname with no shape) travels unscrubbed — the local
//! memory keeps it either way.

use eukhe_types::pi_ai::{
    AssistantContentBlock, Message, SystemContent, UserContent, UserContentBlock,
};
use sha2::{Digest, Sha256};
use std::sync::LazyLock;

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

/// A stable pseudonym for `value` in `class`: `CLASS_<6 hex>`.
fn pseudonym(class: &str, value: &str) -> String {
    let digest = Sha256::digest(value.as_bytes());
    format!(
        "{}_{:02x}{:02x}{:02x}",
        class, digest[0], digest[1], digest[2]
    )
}

/// One pattern pass: every match of `pattern` becomes a pseudonym of
/// `class`, keyed by the match text.
struct Pass {
    pattern: &'static str,
    class: &'static str,
}

static PASSES: LazyLock<Vec<(regex_lite::Regex, &'static str)>> = LazyLock::new(|| {
    PATTERN_PASSES
        .iter()
        .map(|pass| {
            (
                regex_lite::Regex::new(pass.pattern).expect("a scrub pattern compiles"),
                pass.class,
            )
        })
        .collect()
});

const PATTERN_PASSES: &[Pass] = &[
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
    // Emails first: the domain pass would otherwise mangle them twice.
    Pass {
        pattern: "[A-Za-z0-9._%+-]+@[A-Za-z0-9.-]+\\.[A-Za-z]{2,}",
        class: "EMAIL",
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
    // A URL's host: the scheme and path stay readable.
    Pass {
        pattern: "(?i)(https?://)([a-z0-9][a-z0-9.-]*\\.[a-z]{2,})",
        class: "DOMAIN",
    },
    // A bare domain.
    Pass {
        pattern: "\\b[a-z0-9][a-z0-9.-]*\\.(?:com|org|net|io|dev|ai|de|eu|sh|app|co|xyz|me|info)\\b",
        class: "DOMAIN",
    },
    // Absolute paths: two segments or more, so a lone `/` never matches.
    Pass {
        pattern: "/(?:home|Users|root|mnt|media|srv|opt|var|etc|usr|private)(?:/[A-Za-z0-9._-]+)+",
        class: "PATH",
    },
    // `~user` and `user@host` (scp, ssh, git remotes).
    Pass {
        pattern: "~[a-z_][a-z0-9_-]*|\\b[a-z_][a-z0-9_-]*@(?:[a-z0-9.-]+)",
        class: "USER",
    },
];

/// Scrub one string: every pattern pass replaces its matches.
#[must_use]
pub fn scrub_str(input: &str) -> String {
    let mut text = input.to_string();
    for (regex, class) in PASSES.iter() {
        text = regex
            .replace_all(&text, |caps: &regex_lite::Captures| {
                pseudonym(class, caps.get(0).map_or("", |m| m.as_str()))
            })
            .into_owned();
    }
    scrub_cards(&text)
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

/// Scrub the text fields of one request's messages. Images are untouched;
/// tool call arguments are scrubbed per string value.
#[must_use]
pub fn scrub_messages(messages: Vec<Message>) -> Vec<Message> {
    messages
        .into_iter()
        .map(|message| match message {
            Message::System(mut system) => {
                system.content = match system.content {
                    SystemContent::Text(text) => SystemContent::Text(scrub_str(&text)),
                    SystemContent::Blocks(blocks) => SystemContent::Blocks(
                        blocks
                            .into_iter()
                            .map(|mut block| {
                                block.text = scrub_str(&block.text);
                                block
                            })
                            .collect(),
                    ),
                };
                Message::System(system)
            }
            Message::User(mut user) => {
                user.content = match user.content {
                    UserContent::Text(text) => UserContent::Text(scrub_str(&text)),
                    UserContent::Blocks(blocks) => UserContent::Blocks(
                        blocks
                            .into_iter()
                            .map(|block| match block {
                                UserContentBlock::Text(mut text) => {
                                    text.text = scrub_str(&text.text);
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
                            text.text = scrub_str(&text.text);
                        }
                        AssistantContentBlock::Thinking(thinking) => {
                            thinking.thinking = scrub_str(&thinking.thinking);
                        }
                        AssistantContentBlock::ToolCall(call) => {
                            call.arguments = scrub_map(call.arguments.clone());
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
                            text.text = scrub_str(&text.text);
                            UserContentBlock::Text(text)
                        }
                        other @ UserContentBlock::Image(_) => other,
                    })
                    .collect();
                result.details = result.details.map(scrub_json);
                Message::ToolResult(result)
            }
        })
        .collect()
}

/// Scrub every string in a JSON tree (keys stay).
#[must_use]
pub fn scrub_json(value: serde_json::Value) -> serde_json::Value {
    match value {
        serde_json::Value::String(text) => serde_json::Value::String(scrub_str(&text)),
        serde_json::Value::Array(items) => {
            serde_json::Value::Array(items.into_iter().map(scrub_json).collect())
        }
        serde_json::Value::Object(map) => serde_json::Value::Object(
            map.into_iter()
                .map(|(key, value)| (key, scrub_json(value)))
                .collect(),
        ),
        other => other,
    }
}

/// Scrub a tool call's arguments: each string value is rewritten, other
/// values are scrubbed as JSON.
fn scrub_map(map: eukhe_types::JsonMap) -> eukhe_types::JsonMap {
    map.into_iter()
        .map(|(key, value)| {
            let value = match value {
                serde_json::Value::String(text) => serde_json::Value::String(scrub_str(&text)),
                other => scrub_json(other),
            };
            (key, value)
        })
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;

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
        let email = scrub_str("write to gil@example.com about the invoice");
        let expected = format!(
            "write to {} about the invoice",
            pseudonym("EMAIL", "gil@example.com")
        );
        assert_eq!(email, expected);
        // The same input twice: the same pseudonym.
        assert_eq!(scrub_str("gil@example.com"), scrub_str("gil@example.com"));
        // A different input: a different pseudonym.
        assert_ne!(scrub_str("gil@example.com"), scrub_str("sam@example.com"));
    }

    #[test]
    fn keys_tokens_and_cards_are_scrubbed() {
        let out = scrub_str("sk-abcdefghijklmnopqrstuvwx and AKIAIOSFODNN7EXAMPLE on the account");
        assert!(!out.contains("sk-abcdefghijklmnopqrstuvwx"));
        assert!(!out.contains("AKIAIOSFODNN7EXAMPLE"));
        assert!(out.contains("KEY_"));
        let card = scrub_str("pay with 4111 1111 1111 1111 today");
        assert!(!card.contains("4111"));
        assert!(card.contains("CARD_"));
        // A date is not a card.
        let date = scrub_str("on 2026-10-27 and 2026-11-01 we ship");
        assert_eq!(date, "on 2026-10-27 and 2026-11-01 we ship");
    }

    #[test]
    fn paths_ips_domains_and_hosts_are_scrubbed() {
        let out = scrub_str("the log at /home/gilrodrigues/Repos/eukhe/target says 10.0.0.7 refused https://api.anthropic.com/v1");
        assert!(!out.contains("/home/gilrodrigues"));
        assert!(!out.contains("10.0.0.7"));
        assert!(!out.contains("api.anthropic.com"));
        assert!(out.contains("PATH_"));
        assert!(out.contains("IP_"));
        assert!(out.contains("DOMAIN_"));
    }

    #[test]
    fn phone_numbers_are_scrubbed_but_dates_survive() {
        let out = scrub_str("call +49 172 4510 5432 or 0172-451-0543 on 2026-10-27");
        assert!(!out.contains("5432 or"));
        assert!(out.contains("PHONE_"));
        assert!(out.contains("2026-10-27"));
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
        let scrubbed = format!("{:?}", scrub_messages(messages));
        assert!(!scrubbed.contains("/home/gil"));
        assert!(!scrubbed.contains("ghp_AAAABBBBCCCCDDDDEEEE"));
        assert!(!scrubbed.contains("sam@example.org"));
        assert!(scrubbed.contains("PATH_"));
        assert!(scrubbed.contains("KEY_"));
        assert!(scrubbed.contains("EMAIL_"));
    }
}
