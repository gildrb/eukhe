//! Claude Code's billing attribution for OAuth (subscription) requests.
//!
//! Claude Code opens every subscription request's `system` with an
//! `x-anthropic-billing-header:` text block: the CLI version with a
//! fingerprint of the first user turn, the entrypoint, and `cch`, an
//! attestation hash of the serialized request body. Anthropic bills a
//! subscription request without it as third-party usage, which answers
//! `429 rate_limit_error` ("This request would exceed your account's rate
//! limit") with a multi-day `retry-after` while Claude Code and omp, which
//! send the block, keep working on the same account.
//!
//! [`billing_header`] builds the block text with the `cch=00000`
//! placeholder; [`patch_cch`] replaces the placeholder in the serialized
//! body with the attestation (omp `createClaudeBillingHeader` and
//! `patchCch`).

use eukhe_types::pi_ai::JsonValue;
use sha2::{Digest, Sha256};

/// The billing block's text prefix.
pub(crate) const BILLING_HEADER_PREFIX: &str = "x-anthropic-billing-header:";

/// Salt of the `cc_version` fingerprint (Claude Code `computeFingerprint`).
const FINGERPRINT_SALT: &str = "59cf53e54c78";

/// UTF-16 indexes of the first user turn the fingerprint samples.
const FINGERPRINT_INDEXES: [usize; 3] = [4, 7, 20];

/// The attestation placeholder [`patch_cch`] overwrites.
const CCH_PLACEHOLDER: &[u8] = b"cch=00000";

/// Seed of the `cch` XXH64 attestation.
const CCH_SEED: u64 = 0x4d65_9218_e32a_3268;

/// The serialized prefix of a billing block that opens `system`. `messages`
/// serializes before `system`, so user content can never forge it.
const BILLING_SYSTEM_MARKER: &[u8] =
    b"\"system\":[{\"type\":\"text\",\"text\":\"x-anthropic-billing-header:";

/// How far after [`BILLING_SYSTEM_MARKER`] the placeholder may sit.
const CCH_SEARCH_WINDOW: usize = 150;

/// The billing block text for `first_user_text` (the first user turn's
/// text, [`first_user_text`]) under Claude Code `version`.
pub(crate) fn billing_header(first_user_text: &str, version: &str) -> String {
    let units: Vec<u16> = first_user_text.encode_utf16().collect();
    let sampled: String = FINGERPRINT_INDEXES
        .iter()
        .map(|&index| match units.get(index) {
            // A lone surrogate hashes as U+FFFD, like JS UTF-8 encoding.
            Some(&unit) => char::from_u32(u32::from(unit)).unwrap_or(char::REPLACEMENT_CHARACTER),
            None => '0',
        })
        .collect();
    let digest = Sha256::digest(format!("{FINGERPRINT_SALT}{sampled}{version}").as_bytes());
    let suffix: String = digest
        .iter()
        .flat_map(|byte| [byte >> 4, byte & 0x0f])
        .take(3)
        .map(|nibble| char::from_digit(u32::from(nibble), 16).unwrap_or('0'))
        .collect();
    format!("{BILLING_HEADER_PREFIX} cc_version={version}.{suffix}; cc_entrypoint=cli; cch=00000;")
}

/// The text of the first wire user turn: its string content, or its first
/// non-blank text block; a turn that opens with an image and no text
/// yields "".
pub(crate) fn first_user_text(wire_messages: &[JsonValue]) -> &str {
    for message in wire_messages {
        if message.get("role").and_then(JsonValue::as_str) != Some("user") {
            continue;
        }
        match message.get("content") {
            Some(JsonValue::String(text)) if !text.trim().is_empty() => return text,
            Some(JsonValue::Array(blocks)) => {
                let text = blocks.iter().find_map(|block| {
                    (block.get("type").and_then(JsonValue::as_str) == Some("text"))
                        .then(|| block.get("text").and_then(JsonValue::as_str))
                        .flatten()
                        .filter(|text| !text.trim().is_empty())
                });
                if let Some(text) = text {
                    return text;
                }
                if blocks
                    .iter()
                    .any(|block| block.get("type").and_then(JsonValue::as_str) == Some("image"))
                {
                    return "";
                }
            }
            _ => {}
        }
    }
    ""
}

/// Replace the billing block's `cch=00000` in the serialized `body` with
/// the attestation: the low 20 bits of XXH64 over the body as serialized
/// (placeholder in place), as five hex digits. A body without a billing
/// block opening `system` is left untouched.
pub(crate) fn patch_cch(body: &mut [u8]) {
    let Some(marker) = find(body, BILLING_SYSTEM_MARKER, 0) else {
        return;
    };
    let from = marker + BILLING_SYSTEM_MARKER.len();
    let Some(at) = find(body, CCH_PLACEHOLDER, from).filter(|&at| at - from <= CCH_SEARCH_WINDOW)
    else {
        return;
    };
    let hash = twox_hash::XxHash64::oneshot(CCH_SEED, body) & 0xf_ffff;
    let digits = format!("{hash:05x}");
    let start = at + "cch=".len();
    body[start..start + 5].copy_from_slice(digits.as_bytes());
}

fn find(haystack: &[u8], needle: &[u8], from: usize) -> Option<usize> {
    haystack
        .get(from..)?
        .windows(needle.len())
        .position(|window| window == needle)
        .map(|position| position + from)
}

#[cfg(test)]
mod tests {
    use serde_json::json;

    use super::*;

    /// Golden values from omp's wire capture and SHA-256 of the sampled
    /// characters: omp sent `cc_version=2.1.280.096` for a first user turn
    /// opening `<system-reminder>\nToday`.
    #[test]
    fn the_billing_header_carries_the_fingerprinted_version_and_the_placeholder() {
        assert_eq!(
            billing_header("<system-reminder>\nToday: 2026-11-02", "2.1.280"),
            "x-anthropic-billing-header: cc_version=2.1.280.096; cc_entrypoint=cli; cch=00000;"
        );
        // UTF-16 indexes 4, 7, 20 sample "ows".
        assert_eq!(
            billing_header("Hello, world! This is a test", "2.1.280"),
            "x-anthropic-billing-header: cc_version=2.1.280.bef; cc_entrypoint=cli; cch=00000;"
        );
        // A short text samples "0" past its end.
        assert_eq!(
            billing_header("", "2.1.280"),
            "x-anthropic-billing-header: cc_version=2.1.280.d7b; cc_entrypoint=cli; cch=00000;"
        );
    }

    #[test]
    fn the_first_user_text_skips_non_user_turns_and_blank_blocks() {
        let messages = [
            json!({ "role": "assistant", "content": "ignored" }),
            json!({ "role": "user", "content": [
                { "type": "text", "text": "  " },
                { "type": "text", "text": "first" },
            ] }),
            json!({ "role": "user", "content": "second" }),
        ];
        assert_eq!(first_user_text(&messages), "first");
        let image_first = [
            json!({ "role": "user", "content": [{ "type": "image", "source": {} }] }),
            json!({ "role": "user", "content": "later" }),
        ];
        assert_eq!(first_user_text(&image_first), "");
        assert_eq!(first_user_text(&[]), "");
    }

    /// Golden attestation: XXH64 (seed `0x4d659218e32a3268`) of the body
    /// below, low 20 bits, computed independently (python `xxhash`); the
    /// same computation reproduced omp's wire `cch`.
    #[test]
    fn patch_cch_attests_the_body_with_the_placeholder_in_place() {
        let body = r#"{"model":"m","messages":[{"role":"user","content":"cch=00000"}],"system":[{"type":"text","text":"x-anthropic-billing-header: cc_version=2.1.280.abc; cc_entrypoint=cli; cch=00000;"}]}"#;
        let mut patched = body.as_bytes().to_vec();
        patch_cch(&mut patched);
        let patched = String::from_utf8(patched).expect("utf-8");
        assert_eq!(
            patched,
            body.replace(
                "cc_entrypoint=cli; cch=00000;",
                "cc_entrypoint=cli; cch=f9843;"
            ),
            "only the system block's placeholder changes"
        );
    }

    #[test]
    fn patch_cch_leaves_a_body_without_a_billing_block_untouched() {
        let body = br#"{"messages":[{"role":"user","content":"cch=00000"}],"system":[{"type":"text","text":"hi"}]}"#;
        let mut patched = body.to_vec();
        patch_cch(&mut patched);
        assert_eq!(patched, body);
    }
}
