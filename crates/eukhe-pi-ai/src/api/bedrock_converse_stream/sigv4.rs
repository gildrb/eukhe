//! AWS Signature Version 4 request signing: the `@smithy/signature-v4`
//! `SignatureV4.sign()` the AWS SDK applies to every Bedrock request (and the
//! STS calls of the credential chain).

use std::fmt::Write as _;
use std::time::{Duration, SystemTime, UNIX_EPOCH};

use hmac::{Hmac, Mac};
use sha2::{Digest, Sha256};

use super::client_config::AwsCredentials;

type HmacSha256 = Hmac<Sha256>;

/// Headers `SigV4` never signs (`ALWAYS_UNSIGNABLE_HEADERS`).
const ALWAYS_UNSIGNABLE_HEADERS: [&str; 15] = [
    "authorization",
    "cache-control",
    "connection",
    "expect",
    "from",
    "keep-alive",
    "max-forwards",
    "pragma",
    "referer",
    "te",
    "trailer",
    "transfer-encoding",
    "upgrade",
    "user-agent",
    "x-amzn-trace-id",
];

/// Headers the signer regenerates (`GENERATED_HEADERS`).
const GENERATED_HEADERS: [&str; 3] = ["authorization", "x-amz-date", "date"];

/// One request to sign. Header names keep the caller's case; the list has JS
/// object semantics (insertion order, exact-key replacement).
pub(crate) struct SignableRequest<'a> {
    pub(crate) method: &'a str,
    /// The request path, already URI-encoded once (as sent on the wire).
    pub(crate) path: &'a str,
    pub(crate) headers: &'a mut Vec<(String, String)>,
    pub(crate) body: &'a [u8],
}

/// Signing scope and identity.
pub(crate) struct SigningScope<'a> {
    pub(crate) credentials: &'a AwsCredentials,
    pub(crate) region: &'a str,
    pub(crate) service: &'a str,
    /// The (clock-skew corrected) signing time.
    pub(crate) now: SystemTime,
}

/// Set or replace a header with JS object semantics (exact key).
pub(crate) fn set_header(headers: &mut Vec<(String, String)>, name: &str, value: String) {
    match headers.iter_mut().find(|(key, _)| key == name) {
        Some(entry) => entry.1 = value,
        None => headers.push((name.to_owned(), value)),
    }
}

fn has_header(headers: &[(String, String)], name: &str) -> bool {
    headers
        .iter()
        .any(|(key, _)| key.eq_ignore_ascii_case(name))
}

pub(crate) fn sha256_hex(bytes: &[u8]) -> String {
    hex::encode(Sha256::digest(bytes))
}

fn hmac_sha256(key: &[u8], data: &[u8]) -> Vec<u8> {
    // HMAC accepts keys of any length, so construction cannot fail.
    let mut mac = HmacSha256::new_from_slice(key).unwrap_or_else(|_| unreachable!());
    mac.update(data);
    mac.finalize().into_bytes().to_vec()
}

/// Civil UTC date-time of a Unix timestamp (Howard Hinnant's algorithm):
/// `(year, month, day, hour, minute, second)`.
pub(crate) fn civil_from_unix(secs: u64) -> (i64, u32, u32, u32, u32, u32) {
    let days = i64::try_from(secs / 86_400).unwrap_or(i64::MAX);
    let secs_of_day = secs % 86_400;
    let z = days + 719_468;
    let era = z.div_euclid(146_097);
    let doe = z.rem_euclid(146_097);
    let yoe = (doe - doe / 1460 + doe / 36_524 - doe / 146_096) / 365;
    let y = yoe + era * 400;
    let doy = doe - (365 * yoe + yoe / 4 - yoe / 100);
    let mp = (5 * doy + 2) / 153;
    let day = u32::try_from(doy - (153 * mp + 2) / 5 + 1).unwrap_or(1);
    let month = u32::try_from(if mp < 10 { mp + 3 } else { mp - 9 }).unwrap_or(1);
    let year = if month <= 2 { y + 1 } else { y };
    let hour = u32::try_from(secs_of_day / 3600).unwrap_or(0);
    let minute = u32::try_from((secs_of_day % 3600) / 60).unwrap_or(0);
    let second = u32::try_from(secs_of_day % 60).unwrap_or(0);
    (year, month, day, hour, minute, second)
}

/// `(longDate, shortDate)`: `20250101T000000Z` and `20250101`.
fn format_dates(now: SystemTime) -> (String, String) {
    let secs = now
        .duration_since(UNIX_EPOCH)
        .unwrap_or(Duration::ZERO)
        .as_secs();
    let (year, month, day, hour, minute, second) = civil_from_unix(secs);
    (
        format!("{year:04}{month:02}{day:02}T{hour:02}{minute:02}{second:02}Z"),
        format!("{year:04}{month:02}{day:02}"),
    )
}

/// JS `encodeURIComponent(value).replace(/[!'()*]/g, hexEncode)`: every byte
/// outside `A-Z a-z 0-9 - _ . ~` percent-encoded (uppercase hex).
pub(crate) fn escape_uri(value: &str) -> String {
    let mut encoded = String::with_capacity(value.len());
    for byte in value.bytes() {
        if byte.is_ascii_alphanumeric() || matches!(byte, b'-' | b'_' | b'.' | b'~') {
            encoded.push(char::from(byte));
        } else {
            let _ = write!(encoded, "%{byte:02X}");
        }
    }
    encoded
}

/// `getCanonicalPath` with `uriEscapePath`: dot segments normalized, then the
/// path encoded a second time with `/` kept.
fn canonical_path(path: &str) -> String {
    let mut segments: Vec<&str> = Vec::new();
    for segment in path.split('/') {
        match segment {
            "" | "." => {}
            ".." => {
                segments.pop();
            }
            other => segments.push(other),
        }
    }
    let leading = if path.starts_with('/') { "/" } else { "" };
    let trailing = if !segments.is_empty() && path.ends_with('/') {
        "/"
    } else {
        ""
    };
    let normalized = format!("{leading}{}{trailing}", segments.join("/"));
    escape_uri(&normalized).replace("%2F", "/")
}

/// The canonical header map: lowercase names (later duplicates win, like
/// assigning into a JS object), trimmed values with whitespace runs
/// collapsed, sorted by name.
fn canonical_headers(headers: &[(String, String)]) -> Vec<(String, String)> {
    let mut canonical: Vec<(String, String)> = Vec::new();
    for (name, value) in headers {
        let lower = name.to_ascii_lowercase();
        if ALWAYS_UNSIGNABLE_HEADERS.contains(&lower.as_str())
            || lower.starts_with("proxy-")
            || lower.starts_with("sec-")
        {
            continue;
        }
        let value = value.split_whitespace().collect::<Vec<_>>().join(" ");
        match canonical.iter_mut().find(|(key, _)| *key == lower) {
            Some(entry) => entry.1 = value,
            None => canonical.push((lower, value)),
        }
    }
    canonical.sort_by(|left, right| left.0.cmp(&right.0));
    canonical
}

/// Sign `request` in place: adds `x-amz-security-token` (session
/// credentials), `x-amz-date`, `x-amz-content-sha256` (when applied), and
/// `authorization`.
pub(crate) fn sign_request(request: &mut SignableRequest<'_>, scope: &SigningScope<'_>) {
    request
        .headers
        .retain(|(name, _)| !GENERATED_HEADERS.contains(&name.to_ascii_lowercase().as_str()));
    let (long_date, short_date) = format_dates(scope.now);
    if let Some(token) = &scope.credentials.session_token {
        set_header(request.headers, "x-amz-security-token", token.clone());
    }
    set_header(request.headers, "x-amz-date", long_date.clone());

    let payload_hash = request
        .headers
        .iter()
        .find(|(name, _)| name.eq_ignore_ascii_case("x-amz-content-sha256"))
        .map_or_else(|| sha256_hex(request.body), |(_, value)| value.clone());
    // The SDK signer's `applyChecksum` (on for Bedrock and STS).
    if !has_header(request.headers, "x-amz-content-sha256") {
        set_header(
            request.headers,
            "x-amz-content-sha256",
            payload_hash.clone(),
        );
    }

    let canonical = canonical_headers(request.headers);
    let signed_headers = canonical
        .iter()
        .map(|(name, _)| name.as_str())
        .collect::<Vec<_>>()
        .join(";");
    let header_lines = canonical
        .iter()
        .map(|(name, value)| format!("{name}:{value}"))
        .collect::<Vec<_>>()
        .join("\n");
    let canonical_request = format!(
        "{}\n{}\n\n{header_lines}\n\n{signed_headers}\n{payload_hash}",
        request.method,
        canonical_path(request.path),
    );
    let credential_scope = format!(
        "{short_date}/{}/{}/aws4_request",
        scope.region, scope.service
    );
    let string_to_sign = format!(
        "AWS4-HMAC-SHA256\n{long_date}\n{credential_scope}\n{}",
        sha256_hex(canonical_request.as_bytes())
    );
    let date_key = hmac_sha256(
        format!("AWS4{}", scope.credentials.secret_access_key).as_bytes(),
        short_date.as_bytes(),
    );
    let region_key = hmac_sha256(&date_key, scope.region.as_bytes());
    let service_key = hmac_sha256(&region_key, scope.service.as_bytes());
    let signing_key = hmac_sha256(&service_key, b"aws4_request");
    let signature = hex::encode(hmac_sha256(&signing_key, string_to_sign.as_bytes()));
    set_header(
        request.headers,
        "authorization",
        format!(
            "AWS4-HMAC-SHA256 Credential={}/{credential_scope}, SignedHeaders={signed_headers}, Signature={signature}",
            scope.credentials.access_key_id
        ),
    );
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A request captured from the TS SDK (`@aws-sdk/client-bedrock-runtime`
    /// 3.1127) against a local server, with its signature.
    #[test]
    fn matches_the_sdk_signature() {
        let mut headers: Vec<(String, String)> = [
            ("content-type", "application/json"),
            ("content-length", "131"),
            ("x-amz-user-agent", "aws-sdk-js/3.1126.0"),
            ("user-agent", "aws-sdk-js/3.1126.0 ua/2.1 os/linux#6.18.50 lang/js md/nodejs#26.10.0 api/bedrock-runtime#3.1126.0 m/N,E,e"),
            ("host", "127.0.0.1:40851"),
            ("x-custom", "v"),
            ("amz-sdk-invocation-id", "3cddd098-db3c-485f-a034-681e429db393"),
            ("amz-sdk-request", "attempt=1; max=3"),
        ]
        .into_iter()
        .map(|(name, value)| (name.to_owned(), value.to_owned()))
        .collect();
        let body = br#"{"messages":[{"role":"user","content":[{"text":"hello"},{"cachePoint":{"type":"default"}}]}],"inferenceConfig":{"maxTokens":64000}}"#;
        let credentials = AwsCredentials {
            access_key_id: "AKIDEXAMPLE".into(),
            secret_access_key: "secret".into(),
            session_token: Some("sess".into()),
        };
        // 20261006T203527Z
        let now = UNIX_EPOCH + Duration::from_secs(1_791_318_927);
        sign_request(
            &mut SignableRequest {
                method: "POST",
                path: "/model/us.anthropic.claude-sonnet-4-5-20250929-v1%3A0/converse-stream",
                headers: &mut headers,
                body,
            },
            &SigningScope {
                credentials: &credentials,
                region: "us-west-2",
                service: "bedrock",
                now,
            },
        );
        let get = |name: &str| {
            headers
                .iter()
                .find(|(key, _)| key == name)
                .map(|(_, value)| value.as_str())
        };
        assert_eq!(get("x-amz-date"), Some("20261006T203527Z"));
        assert_eq!(get("x-amz-security-token"), Some("sess"));
        assert_eq!(
            get("x-amz-content-sha256"),
            Some("0176c117e24fc8abd9f897f648056fbcd506c34e126ea648fd0d7c9cd319d780")
        );
        assert_eq!(
            get("authorization"),
            Some("AWS4-HMAC-SHA256 Credential=AKIDEXAMPLE/20261006/us-west-2/bedrock/aws4_request, SignedHeaders=amz-sdk-invocation-id;amz-sdk-request;content-length;content-type;host;x-amz-content-sha256;x-amz-date;x-amz-security-token;x-amz-user-agent;x-custom, Signature=addad7cb00964361c2b954cf2cea1f5dce660a166eadccbaeb3d8f427617d023")
        );
    }

    #[test]
    fn double_encodes_the_canonical_path() {
        assert_eq!(
            canonical_path("/model/a%3Ab/converse-stream"),
            "/model/a%253Ab/converse-stream"
        );
        assert_eq!(canonical_path("/a/./b/../c/"), "/a/c/");
    }
}
