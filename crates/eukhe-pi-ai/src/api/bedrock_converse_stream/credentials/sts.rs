//! The STS role assumers of `@aws-sdk/nested-clients/sts`
//! (`getDefaultRoleAssumer`, `getDefaultRoleAssumerWithWebIdentity`) as raw
//! `awsQuery` requests, and `fromTokenFile` / `fromWebToken` of
//! `@aws-sdk/credential-provider-web-identity`.

use eukhe_types::pi_ai::JsonValue;
use reqwest::Method;

use super::super::client_config::AwsCredentials;
use super::super::sigv4::escape_uri;
use super::js_compat::{node_fs_error, now_ms};
use super::sdk_client::{
    classify_service_error, nested_client, retry_after_hint, reused_proxy, AttemptError,
    AwsService, HttpReply, NestedClientConfig, PreparedRequest, RetryErrorType,
};
use super::{ProviderFailure, ProviderResult, Resolution};
use crate::utils::diagnostics::ErrorObject;
use crate::utils::js::number_to_js_string;

/// The body of a raw `<Tag>…</Tag>` element (first occurrence), entities
/// decoded; `<Tag/>` reads as empty.
pub(crate) fn xml_tag_text(xml: &str, tag: &str) -> Option<String> {
    let open = format!("<{tag}>");
    let self_closing = format!("<{tag}/>");
    let open_at = xml.find(&open);
    let empty_at = xml.find(&self_closing);
    match (open_at, empty_at) {
        (Some(open_at), empty_at) if empty_at.is_none_or(|empty_at| open_at < empty_at) => {
            let start = open_at + open.len();
            let close = format!("</{tag}>");
            let end = xml[start..].find(&close)? + start;
            Some(decode_xml_entities(&xml[start..end]))
        }
        (_, Some(_)) => Some(String::new()),
        (_, None) => None,
    }
}

/// The text of the first `<Tag>` element inside the first `<Scope>` element.
fn scoped_tag_text(xml: &str, scope: &str, tag: &str) -> Option<String> {
    let open = format!("<{scope}>");
    let start = xml.find(&open)? + open.len();
    let close = format!("</{scope}>");
    let end = xml[start..]
        .find(&close)
        .map_or(xml.len(), |end| end + start);
    xml_tag_text(&xml[start..end], tag)
}

/// XML entity decoding (`&amp;`, `&lt;`, `&gt;`, `&quot;`, `&apos;`, `&#N;`, `&#xN;`).
fn decode_xml_entities(text: &str) -> String {
    let mut decoded = String::with_capacity(text.len());
    let mut rest = text;
    while let Some(amp) = rest.find('&') {
        decoded.push_str(&rest[..amp]);
        let after = &rest[amp..];
        let Some(semicolon) = after.find(';') else {
            decoded.push_str(after);
            return decoded;
        };
        let entity = &after[1..semicolon];
        let replacement = match entity {
            "amp" => Some('&'),
            "lt" => Some('<'),
            "gt" => Some('>'),
            "quot" => Some('"'),
            "apos" => Some('\''),
            _ => entity
                .strip_prefix("#x")
                .or_else(|| entity.strip_prefix("#X"))
                .and_then(|hex| u32::from_str_radix(hex, 16).ok())
                .or_else(|| entity.strip_prefix('#').and_then(|dec| dec.parse().ok()))
                .and_then(char::from_u32),
        };
        if let Some(c) = replacement {
            decoded.push(c);
            rest = &after[semicolon + 1..];
        } else {
            decoded.push('&');
            rest = &after[1..];
        }
    }
    decoded.push_str(rest);
    decoded
}

/// The SDK's error for a body its XML parser rejects.
fn xml_parse_error() -> ErrorObject {
    ErrorObject::new(
        "@aws-sdk XML parse error: unexpected content.\n  Deserialization error: to see the raw response, inspect the hidden field {error}.$response on this object.",
    )
}

/// Whether the XML parser rejects `body` (text that is not markup).
fn is_unparsable_xml(body: &str) -> bool {
    let trimmed = body.trim();
    !trimmed.is_empty() && !trimmed.starts_with('<')
}

/// STS modeled errors: `awsQueryError` code → exception name, and whether the
/// shape carries the `retryable` trait.
fn modeled_error(code: &str) -> Option<(&'static str, bool)> {
    match code {
        "ExpiredTokenException" => Some(("ExpiredTokenException", false)),
        "IDPCommunicationError" => Some(("IDPCommunicationErrorException", true)),
        "IDPRejectedClaim" => Some(("IDPRejectedClaimException", false)),
        "InvalidIdentityToken" => Some(("InvalidIdentityTokenException", false)),
        "MalformedPolicyDocument" => Some(("MalformedPolicyDocumentException", false)),
        "PackedPolicyTooLarge" => Some(("PackedPolicyTooLargeException", false)),
        "RegionDisabledException" => Some(("RegionDisabledException", false)),
        _ => None,
    }
}

/// The `awsQuery` error of a non-2xx STS response.
fn query_error(reply: &HttpReply) -> AttemptError {
    if is_unparsable_xml(&reply.body) {
        return AttemptError {
            error: xml_parse_error().thrown(),
            kind: RetryErrorType::ClientError,
            retry_after: None,
        };
    }
    let code = scoped_tag_text(&reply.body, "Error", "Code");
    let message =
        scoped_tag_text(&reply.body, "Error", "Message").unwrap_or_else(|| "Unknown".to_owned());
    let (name, retryable) = match code.as_deref() {
        Some(code) => modeled_error(code).map_or_else(
            || (code.to_owned(), false),
            |(name, retryable)| (name.to_owned(), retryable),
        ),
        None if reply.status == 404 => ("NotFound".to_owned(), false),
        None => ("Unknown".to_owned(), false),
    };
    let mut error = ErrorObject::named(name.clone(), message);
    error.metadata_http_status_code = Some(JsonValue::from(reply.status));
    AttemptError {
        kind: classify_service_error(&name, reply.status, retryable),
        error: error.thrown(),
        retry_after: retry_after_hint(&reply.headers),
    }
}

/// The `Credentials` of a successful `AssumeRole*` response; `Ok(None)` when
/// the keys are missing.
fn parse_credentials(reply: &HttpReply) -> Result<Option<AwsCredentials>, AttemptError> {
    if is_unparsable_xml(&reply.body) {
        return Err(AttemptError {
            error: xml_parse_error().thrown(),
            kind: RetryErrorType::ClientError,
            retry_after: None,
        });
    }
    let field =
        |tag| scoped_tag_text(&reply.body, "Credentials", tag).filter(|value| !value.is_empty());
    Ok(match (field("AccessKeyId"), field("SecretAccessKey")) {
        (Some(access_key_id), Some(secret_access_key)) => Some(AwsCredentials {
            access_key_id,
            secret_access_key,
            session_token: field("SessionToken"),
        }),
        _ => None,
    })
}

/// `x-www-form-urlencoded` body with the SDK's query serializer escaping.
fn query_body(pairs: &[(&str, String)]) -> Vec<u8> {
    pairs
        .iter()
        .map(|(key, value)| format!("{key}={}", escape_uri(value)))
        .collect::<Vec<_>>()
        .join("&")
        .into_bytes()
}

/// Send one STS operation and read its credentials.
async fn send_sts(
    resolution: &Resolution<'_>,
    region: &str,
    body: Vec<u8>,
    credentials: Option<&AwsCredentials>,
    invalid_message: String,
) -> ProviderResult<AwsCredentials> {
    let client = nested_client(
        resolution,
        &NestedClientConfig {
            service: AwsService::Sts,
            region,
            profile: resolution.caller.profile,
            proxy: reused_proxy(resolution.caller.request_handler),
        },
    )
    .await?;
    let request = PreparedRequest {
        method: Method::POST,
        path_and_query: "/".to_owned(),
        headers: vec![(
            "content-type".to_owned(),
            "application/x-www-form-urlencoded".to_owned(),
        )],
        body,
        credentials,
        attempt_headers: None,
    };
    let assumed = client
        .send(resolution, &request, |reply| {
            if (200..300).contains(&reply.status) {
                parse_credentials(&reply)
            } else {
                Err(query_error(&reply))
            }
        })
        .await?;
    assumed.ok_or_else(|| ProviderFailure::error(ErrorObject::new(invalid_message)))
}

/// `AssumeRole` request parameters.
#[derive(Debug, Clone, PartialEq)]
pub(crate) struct AssumeRoleParams {
    pub(crate) role_arn: String,
    pub(crate) role_session_name: String,
    pub(crate) external_id: Option<String>,
    pub(crate) duration_seconds: f64,
}

/// `roleAssumer(sourceCreds, params)`: SigV4-signed `AssumeRole`.
///
/// # Errors
///
/// The STS service error, `Invalid response from STS.assumeRole call with
/// role …`, or a client configuration error.
pub(crate) async fn assume_role(
    resolution: &Resolution<'_>,
    region: &str,
    source: &AwsCredentials,
    params: &AssumeRoleParams,
) -> ProviderResult<AwsCredentials> {
    let mut pairs = vec![
        ("Action", "AssumeRole".to_owned()),
        ("Version", "2011-06-15".to_owned()),
        ("RoleArn", params.role_arn.clone()),
        ("RoleSessionName", params.role_session_name.clone()),
        (
            "DurationSeconds",
            number_to_js_string(params.duration_seconds),
        ),
    ];
    if let Some(external_id) = &params.external_id {
        pairs.push(("ExternalId", external_id.clone()));
    }
    send_sts(
        resolution,
        region,
        query_body(&pairs),
        Some(source),
        format!(
            "Invalid response from STS.assumeRole call with role {}",
            params.role_arn
        ),
    )
    .await
}

/// `fromTokenFile` init fields (`undefined` falls back to the env vars).
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub(crate) struct TokenFileInit {
    pub(crate) web_identity_token_file: Option<String>,
    pub(crate) role_arn: Option<String>,
    pub(crate) role_session_name: Option<String>,
}

/// Node `readFileSync(path, { encoding: "ascii" })`.
fn read_ascii_file(path: &str) -> ProviderResult<String> {
    let bytes = std::fs::read(path)
        .map_err(|error| ProviderFailure::thrown(node_fs_error(&error, "open", path)))?;
    Ok(bytes.iter().map(|byte| char::from(byte & 0x7f)).collect())
}

/// `fromTokenFile(init)()`: an unsigned `AssumeRoleWithWebIdentity` in the
/// caller's region.
///
/// # Errors
///
/// `Web identity configuration not specified` (lets the chain continue), the
/// token file read error, or the STS error.
pub(crate) async fn from_token_file(
    resolution: &Resolution<'_>,
    init: TokenFileInit,
) -> ProviderResult<AwsCredentials> {
    let env = resolution.env;
    let token_file = init
        .web_identity_token_file
        .or_else(|| env.var("AWS_WEB_IDENTITY_TOKEN_FILE"));
    let role_arn = init.role_arn.or_else(|| env.var("AWS_ROLE_ARN"));
    let role_session_name = init
        .role_session_name
        .or_else(|| env.var("AWS_ROLE_SESSION_NAME"));
    let (Some(token_file), Some(role_arn)) = (
        token_file.filter(|file| !file.is_empty()),
        role_arn.filter(|arn| !arn.is_empty()),
    ) else {
        return Err(ProviderFailure::credentials(
            "Web identity configuration not specified",
        ));
    };
    let web_identity_token = read_ascii_file(&token_file)?;
    let role_session_name = role_session_name
        .unwrap_or_else(|| format!("aws-sdk-js-session-{}", number_to_js_string(now_ms())));
    let pairs = [
        ("Action", "AssumeRoleWithWebIdentity".to_owned()),
        ("Version", "2011-06-15".to_owned()),
        ("RoleArn", role_arn.clone()),
        ("RoleSessionName", role_session_name),
        ("WebIdentityToken", web_identity_token),
    ];
    send_sts(
        resolution,
        resolution.caller.region,
        query_body(&pairs),
        None,
        format!("Invalid response from STS.assumeRoleWithWebIdentity call with role {role_arn}"),
    )
    .await
}
