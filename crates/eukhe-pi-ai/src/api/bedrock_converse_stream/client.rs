//! The slice of `BedrockRuntimeClient.send(new ConverseStreamCommand(...))`
//! the TS module relies on, over raw HTTP: endpoint resolution, the request
//! headers and SigV4/bearer signing, the caller-header and response-header
//! middlewares, the standard retry strategy (3 attempts), clock-skew
//! correction, `awsRestJson1` error deserialization, and the event-stream
//! unmarshalling of the response (whose first event is read eagerly inside
//! `send`, like the SDK's `deserializeEventStream`).
//!
//! Transport: HTTP/1.1 (the SDK's `NodeHttpHandler`, which TS selects with
//! `AWS_BEDROCK_FORCE_HTTP1=1` or a proxy) for every request.

// Failures carry the SDK error shape the TS catch inspects; they are cold,
// so the `Result` size is not worth boxing.
#![allow(clippy::result_large_err)]

use std::collections::VecDeque;
use std::sync::LazyLock;
use std::time::{Duration, SystemTime, UNIX_EPOCH};

use eukhe_chord::context::AbortSignal;
use eukhe_types::pi_ai::{IndexMap, JsonObject, JsonValue, Model, ProviderResponse};
use regex::Regex;

use super::client_config::{AwsCredentials, BedrockClientConfig, BedrockRequestHandler};
use super::credentials::{resolve_default_credentials, resolve_default_region};
use super::event_stream_codec::{decode_message, EventMessage, HeaderValue, MessageChunker};
use super::shape_codec::{deserialize_struct, Shape};
use super::sigv4::{escape_uri, set_header, sign_request, SignableRequest, SigningScope};
use super::smithy_schema::STREAM_OUTPUT;
use crate::types::OnResponse;
use crate::utils::diagnostics::{
    DiagnosticCode, ErrorObject, SdkResponse, SdkValue, Thrown, ThrownValue,
};
use crate::utils::js::js_to_string;
use crate::utils::json_parse::json_parse;
use crate::utils::provider_env::get_provider_env_value;

/// The SDK version the request headers announce.
const SDK_VERSION: &str = "3.1126.0";

/// `DEFAULT_MAX_ATTEMPTS`.
const MAX_ATTEMPTS: u32 = 3;
/// `DEFAULT_RETRY_DELAY_BASE` / `THROTTLING_RETRY_DELAY_BASE` / `MAXIMUM_RETRY_DELAY`.
const RETRY_DELAY_BASE_MS: f64 = 100.0;
const THROTTLING_RETRY_DELAY_BASE_MS: f64 = 500.0;
const MAXIMUM_RETRY_DELAY_MS: f64 = 20_000.0;

/// The deserializer middleware's hint for failures while reading a response.
pub(crate) const DESERIALIZATION_HINT: &str =
    "\n  Deserialization error: to see the raw response, inspect the hidden field {error}.$response on this object.";

const THROTTLING_ERROR_CODES: [&str; 14] = [
    "BandwidthLimitExceeded",
    "EC2ThrottledException",
    "LimitExceededException",
    "PriorRequestNotComplete",
    "ProvisionedThroughputExceededException",
    "RequestLimitExceeded",
    "RequestThrottled",
    "RequestThrottledException",
    "SlowDown",
    "ThrottledException",
    "Throttling",
    "ThrottlingException",
    "TooManyRequestsException",
    "TransactionInProgressException",
];
const TRANSIENT_ERROR_CODES: [&str; 3] =
    ["TimeoutError", "RequestTimeout", "RequestTimeoutException"];
const TRANSIENT_ERROR_STATUS_CODES: [u16; 4] = [500, 502, 503, 504];
const NODEJS_TRANSIENT_CODES: [&str; 8] = [
    "ECONNRESET",
    "ECONNREFUSED",
    "EPIPE",
    "ETIMEDOUT",
    "EHOSTUNREACH",
    "ENETUNREACH",
    "ENOTFOUND",
    "EAI_AGAIN",
];

/// `$metadata` of an SDK error.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub(crate) struct SdkMetadata {
    pub(crate) http_status_code: Option<u16>,
    pub(crate) request_id: Option<String>,
    pub(crate) clock_skew_corrected: bool,
}

/// An `Error` the AWS SDK throws out of `send()` or the event stream.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct SdkError {
    pub(crate) name: String,
    pub(crate) message: String,
    /// `instanceof BedrockRuntimeServiceException`.
    pub(crate) service_exception: bool,
    /// `"$metadata" in error`: `None` when the property is absent; a modeled
    /// event-stream exception has the property with an `undefined` value
    /// (`Some` with every field empty).
    pub(crate) metadata: Option<SdkMetadata>,
    /// Node's `err.code` (`ECONNREFUSED`, ...).
    pub(crate) code: Option<String>,
    /// The modeled `@retryable` trait (`$retryable`).
    pub(crate) retryable: bool,
    /// `$response` headers, when the error carries the raw response.
    pub(crate) response_headers: Option<Vec<(String, String)>>,
}

impl SdkError {
    /// A plain `Error` with a name.
    pub(crate) fn plain(name: impl Into<String>, message: impl Into<String>) -> Self {
        Self {
            name: name.into(),
            message: message.into(),
            service_exception: false,
            metadata: None,
            code: None,
            retryable: false,
            response_headers: None,
        }
    }

    fn with_code(mut self, code: &str) -> Self {
        self.code = Some(code.to_owned());
        self
    }

    /// The `ErrorObject` view `normalizeProviderError` probes.
    pub(crate) fn to_error_object(&self) -> ErrorObject {
        ErrorObject {
            name: self.name.clone(),
            message: self.message.clone(),
            code: self.code.clone().map(DiagnosticCode::String),
            metadata_http_status_code: self
                .metadata
                .as_ref()
                .and_then(|metadata| metadata.http_status_code)
                .map(JsonValue::from),
            response: self.response_headers.as_ref().map(|_| SdkResponse {
                status_code: None,
                // The raw response body is an already consumed stream.
                body: Some(SdkValue::Stream),
            }),
            ..ErrorObject::default()
        }
    }
}

/// What a Bedrock request or stream failed with (TS `unknown` in `catch`).
#[derive(Debug, Clone)]
pub(crate) enum BedrockFailure {
    Sdk(SdkError),
    Thrown(Thrown),
}

impl From<Thrown> for BedrockFailure {
    fn from(thrown: Thrown) -> Self {
        Self::Thrown(thrown)
    }
}

impl From<SdkError> for BedrockFailure {
    fn from(error: SdkError) -> Self {
        Self::Sdk(error)
    }
}

/// The node handler's `AbortError` for an aborted request.
fn request_aborted() -> SdkError {
    SdkError::plain("AbortError", "Request aborted")
}

/// One unmarshalled `ConverseStreamOutput` item: `{ [member]: value }`.
#[derive(Debug, Clone)]
pub(crate) struct StreamItem {
    pub(crate) member: String,
    pub(crate) value: StreamValue,
}

/// The value of a stream item.
#[derive(Debug, Clone)]
pub(crate) enum StreamValue {
    /// A deserialized event structure.
    Data(JsonValue),
    /// A modeled exception delivered as an event member.
    Exception(SdkError, JsonObject),
}

impl StreamItem {
    /// The item as the SDK yields it (blobs as base64).
    pub(crate) fn to_json(&self) -> JsonValue {
        let value = match &self.value {
            StreamValue::Data(data) => data.clone(),
            StreamValue::Exception(error, data) => {
                let mut object = JsonObject::new();
                object.insert("name".to_owned(), error.name.clone().into());
                if let Some(fault) = data.get("$fault") {
                    object.insert("$fault".to_owned(), fault.clone());
                }
                object.insert("message".to_owned(), error.message.clone().into());
                for (key, item) in data {
                    object.insert(key.clone(), item.clone());
                }
                JsonValue::Object(object)
            }
        };
        let mut item = JsonObject::new();
        item.insert(self.member.clone(), value);
        JsonValue::Object(item)
    }
}

/// The request `stream` sends.
pub(crate) struct SendRequest<'a> {
    pub(crate) model: &'a Model,
    /// The `modelId` HTTP label (from the possibly replaced payload).
    pub(crate) model_id: String,
    pub(crate) config: &'a BedrockClientConfig,
    /// The serialized `ConverseStreamRequest` body.
    pub(crate) body: String,
    /// The caller headers (TS `providerHeadersToRecord(options.headers)`).
    pub(crate) custom_headers: Option<&'a IndexMap<String, String>>,
    pub(crate) on_response: Option<&'a OnResponse<Model>>,
    pub(crate) signal: Option<&'a AbortSignal>,
}

/// TS `isReservedHeader`: `host`, `authorization`, and `x-amz-*` participate
/// in signing and are never overwritten by caller headers.
fn is_reserved_header(key: &str) -> bool {
    let lower = key.to_lowercase();
    lower.starts_with("x-amz-") || lower == "authorization" || lower == "host"
}

/// The `aws.partition` outputs: `(dnsSuffix, dualStackDnsSuffix)`.
fn partition_dns_suffixes(region: &str) -> (&'static str, &'static str) {
    static PARTITIONS: LazyLock<Vec<(Regex, &'static str, &'static str, &'static str)>> =
        LazyLock::new(|| {
            [
                (
                    r"^(us|eu|ap|sa|ca|me|af|il|mx)\-\w+\-\d+$",
                    "aws",
                    "amazonaws.com",
                    "api.aws",
                ),
                (
                    r"^cn\-\w+\-\d+$",
                    "aws-cn",
                    "amazonaws.com.cn",
                    "api.amazonwebservices.com.cn",
                ),
                (
                    r"^eusc\-(de)\-\w+\-\d+$",
                    "aws-eusc",
                    "amazonaws.eu",
                    "api.amazonwebservices.eu",
                ),
                (
                    r"^us\-iso\-\w+\-\d+$",
                    "aws-iso",
                    "c2s.ic.gov",
                    "api.aws.ic.gov",
                ),
                (
                    r"^us\-isob\-\w+\-\d+$",
                    "aws-iso-b",
                    "sc2s.sgov.gov",
                    "api.aws.scloud",
                ),
                (
                    r"^eu\-isoe\-\w+\-\d+$",
                    "aws-iso-e",
                    "cloud.adc-e.uk",
                    "api.cloud-aws.adc-e.uk",
                ),
                (
                    r"^us\-isof\-\w+\-\d+$",
                    "aws-iso-f",
                    "csp.hci.ic.gov",
                    "api.aws.hci.ic.gov",
                ),
                (
                    r"^us\-gov\-\w+\-\d+$",
                    "aws-us-gov",
                    "amazonaws.com",
                    "api.aws",
                ),
            ]
            .into_iter()
            .map(|(pattern, id, dns, dual)| {
                (
                    Regex::new(pattern).unwrap_or_else(|_| unreachable!("static regex")),
                    id,
                    dns,
                    dual,
                )
            })
            .collect()
        });
    // Global pseudo-regions name their partition.
    if let Some(id) = region.strip_suffix("-global") {
        if let Some((_, _, dns, dual)) = PARTITIONS.iter().find(|(_, pid, _, _)| *pid == id) {
            return (dns, dual);
        }
    }
    // `us-gov-*` also matches the `aws` pattern's `us-…` prefix; the SDK
    // checks the explicit region lists first, which keep GovCloud separate.
    let mut matched = None;
    for (pattern, id, dns, dual) in PARTITIONS.iter() {
        if pattern.is_match(region) {
            matched = Some((*id, *dns, *dual));
            if *id != "aws" {
                break;
            }
        }
    }
    matched.map_or(("amazonaws.com", "api.aws"), |(_, dns, dual)| (dns, dual))
}

/// The SDK's boolean env config (`booleanSelector`).
fn boolean_env(name: &str) -> Result<bool, SdkError> {
    match get_provider_env_value(name, None).as_deref() {
        None | Some("false") => Ok(false),
        Some("true") => Ok(true),
        Some(other) => Err(SdkError::plain(
            "Error",
            format!("Cannot load env \"{name}\". Expected \"true\" or \"false\", got {other}."),
        )),
    }
}

/// The endpoint ruleset of `bedrock-runtime`.
fn resolve_endpoint(config: &BedrockClientConfig, region: &str) -> Result<url::Url, SdkError> {
    let use_fips = boolean_env("AWS_USE_FIPS_ENDPOINT")?;
    let use_dual_stack = boolean_env("AWS_USE_DUALSTACK_ENDPOINT")?;
    let endpoint = if let Some(endpoint) = &config.endpoint {
        if use_fips {
            return Err(SdkError::plain(
                "Error",
                "Invalid Configuration: FIPS and custom endpoint are not supported",
            ));
        }
        if use_dual_stack {
            return Err(SdkError::plain(
                "Error",
                "Invalid Configuration: Dualstack and custom endpoint are not supported",
            ));
        }
        endpoint.clone()
    } else {
        let (dns_suffix, dual_stack_suffix) = partition_dns_suffixes(region);
        let suffix = if use_dual_stack {
            dual_stack_suffix
        } else {
            dns_suffix
        };
        let host = if use_fips {
            "bedrock-runtime-fips"
        } else {
            "bedrock-runtime"
        };
        format!("https://{host}.{region}.{suffix}")
    };
    url::Url::parse(&endpoint)
        .map_err(|_| SdkError::plain("TypeError", format!("Invalid URL: {endpoint}")))
}

/// `findHeader(/^x-[\w-]+-request-?id$/, headers)` of the deserializer
/// middleware.
fn find_request_id_header(headers: &[(String, String)]) -> Option<String> {
    static PATTERN: LazyLock<Regex> = LazyLock::new(|| {
        Regex::new(r"^x-[\w-]+-request-?id$").unwrap_or_else(|_| unreachable!("static regex"))
    });
    headers
        .iter()
        .find(|(name, _)| PATTERN.is_match(name))
        .map(|(_, value)| value.clone())
}

/// `deserializeMetadata().requestId`.
fn metadata_request_id(headers: &[(String, String)]) -> Option<String> {
    ["x-amzn-requestid", "x-amzn-request-id", "x-amz-request-id"]
        .iter()
        .find_map(|name| {
            headers
                .iter()
                .find(|(key, _)| key == name)
                .map(|(_, value)| value.clone())
        })
}

/// The response headers in arrival order, lowercased, duplicates joined
/// with `, ` (node's `IncomingMessage.headers`).
fn response_headers(response: &reqwest::Response) -> Vec<(String, String)> {
    let mut headers: Vec<(String, String)> = Vec::new();
    for (name, value) in response.headers() {
        let value = String::from_utf8_lossy(value.as_bytes()).into_owned();
        match headers.iter_mut().find(|(key, _)| key == name.as_str()) {
            Some(entry) => {
                entry.1.push_str(", ");
                entry.1.push_str(&value);
            }
            None => headers.push((name.as_str().to_owned(), value)),
        }
    }
    headers
}

/// RFC 7231 IMF-fixdate (`Tue, 06 Oct 2026 20:25:28 GMT`) in epoch ms.
fn parse_http_date(value: &str) -> Option<i64> {
    let parts: Vec<&str> = value.split_whitespace().collect();
    let [_, day, month, year, time, "GMT"] = parts.as_slice() else {
        return None;
    };
    let month = i64::from(
        u8::try_from(
            [
                "Jan", "Feb", "Mar", "Apr", "May", "Jun", "Jul", "Aug", "Sep", "Oct", "Nov", "Dec",
            ]
            .iter()
            .position(|name| name == month)?,
        )
        .ok()?,
    ) + 1;
    let day: i64 = day.parse().ok()?;
    let year: i64 = year.parse().ok()?;
    let mut clock = time.split(':').map(str::parse::<i64>);
    let (Some(Ok(hour)), Some(Ok(minute)), Some(Ok(second))) =
        (clock.next(), clock.next(), clock.next())
    else {
        return None;
    };
    // Days from civil (Howard Hinnant).
    let y = if month <= 2 { year - 1 } else { year };
    let era = y.div_euclid(400);
    let yoe = y.rem_euclid(400);
    let mp = (month + 9) % 12;
    let doy = (153 * mp + 2) / 5 + day - 1;
    let doe = yoe * 365 + yoe / 4 - yoe / 100 + doy;
    let days = era * 146_097 + doe - 719_468;
    Some(((days * 86_400) + hour * 3600 + minute * 60 + second) * 1000)
}

fn now_ms() -> i64 {
    SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .map_or(0, |elapsed| {
            i64::try_from(elapsed.as_millis()).unwrap_or(i64::MAX)
        })
}

/// The per-client mutable state the SDK keeps (`systemClockOffset`).
#[derive(Default)]
struct ClockSkew {
    offset_ms: i64,
}

impl ClockSkew {
    /// `getUpdatedSystemClockOffset`; `true` when the offset changed.
    fn update(&mut self, headers: &[(String, String)]) -> bool {
        let Some(server_ms) = headers
            .iter()
            .find(|(name, _)| name == "date")
            .and_then(|(_, value)| parse_http_date(value))
        else {
            return false;
        };
        let local = now_ms() + self.offset_ms;
        if (local - server_ms).abs() >= 300_000 {
            let next = server_ms - now_ms();
            let changed = next != self.offset_ms;
            self.offset_ms = next;
            return changed;
        }
        false
    }

    fn signing_time(&self) -> SystemTime {
        let ms = now_ms() + self.offset_ms;
        UNIX_EPOCH + Duration::from_millis(u64::try_from(ms).unwrap_or(0))
    }
}

/// The retry classification of `getRetryErrorType`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum RetryErrorType {
    Throttling,
    Transient,
    ServerError,
    ClientError,
}

fn retry_error_type(error: &SdkError) -> RetryErrorType {
    let status = error
        .metadata
        .as_ref()
        .and_then(|metadata| metadata.http_status_code);
    if status == Some(429) || THROTTLING_ERROR_CODES.contains(&error.name.as_str()) {
        return RetryErrorType::Throttling;
    }
    let transient = error.name != "AbortError"
        && (error.retryable
            || error
                .metadata
                .as_ref()
                .is_some_and(|metadata| metadata.clock_skew_corrected)
            || (error.name == "InvalidSignatureException"
                && error.message.contains("Signature expired"))
            || TRANSIENT_ERROR_CODES.contains(&error.name.as_str())
            || error
                .code
                .as_deref()
                .is_some_and(|code| NODEJS_TRANSIENT_CODES.contains(&code))
            || status.is_some_and(|status| TRANSIENT_ERROR_STATUS_CODES.contains(&status)));
    if transient {
        return RetryErrorType::Transient;
    }
    if status.is_some_and(|status| (500..=599).contains(&status)) {
        return RetryErrorType::ServerError;
    }
    RetryErrorType::ClientError
}

/// `parseRetryAfterHeader` of the error's raw response, in ms from now.
// Millisecond differences are far below 2^53.
#[allow(clippy::cast_precision_loss)]
fn retry_after_hint_ms(error: &SdkError) -> Option<f64> {
    for (name, value) in error.response_headers.as_ref()? {
        if name == "retry-after" {
            if value.ends_with("GMT") {
                return parse_http_date(value).map(|at| (at - now_ms()) as f64);
            }
            return value
                .parse::<f64>()
                .ok()
                .filter(|seconds| seconds.is_finite())
                .map(|seconds| seconds * 1000.0);
        }
        if name == "x-amz-retry-after" {
            return value.parse::<f64>().ok().filter(|ms| ms.is_finite());
        }
    }
    None
}

/// `StandardRetryStrategy.refreshRetryTokenForRetry`'s delay.
// The delay is a non-negative millisecond count far below 2^53.
#[allow(clippy::cast_possible_truncation, clippy::cast_sign_loss)]
fn retry_delay_ms(error: &SdkError, error_type: RetryErrorType, retry_count: u32) -> u64 {
    let base = if error_type == RetryErrorType::Throttling {
        THROTTLING_RETRY_DELAY_BASE_MS
    } else {
        RETRY_DELAY_BASE_MS
    };
    let ceiling = (base * 2f64.powi(i32::try_from(retry_count).unwrap_or(i32::MAX)))
        .min(MAXIMUM_RETRY_DELAY_MS);
    let delay = (rand::random::<f64>() * ceiling).floor();
    let delay = match retry_after_hint_ms(error) {
        Some(hint) => delay.max(hint.min(delay + 5_000.0)),
        None => delay,
    };
    delay.clamp(0.0, MAXIMUM_RETRY_DELAY_MS) as u64
}

/// The user agent the SDK sends (`os/<platform>#<release>`).
fn user_agent(bearer: bool) -> String {
    let platform = match std::env::consts::OS {
        "macos" => "darwin",
        other => other,
    };
    let release = rustix::system::uname()
        .release()
        .to_string_lossy()
        .into_owned();
    let features = if bearer { "N,E" } else { "N,E,e" };
    format!(
        "aws-sdk-js/{SDK_VERSION} ua/2.1 os/{platform}#{release} lang/rust api/bedrock-runtime#{SDK_VERSION} m/{features}"
    )
}

/// The HTTP client of one request handler.
fn http_client(handler: &BedrockRequestHandler) -> Result<reqwest::Client, SdkError> {
    let builder = reqwest::Client::builder().http1_only();
    let builder = match handler {
        BedrockRequestHandler::Proxy(proxy) => builder.proxy(
            reqwest::Proxy::all(proxy.as_str())
                .map_err(|error| SdkError::plain("Error", error.to_string()))?,
        ),
        BedrockRequestHandler::Default | BedrockRequestHandler::Http1 => builder.no_proxy(),
    };
    builder
        .build()
        .map_err(|error| SdkError::plain("Error", error.to_string()))
}

/// Node's error for a failed request (before any response).
fn connection_error(error: &reqwest::Error, url: &url::Url) -> SdkError {
    let host = url.host_str().unwrap_or_default().to_owned();
    let port = url.port_or_known_default().unwrap_or(443);
    let io_kind = std::iter::successors(
        Some(error as &(dyn std::error::Error + 'static)),
        |source| source.source(),
    )
    .find_map(|source| source.downcast_ref::<std::io::Error>())
    .map(std::io::Error::kind);
    let text = error.to_string().to_lowercase();
    if error.is_connect() {
        return match io_kind {
            Some(std::io::ErrorKind::ConnectionRefused) => {
                SdkError::plain("Error", format!("connect ECONNREFUSED {host}:{port}"))
                    .with_code("ECONNREFUSED")
            }
            Some(std::io::ErrorKind::TimedOut) => {
                SdkError::plain("Error", format!("connect ETIMEDOUT {host}:{port}"))
                    .with_code("ETIMEDOUT")
            }
            _ if text.contains("dns") => {
                SdkError::plain("Error", format!("getaddrinfo ENOTFOUND {host}"))
                    .with_code("ENOTFOUND")
            }
            _ => SdkError::plain("Error", error.to_string()),
        };
    }
    SdkError::plain("Error", "socket hang up").with_code("ECONNRESET")
}

/// Node's error for a response body that failed mid-read.
fn body_aborted() -> SdkError {
    SdkError::plain("Error", "aborted").with_code("ECONNRESET")
}

/// A response body reader that fails like node when the signal aborts.
struct BodyReader {
    response: reqwest::Response,
    signal: Option<AbortSignal>,
}

impl BodyReader {
    async fn chunk(&mut self) -> Result<Option<bytes::Bytes>, SdkError> {
        let next = self.response.chunk();
        let result = match &self.signal {
            Some(signal) => {
                if signal.aborted() {
                    return Err(body_aborted());
                }
                tokio::select! {
                    _ = signal.cancelled() => return Err(body_aborted()),
                    result = next => result,
                }
            }
            None => next.await,
        };
        result.map_err(|_| body_aborted())
    }

    async fn text(&mut self) -> Result<String, SdkError> {
        let mut bytes = Vec::new();
        while let Some(chunk) = self.chunk().await? {
            bytes.extend_from_slice(&chunk);
        }
        Ok(String::from_utf8_lossy(&bytes).into_owned())
    }
}

/// The event stream of a `ConverseStream` response.
pub(crate) struct ConverseStream {
    body: BodyReader,
    chunker: MessageChunker,
    pending: VecDeque<Result<Vec<u8>, SdkError>>,
    finished: bool,
    first: Option<StreamItem>,
    /// `response.$metadata.requestId`.
    pub(crate) request_id: Option<String>,
}

/// A header value that must be present (`message.headers[name].value`).
fn required_header<'a>(message: &'a EventMessage, name: &str) -> Result<&'a HeaderValue, SdkError> {
    message.headers.get(name).ok_or_else(|| {
        SdkError::plain(
            "TypeError",
            "Cannot read properties of undefined (reading 'value')",
        )
    })
}

fn header_string(value: &HeaderValue) -> String {
    value.to_js_string()
}

/// `JSON.parse` of an event body (`{}` for an empty body).
fn parse_body(body: &[u8]) -> Result<JsonValue, SdkError> {
    if body.is_empty() {
        return Ok(JsonValue::Object(JsonObject::new()));
    }
    json_parse(&String::from_utf8_lossy(body))
        .map_err(|error| SdkError::plain("SyntaxError", error.message))
}

/// `getMessageUnmarshaller` + `deserializeEventStream` for one message:
/// `Ok(None)` for an unknown event (skipped).
fn unmarshal_message(message: &EventMessage) -> Result<Option<StreamItem>, BedrockFailure> {
    let Some(message_type) = message.headers.get(":message-type") else {
        return Err(BedrockFailure::Sdk(SdkError::plain(
            "TypeError",
            "Cannot destructure property 'value' of 'message.headers[\":message-type\"]' as it is undefined.",
        )));
    };
    match message_type {
        HeaderValue::String(kind) if kind == "error" => {
            let error_message = header_string(required_header(message, ":error-message")?);
            let code = header_string(required_header(message, ":error-code")?);
            let error_message = if error_message.is_empty() {
                "UnknownError".to_owned()
            } else {
                error_message
            };
            Err(BedrockFailure::Sdk(SdkError::plain(code, error_message)))
        }
        HeaderValue::String(kind) if kind == "exception" => {
            let code = header_string(required_header(message, ":exception-type")?);
            match STREAM_OUTPUT.member(&code) {
                Some(Shape::Struct(shape)) => {
                    let data = parse_body(&message.body)?;
                    let data = match &data {
                        JsonValue::Object(object) => deserialize_struct(shape, false, object)
                            .map_err(|error| SdkError::plain(error.name, error.message))?,
                        _ => JsonObject::new(),
                    };
                    match exception_fault(shape.name) {
                        Some(fault) => Err(BedrockFailure::Sdk(stream_exception(
                            shape.name, fault, &data,
                        ))),
                        // A non-error member thrown as a bare object.
                        None => Err(BedrockFailure::Thrown(
                            ThrownValue(JsonValue::Object(data)).thrown(),
                        )),
                    }
                }
                _ => Err(BedrockFailure::Sdk(SdkError::plain(
                    code,
                    String::from_utf8_lossy(&message.body).into_owned(),
                ))),
            }
        }
        HeaderValue::String(kind) if kind == "event" => {
            let event_type = header_string(required_header(message, ":event-type")?);
            let Some(Shape::Struct(shape)) = STREAM_OUTPUT.member(&event_type) else {
                return Ok(None);
            };
            let data = parse_body(&message.body)?;
            if let Some(fault) = exception_fault(shape.name) {
                let data = match &data {
                    JsonValue::Object(object) => deserialize_struct(shape, false, object)
                        .map_err(|error| SdkError::plain(error.name, error.message))?,
                    _ => JsonObject::new(),
                };
                let error = stream_exception(shape.name, fault, &data);
                return Ok(Some(StreamItem {
                    member: event_type,
                    value: StreamValue::Exception(error, data),
                }));
            }
            let value = match &data {
                JsonValue::Object(object) => JsonValue::Object(
                    deserialize_struct(shape, false, object)
                        .map_err(|error| SdkError::plain(error.name, error.message))?,
                ),
                other => other.clone(),
            };
            Ok(Some(StreamItem {
                member: event_type,
                value: StreamValue::Data(value),
            }))
        }
        _ => {
            let event_type = message
                .headers
                .get(":event-type")
                .map_or_else(|| "undefined".to_owned(), header_string);
            Err(BedrockFailure::Sdk(SdkError::plain(
                "Error",
                format!("Unrecognizable event type: {event_type}"),
            )))
        }
    }
}

/// The `$fault` of a modeled event-stream exception structure.
fn exception_fault(shape_name: &str) -> Option<&'static str> {
    match shape_name {
        "InternalServerException" | "ServiceUnavailableException" => Some("server"),
        "ModelStreamErrorException" | "ValidationException" | "ThrottlingException" => {
            Some("client")
        }
        _ => None,
    }
}

/// `readEventMember` for an error structure: the modeled exception, whose
/// message is `message ?? Message ?? "Unknown"`.
fn stream_exception(name: &str, _fault: &str, data: &JsonObject) -> SdkError {
    let message = data
        .get("message")
        .or_else(|| data.get("Message"))
        .filter(|value| !value.is_null())
        .map_or_else(|| "Unknown".to_owned(), js_to_string);
    SdkError {
        name: name.to_owned(),
        message,
        service_exception: true,
        metadata: Some(SdkMetadata::default()),
        code: None,
        retryable: false,
        response_headers: None,
    }
}

impl ConverseStream {
    fn new(body: BodyReader, request_id: Option<String>) -> Self {
        Self {
            body,
            chunker: MessageChunker::default(),
            pending: VecDeque::new(),
            finished: false,
            first: None,
            request_id,
        }
    }

    /// The next raw message, `None` at the end of the body.
    async fn next_message(&mut self) -> Result<Option<Vec<u8>>, SdkError> {
        loop {
            if let Some(message) = self.pending.pop_front() {
                return message.map(Some);
            }
            if self.finished {
                return Ok(None);
            }
            if let Some(chunk) = self.body.chunk().await? {
                self.pending
                    .extend(self.chunker.push(&chunk).into_iter().map(|message| {
                        message.map_err(|error| SdkError::plain(error.name, error.message))
                    }));
            } else {
                self.finished = true;
                self.chunker
                    .finish()
                    .map_err(|error| SdkError::plain(error.name, error.message))?;
            }
        }
    }

    async fn read_item(&mut self) -> Result<Option<StreamItem>, BedrockFailure> {
        loop {
            let Some(bytes) = self.next_message().await.map_err(BedrockFailure::Sdk)? else {
                return Ok(None);
            };
            let message = decode_message(&bytes)
                .map_err(|error| BedrockFailure::Sdk(SdkError::plain(error.name, error.message)))?;
            if let Some(item) = unmarshal_message(&message)? {
                return Ok(Some(item));
            }
        }
    }

    /// The next stream item (TS `for await (const item of response.stream)`).
    pub(crate) async fn next_item(&mut self) -> Result<Option<StreamItem>, BedrockFailure> {
        if let Some(first) = self.first.take() {
            return Ok(Some(first));
        }
        self.read_item().await
    }
}

/// The outcome of one attempt.
enum AttemptError {
    /// An SDK error, subject to the retry strategy.
    Sdk(SdkError),
    /// A non-SDK failure (the `onResponse` callback, a bare thrown object):
    /// not retried.
    Fatal(BedrockFailure),
}

/// TS `client.send(command, { abortSignal })`.
// Mirrors the SDK middleware stack in order; splitting it would hide that.
#[allow(clippy::too_many_lines)]
pub(crate) async fn send(request: SendRequest<'_>) -> Result<ConverseStream, BedrockFailure> {
    let config = request.config;
    let region = match &config.region {
        Some(region) => region.clone(),
        None => resolve_default_region(config.profile.as_deref(), request.signal).await?,
    };
    let endpoint = resolve_endpoint(config, &region).map_err(BedrockFailure::Sdk)?;
    let bearer = config.uses_bearer_token();
    let credentials = if bearer {
        None
    } else {
        Some(match &config.credentials {
            Some(credentials) => credentials.clone(),
            None => {
                resolve_default_credentials(
                    config.profile.as_deref(),
                    &region,
                    &config.request_handler,
                    request.signal,
                )
                .await?
            }
        })
    };
    let client = http_client(&config.request_handler).map_err(BedrockFailure::Sdk)?;

    let path = format!(
        "{}/model/{}/converse-stream",
        endpoint.path().trim_end_matches('/'),
        escape_uri(&request.model_id)
    );
    let mut url = endpoint.clone();
    url.set_path(&path);
    let host = match url.port() {
        Some(port) => format!("{}:{port}", url.host_str().unwrap_or_default()),
        None => url.host_str().unwrap_or_default().to_owned(),
    };

    let mut base_headers: Vec<(String, String)> = vec![
        ("content-type".to_owned(), "application/json".to_owned()),
        ("content-length".to_owned(), request.body.len().to_string()),
        (
            "x-amz-user-agent".to_owned(),
            format!("aws-sdk-js/{SDK_VERSION}"),
        ),
        ("user-agent".to_owned(), user_agent(bearer)),
        ("host".to_owned(), host),
    ];
    // TS `addCustomHeadersMiddleware` (build step, before signing).
    if let Some(custom) = request.custom_headers {
        for (key, value) in custom {
            if !is_reserved_header(key) {
                set_header(&mut base_headers, key, value.clone());
            }
        }
    }
    set_header(
        &mut base_headers,
        "amz-sdk-invocation-id",
        uuid::Uuid::new_v4().to_string(),
    );

    let mut clock = ClockSkew::default();
    let mut attempts: u32 = 0;
    loop {
        let mut headers = base_headers.clone();
        set_header(
            &mut headers,
            "amz-sdk-request",
            format!("attempt={}; max={MAX_ATTEMPTS}", attempts + 1),
        );
        let outcome = attempt(
            &request,
            &client,
            &url,
            &region,
            credentials.as_ref(),
            headers,
            &mut clock,
        )
        .await;
        let error = match outcome {
            Ok(stream) => return Ok(stream),
            Err(AttemptError::Fatal(failure)) => return Err(failure),
            Err(AttemptError::Sdk(error)) => error,
        };
        let error_type = retry_error_type(&error);
        let retryable = matches!(
            error_type,
            RetryErrorType::Throttling | RetryErrorType::Transient
        );
        if !retryable || attempts + 1 >= MAX_ATTEMPTS {
            return Err(BedrockFailure::Sdk(error));
        }
        let delay = Duration::from_millis(retry_delay_ms(&error, error_type, attempts));
        match request.signal {
            Some(signal) => {
                tokio::select! {
                    _ = signal.cancelled() => {}
                    () = tokio::time::sleep(delay) => {}
                }
            }
            None => tokio::time::sleep(delay).await,
        }
        attempts += 1;
    }
}

/// One attempt: sign, send, `onResponse`, deserialize the error or the
/// first event.
async fn attempt(
    request: &SendRequest<'_>,
    client: &reqwest::Client,
    url: &url::Url,
    region: &str,
    credentials: Option<&AwsCredentials>,
    mut headers: Vec<(String, String)>,
    clock: &mut ClockSkew,
) -> Result<ConverseStream, AttemptError> {
    if request.signal.is_some_and(AbortSignal::aborted) {
        return Err(AttemptError::Sdk(request_aborted()));
    }
    let path = url.path().to_owned();
    match (credentials, &request.config.token) {
        (Some(credentials), _) => sign_request(
            &mut SignableRequest {
                method: "POST",
                path: &path,
                headers: &mut headers,
                body: request.body.as_bytes(),
            },
            &SigningScope {
                credentials,
                region,
                service: "bedrock",
                now: clock.signing_time(),
            },
        ),
        (None, Some(token)) => set_header(&mut headers, "Authorization", format!("Bearer {token}")),
        (None, None) => {}
    }

    let mut builder = client.post(url.clone());
    for (name, value) in &headers {
        builder = builder.header(name.as_str(), value.as_str());
    }
    let send = builder.body(request.body.clone()).send();
    let response = match request.signal {
        Some(signal) => tokio::select! {
            _ = signal.cancelled() => return Err(AttemptError::Sdk(request_aborted())),
            response = send => response,
        },
        None => send.await,
    }
    .map_err(|error| AttemptError::Sdk(connection_error(&error, url)))?;

    let status = response.status().as_u16();
    let headers = response_headers(&response);
    // TS `addResponseHeadersMiddleware`: the raw response, before the body.
    if let Some(on_response) = request.on_response {
        on_response(
            ProviderResponse {
                status,
                headers: headers.iter().cloned().collect(),
            },
            request.model,
        )
        .await
        .map_err(|thrown| AttemptError::Fatal(BedrockFailure::Thrown(thrown)))?;
    }
    let signed = credentials.is_some();
    let mut body = BodyReader {
        response,
        signal: request.signal.cloned(),
    };

    if !(200..300).contains(&status) {
        let mut error = deserialize_http_error(status, &headers, &mut body).await;
        if signed && clock.update(&headers) {
            if let Some(metadata) = error.metadata.as_mut() {
                metadata.clock_skew_corrected = true;
            }
        }
        return Err(AttemptError::Sdk(error));
    }
    if signed {
        clock.update(&headers);
    }

    let mut stream = ConverseStream::new(body, metadata_request_id(&headers));
    // `deserializeEventStream` reads the first event inside `send`.
    match stream.read_item().await {
        Ok(first) => {
            stream.first = first;
            Ok(stream)
        }
        Err(BedrockFailure::Sdk(mut error)) => {
            if error.metadata.is_none() {
                error.message.push_str(DESERIALIZATION_HINT);
                error.metadata = Some(SdkMetadata {
                    http_status_code: Some(status),
                    request_id: find_request_id_header(&headers),
                    clock_skew_corrected: false,
                });
            }
            error.response_headers = Some(headers);
            Err(AttemptError::Sdk(error))
        }
        Err(failure @ BedrockFailure::Thrown(_)) => Err(AttemptError::Fatal(failure)),
    }
}

/// `loadRestJsonErrorCode`'s `sanitizeErrorCode`.
fn sanitize_error_code(raw: &str) -> String {
    let mut clean = raw;
    if let Some((head, _)) = clean.split_once(',') {
        clean = head;
    }
    if let Some((head, _)) = clean.split_once(':') {
        clean = head;
    }
    if clean.contains('#') {
        clean = clean.split('#').nth(1).unwrap_or_default();
    }
    clean.to_owned()
}

/// `AwsRestJsonProtocol.handleError` (behind the deserializer middleware)
/// for a non-2xx response.
async fn deserialize_http_error(
    status: u16,
    headers: &[(String, String)],
    body: &mut BodyReader,
) -> SdkError {
    let request_id = metadata_request_id(headers);
    let text = match body.text().await {
        Ok(text) => text,
        Err(error) => return error,
    };
    let data = if text.is_empty() {
        JsonValue::Object(JsonObject::new())
    } else {
        match json_parse(&text) {
            Ok(data) => data,
            Err(error) => {
                // The deserializer middleware decorates the `SyntaxError`.
                let mut error = SdkError::plain("SyntaxError", error.message);
                error.message.push_str(DESERIALIZATION_HINT);
                error.metadata = Some(SdkMetadata {
                    http_status_code: Some(status),
                    request_id: find_request_id_header(headers),
                    clock_skew_corrected: false,
                });
                error.response_headers = Some(headers.to_vec());
                return error;
            }
        }
    };
    let object = data.as_object();
    let header_code = headers
        .iter()
        .find(|(name, _)| name.eq_ignore_ascii_case("x-amzn-errortype"))
        .map(|(_, value)| sanitize_error_code(value));
    let body_code = object.and_then(|object| {
        object
            .iter()
            .find(|(key, _)| key.eq_ignore_ascii_case("code"))
            .map(|(_, value)| sanitize_error_code(&js_to_string(value)))
            .or_else(|| {
                object
                    .get("__type")
                    .map(|value| sanitize_error_code(&js_to_string(value)))
            })
    });
    let name = header_code
        .or(body_code)
        .unwrap_or_else(|| "Unknown".to_owned());
    if data.is_null() {
        let mut error = SdkError::plain(
            "TypeError",
            "Cannot read properties of null (reading 'message')",
        );
        error.message.push_str(DESERIALIZATION_HINT);
        error.metadata = Some(SdkMetadata {
            http_status_code: Some(status),
            request_id: find_request_id_header(headers),
            clock_skew_corrected: false,
        });
        error.response_headers = Some(headers.to_vec());
        return error;
    }
    let message = object
        .and_then(|object| {
            object
                .get("message")
                .filter(|value| !value.is_null())
                .or_else(|| object.get("Message").filter(|value| !value.is_null()))
        })
        .map_or_else(|| "UnknownError".to_owned(), js_to_string);
    SdkError {
        retryable: name == "ModelNotReadyException",
        name,
        message,
        service_exception: true,
        metadata: Some(SdkMetadata {
            http_status_code: Some(status),
            request_id,
            clock_skew_corrected: false,
        }),
        code: None,
        response_headers: Some(headers.to_vec()),
    }
}

/// The UTC calendar date of `ms` (for tests of the date parser).
#[cfg(test)]
fn civil(ms: i64) -> (i64, u32, u32, u32, u32, u32) {
    super::sigv4::civil_from_unix(u64::try_from(ms / 1000).unwrap_or(0))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parses_imf_fixdates() {
        let ms = parse_http_date("Tue, 06 Oct 2026 20:25:28 GMT").expect("parses");
        assert_eq!(civil(ms), (2026, 10, 6, 20, 25, 28));
        assert_eq!(parse_http_date("garbage"), None);
    }

    #[test]
    fn sanitizes_error_codes_like_the_sdk() {
        assert_eq!(
            sanitize_error_code("ValidationException:http://internal.amazon.com/coral/"),
            "ValidationException"
        );
        assert_eq!(
            sanitize_error_code("com.amazon#ThrottlingException"),
            "ThrottlingException"
        );
    }

    #[test]
    fn resolves_partition_dns_suffixes() {
        assert_eq!(partition_dns_suffixes("us-east-1").0, "amazonaws.com");
        assert_eq!(partition_dns_suffixes("cn-north-1").0, "amazonaws.com.cn");
        assert_eq!(partition_dns_suffixes("us-iso-east-1").0, "c2s.ic.gov");
        assert_eq!(partition_dns_suffixes("mars").0, "amazonaws.com");
    }

    #[test]
    fn classifies_retryable_errors() {
        let mut throttled = SdkError::plain("ThrottlingException", "slow");
        throttled.service_exception = true;
        assert_eq!(retry_error_type(&throttled), RetryErrorType::Throttling);
        let refused =
            SdkError::plain("Error", "connect ECONNREFUSED 127.0.0.1:1").with_code("ECONNREFUSED");
        assert_eq!(retry_error_type(&refused), RetryErrorType::Transient);
        assert_eq!(
            retry_error_type(&request_aborted()),
            RetryErrorType::ClientError
        );
    }
}
