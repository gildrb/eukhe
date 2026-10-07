//! EC2 instance metadata: `fromInstanceMetadata` of
//! `@smithy/credential-provider-imds` (`IMDSv2` token, v1 fallback) and the
//! instance-metadata region lookup of `NODE_REGION_CONFIG_OPTIONS.default`,
//! plus the `httpRequest` helper the container metadata provider shares.

use std::sync::PoisonError;
use std::time::Duration;

use eukhe_types::pi_ai::JsonValue;
use reqwest::Method;
use url::Url;

use super::super::client_config::AwsCredentials;
use super::js_compat::now_ms;
use super::shared_ini::{load_config, PreferredFile};
use super::{CredentialEnv, ProviderFailure, ProviderResult, Resolution};
use crate::utils::diagnostics::ErrorObject;
use crate::utils::js::js_trim;
use crate::utils::json_parse::js_json_parse;

/// `DEFAULT_TIMEOUT` (and the region lookup's `TIMEOUT_MS`).
pub(crate) const METADATA_TIMEOUT: Duration = Duration::from_secs(1);

const IMDS_TOKEN_PATH: &str = "/latest/api/token";
const IMDS_CREDENTIALS_PATH: &str = "/latest/meta-data/iam/security-credentials/";
const IMDS_REGION_PATH: &str = "/latest/meta-data/placement/region";

/// A failed metadata `httpRequest`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum MetadataError {
    /// `Unable to connect to instance metadata service`.
    Connect,
    /// `TimeoutError from instance metadata service`.
    Timeout,
    /// `Error response received from instance metadata service` with `statusCode`.
    Status(u16),
    /// Node `http.request` rejects a non-`http:` protocol.
    Protocol(String),
    /// The HTTP client could not be built.
    Client(String),
}

impl MetadataError {
    /// The rejection as the SDK throws it.
    pub(crate) fn into_failure(self) -> ProviderFailure {
        match self {
            Self::Connect => {
                ProviderFailure::provider("Unable to connect to instance metadata service")
            }
            Self::Timeout => {
                ProviderFailure::provider("TimeoutError from instance metadata service")
            }
            Self::Status(_) => {
                ProviderFailure::provider("Error response received from instance metadata service")
            }
            Self::Protocol(protocol) => ProviderFailure::error(ErrorObject::named(
                "TypeError",
                format!("Protocol \"{protocol}\" not supported. Expected \"http:\""),
            )),
            Self::Client(message) => ProviderFailure::error(ErrorObject::new(message)),
        }
    }

    fn status(&self) -> Option<u16> {
        match self {
            Self::Status(status) => Some(*status),
            Self::Connect | Self::Timeout | Self::Protocol(_) | Self::Client(_) => None,
        }
    }
}

/// `parseUrl(endpoint)` fields a metadata request uses.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct MetadataEndpoint {
    pub(crate) protocol: String,
    /// Without IPv6 brackets.
    pub(crate) hostname: String,
    pub(crate) port: Option<u16>,
}

impl MetadataEndpoint {
    /// The endpoint of a parsed URL.
    pub(crate) fn from_url(url: &Url) -> Self {
        let host = url.host_str().unwrap_or_default();
        let hostname = host
            .strip_prefix('[')
            .and_then(|host| host.strip_suffix(']'))
            .unwrap_or(host)
            .to_owned();
        Self {
            protocol: format!("{}:", url.scheme()),
            hostname,
            port: url.port(),
        }
    }

    fn origin(&self) -> String {
        let host = if self.hostname.contains(':') {
            format!("[{}]", self.hostname)
        } else {
            self.hostname.clone()
        };
        match self.port {
            Some(port) => format!("http://{host}:{port}"),
            None => format!("http://{host}"),
        }
    }
}

/// `httpRequest(options)`: one plain-HTTP request with a socket timeout; the
/// body of a 2xx response.
///
/// # Errors
///
/// [`MetadataError`] for connection failures, timeouts, non-2xx statuses, and
/// non-`http:` endpoints.
pub(crate) async fn metadata_request(
    endpoint: &MetadataEndpoint,
    method: Method,
    path: &str,
    headers: &[(&str, String)],
    timeout: Duration,
) -> Result<String, MetadataError> {
    if endpoint.protocol != "http:" {
        return Err(MetadataError::Protocol(endpoint.protocol.clone()));
    }
    let client = reqwest::Client::builder()
        .no_proxy()
        .http1_only()
        .connect_timeout(timeout)
        .read_timeout(timeout)
        .build()
        .map_err(|error| MetadataError::Client(error.to_string()))?;
    let url = format!("{}{path}", endpoint.origin());
    let mut request = client.request(method, url);
    for (name, value) in headers {
        request = request.header(*name, value);
    }
    let response = request.send().await.map_err(|error| {
        if error.is_timeout() {
            MetadataError::Timeout
        } else {
            MetadataError::Connect
        }
    })?;
    let status = response.status().as_u16();
    if !(200..300).contains(&status) {
        return Err(MetadataError::Status(status));
    }
    let body = response.bytes().await.map_err(|error| {
        if error.is_timeout() {
            MetadataError::Timeout
        } else {
            MetadataError::Connect
        }
    })?;
    Ok(String::from_utf8_lossy(&body).into_owned())
}

/// `isImdsCredentials` + `fromImdsCredentials` of a metadata response body.
///
/// # Errors
///
/// The `SyntaxError` of a malformed body (stops the chain), or `Invalid
/// response received from instance metadata service.` (continues it).
pub(crate) fn imds_credentials(body: &str) -> ProviderResult<AwsCredentials> {
    let parsed = js_json_parse(body).map_err(|error| {
        ProviderFailure::error(ErrorObject::named("SyntaxError", error.message))
    })?;
    let string = |key: &str| match parsed.get(key) {
        Some(JsonValue::String(value)) => Some(value.clone()),
        _ => None,
    };
    match (
        string("AccessKeyId"),
        string("SecretAccessKey"),
        string("Token"),
        string("Expiration"),
    ) {
        (Some(access_key_id), Some(secret_access_key), Some(token), Some(_)) => {
            Ok(AwsCredentials {
                access_key_id,
                secret_access_key,
                session_token: Some(token).filter(|token| !token.is_empty()),
            })
        }
        _ => Err(ProviderFailure::credentials(
            "Invalid response received from instance metadata service.",
        )),
    }
}

/// `getInstanceMetadataEndpoint()`: `AWS_EC2_METADATA_SERVICE_ENDPOINT` /
/// `ec2_metadata_service_endpoint`, else the endpoint mode's address.
async fn instance_metadata_endpoint(env: &CredentialEnv<'_>) -> ProviderResult<MetadataEndpoint> {
    let configured = load_config(
        env,
        None,
        PreferredFile::Config,
        |env| env.var("AWS_EC2_METADATA_SERVICE_ENDPOINT"),
        |profile, _| {
            profile
                .get("ec2_metadata_service_endpoint")
                .map(str::to_owned)
        },
    )
    .await
    .filter(|endpoint| !endpoint.is_empty());
    let endpoint = if let Some(endpoint) = configured {
        endpoint
    } else {
        let mode = load_config(
            env,
            None,
            PreferredFile::Config,
            |env| env.var("AWS_EC2_METADATA_SERVICE_ENDPOINT_MODE"),
            |profile, _| {
                profile
                    .get("ec2_metadata_service_endpoint_mode")
                    .map(str::to_owned)
            },
        )
        .await
        .unwrap_or_else(|| "IPv4".to_owned());
        match mode.as_str() {
            "IPv4" => "http://169.254.169.254".to_owned(),
            "IPv6" => "http://[fd00:ec2::254]".to_owned(),
            other => {
                return Err(ProviderFailure::error(ErrorObject::new(format!(
                    "Unsupported endpoint mode: {other}. Select from IPv4,IPv6"
                ))))
            }
        }
    };
    let url = Url::parse(&endpoint)
        .map_err(|_| ProviderFailure::error(ErrorObject::named("TypeError", "Invalid URL")))?;
    Ok(MetadataEndpoint::from_url(&url))
}

/// The `IMDSv1` fallback guard: `AWS_EC2_METADATA_V1_DISABLED` /
/// `ec2_metadata_v1_disabled` block it.
async fn check_v1_fallback(resolution: &Resolution<'_>) -> ProviderResult<()> {
    let env = resolution.env;
    let env_value = env.var("AWS_EC2_METADATA_V1_DISABLED");
    let blocked_by_env = env_value
        .as_deref()
        .is_some_and(|value| !value.is_empty() && value != "false");
    let mut blocked_by_profile = false;
    let blocked = if env_value.is_some() {
        blocked_by_env
    } else {
        let profile_value = load_config(
            env,
            resolution.caller.profile,
            PreferredFile::Config,
            |_| None,
            |profile, _| Some(profile.get("ec2_metadata_v1_disabled").map(str::to_owned)),
        )
        .await
        .flatten();
        blocked_by_profile = profile_value
            .as_deref()
            .is_some_and(|value| value != "false");
        blocked_by_profile
    };
    if !blocked {
        return Ok(());
    }
    let mut causes = Vec::new();
    if blocked_by_profile {
        causes.push("config file profile (ec2_metadata_v1_disabled)");
    }
    if blocked_by_env {
        causes.push("process environment variable (AWS_EC2_METADATA_V1_DISABLED)");
    }
    Err(ProviderFailure {
        error: ErrorObject::named(
            "InstanceMetadataV1FallbackError",
            format!(
                "AWS EC2 Metadata v1 fallback has been blocked by AWS SDK configuration in the following: [{}].",
                causes.join(", ")
            ),
        )
        .thrown(),
        try_next_link: true,
    })
}

/// `getCredentials(maxRetries = 0, options)`: the role name, then its credentials.
async fn instance_credentials(
    resolution: &Resolution<'_>,
    endpoint: &MetadataEndpoint,
    token: Option<&str>,
) -> ProviderResult<AwsCredentials> {
    if token.is_none() {
        check_v1_fallback(resolution).await?;
    }
    let headers: Vec<(&str, String)> = token
        .map(|token| vec![("x-aws-ec2-metadata-token", token.to_owned())])
        .unwrap_or_default();
    let profile = resolution
        .abortable(metadata_request(
            endpoint,
            Method::GET,
            IMDS_CREDENTIALS_PATH,
            &headers,
            METADATA_TIMEOUT,
        ))
        .await?
        .map_err(MetadataError::into_failure)?;
    let profile = js_trim(&profile);
    let body = resolution
        .abortable(metadata_request(
            endpoint,
            Method::GET,
            &format!("{IMDS_CREDENTIALS_PATH}{profile}"),
            &headers,
            METADATA_TIMEOUT,
        ))
        .await?
        .map_err(MetadataError::into_failure)?;
    imds_credentials(&body)
}

/// `fromInstanceMetadata(init)()`.
///
/// # Errors
///
/// `ProviderError`s for unreachable or failing metadata (chain continues),
/// configuration errors and malformed JSON (chain stops), or the signal's
/// reason.
pub(crate) async fn from_instance_metadata(
    resolution: &Resolution<'_>,
) -> ProviderResult<AwsCredentials> {
    let endpoint = instance_metadata_endpoint(resolution.env).await?;
    let token = resolution
        .abortable(metadata_request(
            &endpoint,
            Method::PUT,
            IMDS_TOKEN_PATH,
            &[("x-aws-ec2-metadata-token-ttl-seconds", "21600".to_owned())],
            METADATA_TIMEOUT,
        ))
        .await?;
    match token {
        Ok(token) => instance_credentials(resolution, &endpoint, Some(&token)).await,
        Err(error) if error.status() == Some(400) => Err(ProviderFailure::provider(
            "EC2 Metadata token request returned error",
        )),
        // Every other token failure falls back to IMDSv1 (which repeats a
        // protocol or client error after the v1 guard).
        Err(_) => instance_credentials(resolution, &endpoint, None).await,
    }
}

/// `getInstanceMetadataRegion()`: the IMDS placement region, with the SDK's
/// 60-second negative cache. `None` when disabled or unavailable.
pub(crate) async fn instance_metadata_region(env: &CredentialEnv<'_>) -> Option<String> {
    if env.truthy_var("AWS_EC2_METADATA_DISABLED").is_some() {
        return None;
    }
    let negative_until = *env
        .state
        .imds_region_negative_cache_until
        .lock()
        .unwrap_or_else(PoisonError::into_inner);
    if now_ms() < negative_until {
        return None;
    }
    let region = lookup_region(env).await.filter(|region| !region.is_empty());
    if region.is_none() {
        *env.state
            .imds_region_negative_cache_until
            .lock()
            .unwrap_or_else(PoisonError::into_inner) = now_ms() + 60_000.0;
    }
    region
}

/// The token + region requests of `getInstanceMetadataRegion`.
async fn lookup_region(env: &CredentialEnv<'_>) -> Option<String> {
    let endpoint = match env.truthy_var("AWS_EC2_METADATA_SERVICE_ENDPOINT") {
        Some(configured) => {
            let url = Url::parse(&configured).ok()?;
            let mut endpoint = MetadataEndpoint::from_url(&url);
            // `imdsRequest` always uses `node:http`.
            "http:".clone_into(&mut endpoint.protocol);
            endpoint
        }
        None => MetadataEndpoint {
            protocol: "http:".to_owned(),
            hostname: if env.var("AWS_EC2_METADATA_SERVICE_ENDPOINT_MODE").as_deref()
                == Some("IPv6")
            {
                "fd00:ec2::254".to_owned()
            } else {
                "169.254.169.254".to_owned()
            },
            port: None,
        },
    };
    let token = tokio::time::timeout(
        METADATA_TIMEOUT,
        metadata_request(
            &endpoint,
            Method::PUT,
            IMDS_TOKEN_PATH,
            &[("x-aws-ec2-metadata-token-ttl-seconds", "21600".to_owned())],
            METADATA_TIMEOUT,
        ),
    )
    .await
    .ok()?
    .ok()?;
    let region = tokio::time::timeout(
        METADATA_TIMEOUT,
        metadata_request(
            &endpoint,
            Method::GET,
            IMDS_REGION_PATH,
            &[("x-aws-ec2-metadata-token", token)],
            METADATA_TIMEOUT,
        ),
    )
    .await
    .ok()?
    .ok()?;
    Some(js_trim(&region).to_owned())
}
