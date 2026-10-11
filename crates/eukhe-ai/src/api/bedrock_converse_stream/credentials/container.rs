//! Container credentials: `fromHttp` of `@aws-sdk/credential-provider-http`
//! (ECS / EKS pod identity endpoints, authorization token, 3 retries) and
//! `fromContainerMetadata` of `@smithy/credential-provider-imds`, chained as
//! `remoteProvider` and `credential_source = EcsContainer` chain them.

use std::time::Duration;

use eukhe_types::pi_ai::JsonValue;
use reqwest::Method;
use url::Url;

use super::super::client_config::AwsCredentials;
use super::imds::{imds_credentials, metadata_request, MetadataEndpoint, METADATA_TIMEOUT};
use super::js_compat::{js_error_string, node_fs_error, parse_rfc3339_date_time};
use super::{ProviderFailure, ProviderResult, Resolution};
use crate::utils::diagnostics::ErrorObject;
use crate::utils::json_parse::js_json_parse;

/// `DEFAULT_LINK_LOCAL_HOST`.
const DEFAULT_LINK_LOCAL_HOST: &str = "http://169.254.170.2";

/// `fromHttp`'s request and retry timing: `timeout` 1000 ms, 3 retries.
const HTTP_TIMEOUT: Duration = Duration::from_secs(1);
const HTTP_MAX_RETRIES: u32 = 3;

/// The checkUrl rejection message.
const URL_NOT_ACCEPTED: &str =
    "URL not accepted. It must either be HTTPS or match one of the following:
  - loopback CIDR 127.0.0.0/8 or [::1/128]
  - ECS container host 169.254.170.2
  - EKS container host 169.254.170.23 or [fd00:ec2::23]";

/// `checkUrl(url)`.
fn check_url(url: &Url) -> ProviderResult<()> {
    if url.scheme() == "https" {
        return Ok(());
    }
    let hostname = url.host_str().unwrap_or_default();
    if matches!(
        hostname,
        "169.254.170.2" | "169.254.170.23" | "[fd00:ec2::23]"
    ) {
        return Ok(());
    }
    if hostname.contains('[') {
        if matches!(
            hostname,
            "[::1]" | "[0000:0000:0000:0000:0000:0000:0000:0001]"
        ) {
            return Ok(());
        }
    } else {
        if hostname == "localhost" {
            return Ok(());
        }
        let components: Vec<&str> = hostname.split('.').collect();
        let in_range = |component: Option<&&str>| {
            let parsed = component.map_or(f64::NAN, |component| {
                super::js_compat::js_parse_int(component, Some(10))
            });
            (0.0..=255.0).contains(&parsed)
        };
        if components.first() == Some(&"127")
            && in_range(components.get(1))
            && in_range(components.get(2))
            && in_range(components.get(3))
            && components.len() == 4
        {
            return Ok(());
        }
    }
    Err(ProviderFailure::credentials(URL_NOT_ACCEPTED))
}

/// A constructed `fromHttp` provider.
struct FromHttp {
    url: Url,
    token: Option<String>,
    token_file: Option<String>,
}

/// `fromHttp(options)` construction: the endpoint URL and its checks.
fn from_http(resolution: &Resolution<'_>) -> ProviderResult<FromHttp> {
    let env = resolution.env;
    let relative = env.var("AWS_CONTAINER_CREDENTIALS_RELATIVE_URI");
    let full = env.var("AWS_CONTAINER_CREDENTIALS_FULL_URI");
    let token = env.var("AWS_CONTAINER_AUTHORIZATION_TOKEN");
    let token_file = env.var("AWS_CONTAINER_AUTHORIZATION_TOKEN_FILE");
    // The SDK warns on the console when both forms of a setting are present.
    let host = match (
        relative.filter(|relative| !relative.is_empty()),
        full.filter(|full| !full.is_empty()),
    ) {
        (Some(relative), _) => format!("{DEFAULT_LINK_LOCAL_HOST}{relative}"),
        (None, Some(full)) => full,
        (None, None) => {
            return Err(ProviderFailure::credentials(
                "No HTTP credential provider host provided.\nSet AWS_CONTAINER_CREDENTIALS_FULL_URI or AWS_CONTAINER_CREDENTIALS_RELATIVE_URI.",
            ))
        }
    };
    let url = Url::parse(&host)
        .map_err(|_| ProviderFailure::error(ErrorObject::named("TypeError", "Invalid URL")))?;
    check_url(&url)?;
    Ok(FromHttp {
        url,
        token: token.filter(|token| !token.is_empty()),
        token_file: token_file.filter(|file| !file.is_empty()),
    })
}

/// `validateToken(token)`.
fn validate_token(token: String) -> ProviderResult<String> {
    if token.contains("\r\n") {
        return Err(ProviderFailure::credentials(
            "Authorization token contains invalid \\r\\n sequence.",
        ));
    }
    Ok(token)
}

/// `getCredentials(response)`. Its rejections bypass `fromHttp`'s
/// try/catch (the promise is returned, not awaited), so they keep their own
/// `tryNextLink`: JSON and date errors stop the chain.
fn http_credentials(status: u16, body: &str) -> ProviderResult<AwsCredentials> {
    if status != 200 {
        return Err(ProviderFailure::credentials(format!(
            "Server responded with status: {status}"
        )));
    }
    let parsed = js_json_parse(body).map_err(|error| {
        ProviderFailure::error(ErrorObject::named("SyntaxError", error.message))
    })?;
    let string = |key: &str| match parsed.get(key) {
        Some(JsonValue::String(value)) => Some(value.clone()),
        _ => None,
    };
    let (Some(access_key_id), Some(secret_access_key), Some(token), Some(expiration)) = (
        string("AccessKeyId"),
        string("SecretAccessKey"),
        string("Token"),
        string("Expiration"),
    ) else {
        return Err(ProviderFailure::credentials(
            "HTTP credential provider response not of the required format, an object matching: { AccessKeyId: string, SecretAccessKey: string, Token: string, Expiration: string(rfc3339) }",
        ));
    };
    parse_rfc3339_date_time(&expiration).map_err(ProviderFailure::error)?;
    Ok(AwsCredentials {
        access_key_id,
        secret_access_key,
        session_token: Some(token).filter(|token| !token.is_empty()),
    })
}

/// One `fromHttp` attempt.
async fn http_attempt(
    resolution: &Resolution<'_>,
    provider: &FromHttp,
) -> ProviderResult<AwsCredentials> {
    let authorization = if let Some(file) = &provider.token_file {
        let bytes = tokio::fs::read(file)
            .await
            .map_err(|error| ProviderFailure::thrown(node_fs_error(&error, "open", file)))?;
        Some(validate_token(
            String::from_utf8_lossy(&bytes).into_owned(),
        )?)
    } else if let Some(token) = &provider.token {
        Some(validate_token(token.clone())?)
    } else {
        None
    };
    let exchange = async {
        let client = reqwest::Client::builder()
            .no_proxy()
            .http1_only()
            .connect_timeout(HTTP_TIMEOUT)
            .read_timeout(HTTP_TIMEOUT)
            .build()?;
        let mut url = provider.url.clone();
        url.set_fragment(None);
        let mut request = client.get(url);
        if let Some(authorization) = &authorization {
            request = request.header("Authorization", authorization);
        }
        let response = request.send().await?;
        let status = response.status().as_u16();
        let body = response.bytes().await?;
        Ok::<_, reqwest::Error>((status, String::from_utf8_lossy(&body).into_owned()))
    };
    match resolution.abortable(exchange).await? {
        Ok((status, body)) => http_credentials(status, &body),
        // `new CredentialsProviderError(String(e))` of a request failure.
        Err(error) => Err(ProviderFailure::credentials(js_error_string(
            &ErrorObject::new(error.to_string()).thrown(),
        ))),
    }
}

/// `retryWrapper(provider, maxRetries, timeout)` around [`http_attempt`].
async fn run_from_http(
    resolution: &Resolution<'_>,
    provider: &FromHttp,
) -> ProviderResult<AwsCredentials> {
    for _ in 0..HTTP_MAX_RETRIES {
        match http_attempt(resolution, provider).await {
            Ok(credentials) => return Ok(credentials),
            Err(failure)
                if resolution
                    .signal
                    .is_some_and(eukhe_chord::context::AbortSignal::aborted) =>
            {
                return Err(failure)
            }
            Err(_) => resolution.sleep(1000.0).await?,
        }
    }
    http_attempt(resolution, provider).await
}

/// `getCmdsUri()` of `fromContainerMetadata`.
fn container_metadata_uri(
    resolution: &Resolution<'_>,
) -> ProviderResult<(MetadataEndpoint, String)> {
    let env = resolution.env;
    if let Some(relative) = env.truthy_var("AWS_CONTAINER_CREDENTIALS_RELATIVE_URI") {
        return Ok((
            MetadataEndpoint {
                protocol: "http:".to_owned(),
                hostname: "169.254.170.2".to_owned(),
                port: None,
            },
            relative,
        ));
    }
    if let Some(full) = env.truthy_var("AWS_CONTAINER_CREDENTIALS_FULL_URI") {
        let parsed = Url::parse(&full).map_err(|_| {
            ProviderFailure::credentials_final(format!(
                "{full} is not a valid container metadata service URL"
            ))
        })?;
        let hostname = parsed.host_str().unwrap_or_default();
        if !matches!(hostname, "localhost" | "127.0.0.1") {
            return Err(ProviderFailure::credentials_final(format!(
                "{hostname} is not a valid container metadata service hostname"
            )));
        }
        let protocol = format!("{}:", parsed.scheme());
        if !matches!(protocol.as_str(), "http:" | "https:") {
            return Err(ProviderFailure::credentials_final(format!(
                "{protocol} is not a valid container metadata service protocol"
            )));
        }
        let path = match parsed.query() {
            Some(query) => format!("{}?{query}", parsed.path()),
            None => parsed.path().to_owned(),
        };
        return Ok((MetadataEndpoint::from_url(&parsed), path));
    }
    Err(ProviderFailure::credentials_final(
        "The container metadata credential provider cannot be used unless the AWS_CONTAINER_CREDENTIALS_RELATIVE_URI or AWS_CONTAINER_CREDENTIALS_FULL_URI environment variable is set",
    ))
}

/// `fromContainerMetadata(init)()` (no retries).
async fn from_container_metadata(resolution: &Resolution<'_>) -> ProviderResult<AwsCredentials> {
    let (endpoint, path) = container_metadata_uri(resolution)?;
    let headers: Vec<(&str, String)> = resolution
        .env
        .truthy_var("AWS_CONTAINER_AUTHORIZATION_TOKEN")
        .map(|token| vec![("Authorization", token)])
        .unwrap_or_default();
    let body = resolution
        .abortable(metadata_request(
            &endpoint,
            Method::GET,
            &path,
            &headers,
            METADATA_TIMEOUT,
        ))
        .await?
        .map_err(super::imds::MetadataError::into_failure)?;
    imds_credentials(&body)
}

/// `chain(fromHttp(init), fromContainerMetadata(init))()`.
///
/// # Errors
///
/// The construction errors of `fromHttp` (an invalid or rejected URL), else
/// the chain's last error, or the signal's reason.
pub(crate) async fn from_http_then_container_metadata(
    resolution: &Resolution<'_>,
) -> ProviderResult<AwsCredentials> {
    let provider = from_http(resolution)?;
    match run_from_http(resolution, &provider).await {
        Ok(credentials) => Ok(credentials),
        Err(failure) if failure.try_next_link => from_container_metadata(resolution).await,
        Err(failure) => Err(failure),
    }
}
