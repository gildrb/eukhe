//! The parts of the SDK's nested STS / SSO / SSO-OIDC / Signin clients the
//! credential providers depend on: region checks (`resolveRegionConfig`),
//! FIPS / dual-stack flags, configured endpoint URLs (`AWS_ENDPOINT_URL_*`,
//! `endpoint_url`, `[services]`), the endpoint rule sets, the standard retry
//! strategy around each HTTP call, and the `restJson1` error shape.

use std::sync::LazyLock;
use std::time::SystemTime;

use eukhe_types::pi_ai::{JsonObject, JsonValue};
use regex::Regex;
use reqwest::header::HeaderMap;
use reqwest::Method;
use url::Url;
use uuid::Uuid;

use super::super::client_config::{AwsCredentials, BedrockRequestHandler};
use super::super::sigv4::{sign_request, SignableRequest, SigningScope};
use super::js_compat::{js_date_parse, js_parse_int, now_ms};
use super::shared_ini::{boolean_value, load_config, PreferredFile};
use super::{CredentialEnv, ProviderFailure, ProviderResult, Resolution};
use crate::utils::diagnostics::{ErrorObject, SdkValue, Thrown};
use crate::utils::js::{js_to_string, number_to_js_string};
use crate::utils::json_parse::js_json_parse;

/// The nested clients the credential providers create.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum AwsService {
    Sts,
    Sso,
    SsoOidc,
    Signin,
}

impl AwsService {
    /// `serviceId`.
    fn service_id(self) -> &'static str {
        match self {
            Self::Sts => "STS",
            Self::Sso => "SSO",
            Self::SsoOidc => "SSO OIDC",
            Self::Signin => "Signin",
        }
    }

    /// The endpoint host prefix (`sts`, `portal.sso`, `oidc`, `signin`).
    fn host_prefix(self) -> &'static str {
        match self {
            Self::Sts => "sts",
            Self::Sso => "portal.sso",
            Self::SsoOidc => "oidc",
            Self::Signin => "signin",
        }
    }

    /// The `SigV4` signing name.
    fn signing_name(self) -> &'static str {
        match self {
            Self::Sts => "sts",
            Self::Sso => "awsssoportal",
            Self::SsoOidc => "sso-oauth",
            Self::Signin => "signin",
        }
    }
}

/// One AWS partition of the SDK's `partitions.json`.
struct Partition {
    name: &'static str,
    regions: &'static [&'static str],
    region_regex: &'static str,
    dns_suffix: &'static str,
    dual_stack_dns_suffix: &'static str,
}

const PARTITIONS: [Partition; 8] = [
    Partition {
        name: "aws",
        regions: &[
            "af-south-1",
            "ap-east-1",
            "ap-east-2",
            "ap-northeast-1",
            "ap-northeast-2",
            "ap-northeast-3",
            "ap-south-1",
            "ap-south-2",
            "ap-southeast-1",
            "ap-southeast-2",
            "ap-southeast-3",
            "ap-southeast-4",
            "ap-southeast-5",
            "ap-southeast-6",
            "ap-southeast-7",
            "aws-global",
            "ca-central-1",
            "ca-west-1",
            "eu-central-1",
            "eu-central-2",
            "eu-north-1",
            "eu-south-1",
            "eu-south-2",
            "eu-west-1",
            "eu-west-2",
            "eu-west-3",
            "il-central-1",
            "me-central-1",
            "me-south-1",
            "mx-central-1",
            "sa-east-1",
            "us-east-1",
            "us-east-2",
            "us-west-1",
            "us-west-2",
        ],
        region_regex: r"^(us|eu|ap|sa|ca|me|af|il|mx)-[A-Za-z0-9_]+-[0-9]+$",
        dns_suffix: "amazonaws.com",
        dual_stack_dns_suffix: "api.aws",
    },
    Partition {
        name: "aws-cn",
        regions: &["aws-cn-global", "cn-north-1", "cn-northwest-1"],
        region_regex: r"^cn-[A-Za-z0-9_]+-[0-9]+$",
        dns_suffix: "amazonaws.com.cn",
        dual_stack_dns_suffix: "api.amazonwebservices.com.cn",
    },
    Partition {
        name: "aws-eusc",
        regions: &["eusc-de-east-1"],
        region_regex: r"^eusc-(de)-[A-Za-z0-9_]+-[0-9]+$",
        dns_suffix: "amazonaws.eu",
        dual_stack_dns_suffix: "api.amazonwebservices.eu",
    },
    Partition {
        name: "aws-iso",
        regions: &["aws-iso-global", "us-iso-east-1", "us-iso-west-1"],
        region_regex: r"^us-iso-[A-Za-z0-9_]+-[0-9]+$",
        dns_suffix: "c2s.ic.gov",
        dual_stack_dns_suffix: "api.aws.ic.gov",
    },
    Partition {
        name: "aws-iso-b",
        regions: &["aws-iso-b-global", "us-isob-east-1", "us-isob-west-1"],
        region_regex: r"^us-isob-[A-Za-z0-9_]+-[0-9]+$",
        dns_suffix: "sc2s.sgov.gov",
        dual_stack_dns_suffix: "api.aws.scloud",
    },
    Partition {
        name: "aws-iso-e",
        regions: &["aws-iso-e-global", "eu-isoe-west-1"],
        region_regex: r"^eu-isoe-[A-Za-z0-9_]+-[0-9]+$",
        dns_suffix: "cloud.adc-e.uk",
        dual_stack_dns_suffix: "api.cloud-aws.adc-e.uk",
    },
    Partition {
        name: "aws-iso-f",
        regions: &["aws-iso-f-global", "us-isof-east-1", "us-isof-south-1"],
        region_regex: r"^us-isof-[A-Za-z0-9_]+-[0-9]+$",
        dns_suffix: "csp.hci.ic.gov",
        dual_stack_dns_suffix: "api.aws.hci.ic.gov",
    },
    Partition {
        name: "aws-us-gov",
        regions: &["aws-us-gov-global", "us-gov-east-1", "us-gov-west-1"],
        region_regex: r"^us-gov-[A-Za-z0-9_]+-[0-9]+$",
        dns_suffix: "amazonaws.com",
        dual_stack_dns_suffix: "api.aws",
    },
];

static PARTITION_REGEXES: LazyLock<Vec<Regex>> = LazyLock::new(|| {
    PARTITIONS
        .iter()
        .map(|partition| Regex::new(partition.region_regex).expect("static partition regex"))
        .collect()
});

/// `partition(region)` of `@aws-sdk/core/client`: an explicit region match,
/// then the region regexes, else `aws`.
fn partition(region: &str) -> &'static Partition {
    if let Some(found) = PARTITIONS
        .iter()
        .find(|partition| partition.regions.contains(&region))
    {
        return found;
    }
    PARTITIONS
        .iter()
        .zip(PARTITION_REGEXES.iter())
        .find(|(_, regex)| regex.is_match(region))
        .map_or(&PARTITIONS[0], |(partition, _)| partition)
}

/// `isFipsRegion`.
fn is_fips_region(region: &str) -> bool {
    region.starts_with("fips-") || region.ends_with("-fips")
}

static FIPS_REGION_PARTS: LazyLock<Regex> =
    LazyLock::new(|| Regex::new("fips-(dkr-|prod-)?|-fips").expect("static fips regex"));

/// `getRealRegion`.
fn get_real_region(region: &str) -> String {
    if !is_fips_region(region) {
        return region.to_owned();
    }
    if matches!(region, "fips-aws-global" | "aws-fips") {
        return "us-east-1".to_owned();
    }
    FIPS_REGION_PARTS.replace(region, "").into_owned()
}

/// `isValidHostLabel(value)`: `/^(?!.*-$)(?!-)[a-zA-Z0-9-]{1,63}$/`.
fn is_valid_host_label(value: &str) -> bool {
    (1..=63).contains(&value.len())
        && !value.starts_with('-')
        && !value.ends_with('-')
        && value
            .bytes()
            .all(|byte| byte.is_ascii_alphanumeric() || byte == b'-')
}

/// The client region after `resolveRegionConfig`.
///
/// # Errors
///
/// `Region not accepted: …` for a region that is not a host label.
fn resolve_client_region(region: &str) -> Result<String, ErrorObject> {
    let real_region = get_real_region(region);
    // "*" is accepted with a console warning in the SDK.
    if real_region != "*" && !is_valid_host_label(&real_region) {
        return Err(ErrorObject::new(format!(
            "Region not accepted: region=\"{real_region}\" is not a valid hostname component."
        )));
    }
    Ok(real_region)
}

/// `getEndpointFromConfig(serviceId)`: `AWS_ENDPOINT_URL_<SERVICE>`,
/// `AWS_ENDPOINT_URL`, then the profile's `[services]` section or
/// `endpoint_url` (default profile name), unless configured endpoints are
/// ignored.
async fn configured_endpoint(env: &CredentialEnv<'_>, service: AwsService) -> Option<String> {
    let ignore = load_config(
        env,
        None,
        PreferredFile::Config,
        |env| boolean_value(env.var("AWS_IGNORE_CONFIGURED_ENDPOINT_URLS").as_deref()),
        |profile, _| boolean_value(profile.get("ignore_configured_endpoint_urls")),
    )
    .await
    .unwrap_or(false);
    if ignore {
        return None;
    }
    let service_id = service.service_id();
    load_config(
        env,
        None,
        PreferredFile::Config,
        |env| {
            let suffix = service_id
                .split(' ')
                .map(str::to_uppercase)
                .collect::<Vec<_>>()
                .join("_");
            env.truthy_var(&format!("AWS_ENDPOINT_URL_{suffix}"))
                .or_else(|| env.truthy_var("AWS_ENDPOINT_URL"))
        },
        |profile, config_file| {
            if let Some(services) = profile.get("services") {
                // A missing section throws, which the loader treats as unset.
                let section = config_file.get(&format!("services.{services}"))?;
                let prefix = service_id
                    .split(' ')
                    .map(str::to_lowercase)
                    .collect::<Vec<_>>()
                    .join("_");
                if let Some(url) = section.get(&format!("{prefix}.endpoint_url")) {
                    return Some(url.to_owned());
                }
            }
            profile.get("endpoint_url").map(str::to_owned)
        },
    )
    .await
}

/// A `true`/`false` client flag (`use_fips_endpoint`, `use_dualstack_endpoint`).
async fn load_flag(
    env: &CredentialEnv<'_>,
    profile: Option<&str>,
    env_name: &str,
    config_key: &str,
) -> bool {
    load_config(
        env,
        profile,
        PreferredFile::Config,
        |env| boolean_value(env.var(env_name).as_deref()),
        |section, _| boolean_value(section.get(config_key)),
    )
    .await
    .unwrap_or(false)
}

/// `NODE_MAX_ATTEMPT_CONFIG_OPTIONS`: `AWS_MAX_ATTEMPTS`, `max_attempts`, 3.
async fn load_max_attempts(env: &CredentialEnv<'_>, profile: Option<&str>) -> f64 {
    let parse = |value: Option<String>| {
        let value = value.filter(|value| !value.is_empty())?;
        let parsed = js_parse_int(&value, None);
        // A non-number throws, which the loader treats as unset.
        (!parsed.is_nan()).then_some(parsed)
    };
    load_config(
        env,
        profile,
        PreferredFile::Config,
        |env| parse(env.var("AWS_MAX_ATTEMPTS")),
        |section, _| parse(section.get("max_attempts").map(str::to_owned)),
    )
    .await
    .unwrap_or(3.0)
}

/// A nested client ready to send: endpoint, signing region, retry budget.
pub(crate) struct NestedClient {
    pub(crate) endpoint: Url,
    pub(crate) signing_region: String,
    signing_name: &'static str,
    http: reqwest::Client,
    max_attempts: f64,
}

/// What the nested client is built from.
pub(crate) struct NestedClientConfig<'a> {
    pub(crate) service: AwsService,
    /// The `region` passed to the client constructor.
    pub(crate) region: &'a str,
    /// The client's `profile` (`undefined` falls back to `AWS_PROFILE`).
    pub(crate) profile: Option<&'a str>,
    /// The proxy of a reused `NodeHttpHandler` with proxy agents.
    pub(crate) proxy: Option<&'a Url>,
}

/// The rule-set endpoint of `service` in `region` (and the signing region
/// when the rule set overrides it).
fn rule_set_endpoint(
    service: AwsService,
    region: &str,
    use_fips: bool,
    use_dual_stack: bool,
) -> (String, Option<&'static str>) {
    let partition = partition(region);
    let prefix = service.host_prefix();
    if service == AwsService::Sts && region == "aws-global" && !use_fips && !use_dual_stack {
        return ("https://sts.amazonaws.com".to_owned(), Some("us-east-1"));
    }
    let url = match (use_fips, use_dual_stack) {
        (true, true) => format!(
            "https://{prefix}-fips.{region}.{}",
            partition.dual_stack_dns_suffix
        ),
        (true, false) if service == AwsService::Signin && region == "us-gov-west-1" => {
            "https://signin-fips.amazonaws-us-gov.com".to_owned()
        }
        (true, false) if service == AwsService::Signin && partition.name == "aws-us-gov" => {
            format!("https://{region}.signin-fips.amazonaws-us-gov.com")
        }
        (true, false) if service != AwsService::Signin && partition.name == "aws-us-gov" => {
            format!("https://{prefix}.{region}.amazonaws.com")
        }
        (true, false) => format!("https://{prefix}-fips.{region}.{}", partition.dns_suffix),
        (false, true) => format!(
            "https://{prefix}.{region}.{}",
            partition.dual_stack_dns_suffix
        ),
        (false, false) if service == AwsService::Signin => signin_endpoint(region, partition),
        (false, false) => format!("https://{prefix}.{region}.{}", partition.dns_suffix),
    };
    (url, None)
}

/// The Signin data-plane endpoint (`IsControlPlane = false`) per partition.
fn signin_endpoint(region: &str, partition: &Partition) -> String {
    let domain = match partition.name {
        "aws" => "signin.aws.amazon.com",
        "aws-cn" => "signin.amazonaws.cn",
        "aws-us-gov" => "signin.amazonaws-us-gov.com",
        "aws-iso" => "signin.c2shome.ic.gov",
        "aws-iso-b" => "signin.sc2shome.sgov.gov",
        "aws-iso-f" => "signin.csphome.hci.ic.gov",
        "aws-iso-e" => "signin.csphome.adc-e.uk",
        "aws-eusc" => "signin.amazonaws-eusc.eu",
        _ => return format!("https://{region}.signin.{}", partition.dns_suffix),
    };
    format!("https://{region}.{domain}")
}

fn invalid_url() -> ProviderFailure {
    ProviderFailure::error(ErrorObject::named("TypeError", "Invalid URL"))
}

/// Build the nested client the SDK constructs for `config`.
///
/// # Errors
///
/// Region, endpoint-configuration, and HTTP client errors (none of them let
/// the chain continue).
pub(crate) async fn nested_client(
    resolution: &Resolution<'_>,
    config: &NestedClientConfig<'_>,
) -> ProviderResult<NestedClient> {
    let env = resolution.env;
    let real_region = resolve_client_region(config.region).map_err(ProviderFailure::error)?;
    let use_fips = is_fips_region(config.region)
        || load_flag(
            env,
            config.profile,
            "AWS_USE_FIPS_ENDPOINT",
            "use_fips_endpoint",
        )
        .await;
    let use_dual_stack = load_flag(
        env,
        config.profile,
        "AWS_USE_DUALSTACK_ENDPOINT",
        "use_dualstack_endpoint",
    )
    .await;
    let (endpoint, signing_region) = match configured_endpoint(env, config.service).await {
        Some(custom) => {
            if use_fips {
                return Err(ProviderFailure::error(ErrorObject::new(
                    "Invalid Configuration: FIPS and custom endpoint are not supported",
                )));
            }
            if use_dual_stack {
                return Err(ProviderFailure::error(ErrorObject::new(
                    "Invalid Configuration: Dualstack and custom endpoint are not supported",
                )));
            }
            (custom, None)
        }
        None => rule_set_endpoint(config.service, &real_region, use_fips, use_dual_stack),
    };
    let endpoint = Url::parse(&endpoint).map_err(|_| invalid_url())?;
    let mut builder = reqwest::Client::builder().no_proxy().http1_only();
    if let Some(proxy) = config.proxy {
        let proxy = reqwest::Proxy::all(proxy.as_str())
            .map_err(|error| ProviderFailure::error(ErrorObject::new(error.to_string())))?;
        builder = builder.proxy(proxy);
    }
    let http = builder
        .build()
        .map_err(|error| ProviderFailure::error(ErrorObject::new(error.to_string())))?;
    Ok(NestedClient {
        endpoint,
        signing_region: signing_region.map_or(real_region, str::to_owned),
        signing_name: config.service.signing_name(),
        http,
        max_attempts: load_max_attempts(env, config.profile).await,
    })
}

/// How the retry strategy classifies a failed attempt.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum RetryErrorType {
    Throttling,
    Transient,
    ServerError,
    ClientError,
}

/// One failed attempt: the error to throw and its retry classification.
#[derive(Debug, Clone)]
pub(crate) struct AttemptError {
    pub(crate) error: Thrown,
    pub(crate) kind: RetryErrorType,
    /// The `retry-after` / `x-amz-retry-after` hint, as an epoch-ms instant.
    pub(crate) retry_after: Option<f64>,
}

/// `THROTTLING_ERROR_CODES`.
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

/// `TRANSIENT_ERROR_CODES`.
const TRANSIENT_ERROR_CODES: [&str; 3] =
    ["TimeoutError", "RequestTimeout", "RequestTimeoutException"];

/// `getRetryErrorType` of a service error response.
pub(crate) fn classify_service_error(
    name: &str,
    status: u16,
    retryable_trait: bool,
) -> RetryErrorType {
    if status == 429 || THROTTLING_ERROR_CODES.contains(&name) {
        return RetryErrorType::Throttling;
    }
    if retryable_trait
        || TRANSIENT_ERROR_CODES.contains(&name)
        || matches!(status, 500 | 502 | 503 | 504)
    {
        return RetryErrorType::Transient;
    }
    if (500..=599).contains(&status) {
        return RetryErrorType::ServerError;
    }
    RetryErrorType::ClientError
}

/// `parseRetryAfterHeader`: the retry hint of an error response.
pub(crate) fn retry_after_hint(headers: &HeaderMap) -> Option<f64> {
    for (name, value) in headers {
        let Ok(value) = value.to_str() else {
            continue;
        };
        if name.as_str() == "retry-after" {
            let seconds = if value.ends_with("GMT") {
                (js_date_parse_http(value)? - now_ms()) / 1000.0
            } else if let Some(position) = value.rfind(" GMT, ") {
                value[position + 6..].parse::<f64>().ok()?
            } else {
                value.parse::<f64>().ok()?
            };
            return Some(now_ms() + seconds * 1000.0);
        }
        if name.as_str() == "x-amz-retry-after" {
            let millis = value.parse::<f64>().ok()?;
            return Some(now_ms() + millis);
        }
    }
    None
}

/// `parseRfc7231DateTime` for the IMF-fixdate form (`Sun, 06 Nov 1994 08:49:37 GMT`).
fn js_date_parse_http(value: &str) -> Option<f64> {
    const MONTHS: [&str; 12] = [
        "Jan", "Feb", "Mar", "Apr", "May", "Jun", "Jul", "Aug", "Sep", "Oct", "Nov", "Dec",
    ];
    let mut parts = value.split(' ');
    let _weekday = parts.next()?;
    let day = parts.next()?;
    let month = parts.next()?;
    let year = parts.next()?;
    let time = parts.next()?;
    let month_index = MONTHS.iter().position(|name| *name == month)? + 1;
    let parsed = js_date_parse(&format!("{year}-{month_index:02}-{day:0>2}T{time}Z"));
    (!parsed.is_nan()).then_some(parsed)
}

/// Headers computed per attempt from the final request URL (the `DPoP`
/// proof of the Signin client's interceptor).
pub(crate) type AttemptHeaders<'a> =
    &'a (dyn Fn(&Method, &Url) -> ProviderResult<Vec<(String, String)>> + Sync);

/// A request the nested client sends (and signs per attempt).
pub(crate) struct PreparedRequest<'a> {
    pub(crate) method: Method,
    /// Path (and query) appended to the endpoint path.
    pub(crate) path_and_query: String,
    pub(crate) headers: Vec<(String, String)>,
    pub(crate) body: Vec<u8>,
    /// `SigV4` credentials; `None` for `smithy.api#noAuth` operations.
    pub(crate) credentials: Option<&'a AwsCredentials>,
    pub(crate) attempt_headers: Option<AttemptHeaders<'a>>,
}

/// A received HTTP response.
pub(crate) struct HttpReply {
    pub(crate) status: u16,
    pub(crate) headers: HeaderMap,
    pub(crate) body: String,
}

impl NestedClient {
    /// The request URL: the endpoint (path included) joined with `path_and_query`.
    fn request_url(&self, path_and_query: &str) -> Result<Url, ProviderFailure> {
        let base = self.endpoint.as_str().trim_end_matches('/');
        Url::parse(&format!("{base}{path_and_query}")).map_err(|_| invalid_url())
    }

    /// Send `request` under the standard retry strategy and hand each
    /// response to `parse`. Network failures retry as transient errors.
    ///
    /// # Errors
    ///
    /// The last attempt's error, or the signal's reason.
    pub(crate) async fn send<T>(
        &self,
        resolution: &Resolution<'_>,
        request: &PreparedRequest<'_>,
        parse: impl Fn(HttpReply) -> Result<T, AttemptError>,
    ) -> ProviderResult<T> {
        let url = self.request_url(&request.path_and_query)?;
        let host = match url.port() {
            Some(port) => format!("{}:{port}", url.host_str().unwrap_or_default()),
            None => url.host_str().unwrap_or_default().to_owned(),
        };
        let invocation_id = Uuid::new_v4().to_string();
        let mut capacity = 500.0;
        let mut retry_count: u32 = 0;
        loop {
            let mut headers = request.headers.clone();
            headers.push(("host".to_owned(), host.clone()));
            if !request.body.is_empty() {
                headers.push(("content-length".to_owned(), request.body.len().to_string()));
            }
            headers.push(("amz-sdk-invocation-id".to_owned(), invocation_id.clone()));
            headers.push((
                "amz-sdk-request".to_owned(),
                format!(
                    "attempt={}; max={}",
                    retry_count + 1,
                    number_to_js_string(self.max_attempts)
                ),
            ));
            if let Some(attempt_headers) = request.attempt_headers {
                headers.extend(attempt_headers(&request.method, &url)?);
            }
            if let Some(credentials) = request.credentials {
                let mut signable = SignableRequest {
                    method: request.method.as_str(),
                    path: url.path(),
                    headers: &mut headers,
                    body: &request.body,
                };
                sign_request(
                    &mut signable,
                    &SigningScope {
                        credentials,
                        region: &self.signing_region,
                        service: self.signing_name,
                        now: SystemTime::now(),
                    },
                );
            }
            let attempt = self.attempt(resolution, &url, request, headers).await?;
            let failure = match attempt {
                Ok(reply) => match parse(reply) {
                    Ok(value) => return Ok(value),
                    Err(failure) => failure,
                },
                Err(failure) => failure,
            };
            let retryable = matches!(
                failure.kind,
                RetryErrorType::Throttling | RetryErrorType::Transient
            );
            let cost = if failure.kind == RetryErrorType::Transient {
                10.0
            } else {
                5.0
            };
            if !retryable || f64::from(retry_count + 1) >= self.max_attempts || capacity < cost {
                return Err(ProviderFailure::thrown(failure.error));
            }
            let base = if failure.kind == RetryErrorType::Throttling {
                500.0
            } else {
                100.0
            };
            let exponent = i32::try_from(retry_count).unwrap_or(i32::MAX);
            let backoff = (base * 2f64.powi(exponent)).min(20_000.0);
            let mut delay = (rand::random::<f64>() * backoff).floor();
            if let Some(hint) = failure.retry_after {
                delay = delay.max((hint - now_ms()).min(delay + 5000.0));
            }
            capacity -= cost;
            resolution.sleep(delay).await?;
            retry_count += 1;
        }
    }

    /// One HTTP exchange: the reply, or a transient network failure.
    async fn attempt(
        &self,
        resolution: &Resolution<'_>,
        url: &Url,
        request: &PreparedRequest<'_>,
        headers: Vec<(String, String)>,
    ) -> ProviderResult<Result<HttpReply, AttemptError>> {
        let mut builder = self
            .http
            .request(request.method.clone(), url.clone())
            .body(request.body.clone());
        for (name, value) in headers {
            builder = builder.header(name, value);
        }
        let exchange = async {
            let response = builder.send().await?;
            let status = response.status().as_u16();
            let headers = response.headers().clone();
            let body = response.bytes().await?;
            Ok::<_, reqwest::Error>(HttpReply {
                status,
                headers,
                body: String::from_utf8_lossy(&body).into_owned(),
            })
        };
        Ok(resolution
            .abortable(exchange)
            .await?
            .map_err(|error| AttemptError {
                error: ErrorObject::new(error.to_string()).thrown(),
                kind: RetryErrorType::Transient,
                retry_after: None,
            }))
    }
}

/// `sanitizeErrorCode`.
fn sanitize_error_code(raw: &str) -> String {
    let mut clean = raw;
    if let Some((first, _)) = clean.split_once(',') {
        clean = first;
    }
    if let Some((first, _)) = clean.split_once(':') {
        clean = first;
    }
    if let Some((_, after)) = clean.split_once('#') {
        clean = after.split('#').next().unwrap_or_default();
    }
    clean.to_owned()
}

/// The `SyntaxError` of a malformed JSON response body.
fn json_body_error(reply: &HttpReply) -> AttemptError {
    let message = js_json_parse(&reply.body)
        .err()
        .map_or_else(String::new, |error| error.message);
    AttemptError {
        error: ErrorObject::named("SyntaxError", message).thrown(),
        kind: classify_service_error("SyntaxError", reply.status, false),
        retry_after: None,
    }
}

/// The `restJson1` service error of a non-2xx response: the code from
/// `x-amzn-errortype`, `code`, or `__type`; the `message` / `Message`; and
/// the modeled `error` member.
pub(crate) fn rest_json_error(reply: &HttpReply) -> AttemptError {
    let body = if reply.body.trim().is_empty() {
        JsonValue::Object(JsonObject::new())
    } else {
        match js_json_parse(&reply.body) {
            Ok(body) => body,
            Err(_) => return json_body_error(reply),
        }
    };
    let string_field = |key: &str| {
        body.get(key)
            .filter(|value| !value.is_null())
            .map(js_to_string)
    };
    let code = reply
        .headers
        .get("x-amzn-errortype")
        .and_then(|value| value.to_str().ok())
        .map(sanitize_error_code)
        .or_else(|| string_field("code"))
        .or_else(|| string_field("__type").map(|value| sanitize_error_code(&value)));
    let name = code.unwrap_or_else(|| "Unknown".to_owned());
    let message = string_field("message")
        .or_else(|| string_field("Message"))
        .unwrap_or_else(|| "Unknown".to_owned());
    let mut error = ErrorObject::named(name.clone(), message);
    error.error = body.get("error").cloned().map(SdkValue::Json);
    error.metadata_http_status_code = Some(JsonValue::from(reply.status));
    AttemptError {
        kind: classify_service_error(&name, reply.status, false),
        error: error.thrown(),
        retry_after: retry_after_hint(&reply.headers),
    }
}

/// A 2xx JSON body (empty reads as `{}`), or the `restJson1` error.
///
/// # Errors
///
/// The service error of a non-2xx response or the `SyntaxError` of a
/// malformed body.
pub(crate) fn json_reply(reply: &HttpReply) -> Result<JsonValue, AttemptError> {
    if !(200..300).contains(&reply.status) {
        return Err(rest_json_error(reply));
    }
    if reply.body.trim().is_empty() {
        return Ok(JsonValue::Object(JsonObject::new()));
    }
    js_json_parse(&reply.body).map_err(|_| json_body_error(reply))
}

/// The proxy of a reused Bedrock request handler: nested clients built from
/// the caller config reuse `requestHandler` unless it is the HTTP/2 default.
pub(crate) fn reused_proxy(handler: &BedrockRequestHandler) -> Option<&Url> {
    match handler {
        BedrockRequestHandler::Proxy(url) => Some(url),
        BedrockRequestHandler::Default | BedrockRequestHandler::Http1 => None,
    }
}
