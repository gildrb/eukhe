//! The AWS SDK default credential and region providers the Bedrock client
//! falls back to when `stream` configures neither: the
//! `@aws-sdk/credential-provider-node` `defaultProvider` chain and the
//! `@smithy/core/config` `NODE_REGION_CONFIG_OPTIONS` loader, ported over raw
//! HTTP. Section of the port of `api/bedrock-converse-stream.ts`.
//!
//! The SDK hands `defaultProvider` the whole Bedrock client config, so the
//! chain also sees the client's `profile`, resolved `region` (the default STS
//! region), and `requestHandler` (reused by the STS client unless it is
//! HTTP/2): [`CallerClientConfig`].

mod container;
mod imds;
mod ini_profile;
mod js_compat;
mod login;
mod process;
mod sdk_client;
mod shared_ini;
mod sso;
mod sts;
#[cfg(test)]
mod tests;

use std::collections::HashMap;
use std::future::Future;
use std::sync::{LazyLock, Mutex, OnceLock};
use std::time::Duration;

use eukhe_chord::context::AbortSignal;

use super::client_config::{AwsCredentials, BedrockRequestHandler};
use crate::utils::diagnostics::{ErrorObject, Thrown};
use js_compat::node_path_join;
use shared_ini::{get_profile_name, load_config, PreferredFile};

/// Module-scope state the SDK keeps for the life of the process.
#[derive(Debug, Default)]
pub(crate) struct SdkProcessState {
    /// `filePromises` of `@smithy/core/config`: shared config/credentials file
    /// text by path, read once per process (`None`: the read failed).
    shared_files: Mutex<HashMap<String, Option<String>>>,
    /// `negativeCacheUntil` of the IMDS region lookup, in epoch milliseconds.
    imds_region_negative_cache_until: Mutex<f64>,
    /// `lastRefreshAttemptTimes` of the SSO token provider, by session name.
    sso_last_refresh_attempts: Mutex<HashMap<String, f64>>,
}

static PROCESS_STATE: LazyLock<SdkProcessState> = LazyLock::new(SdkProcessState::default);

/// The process environment, home directory, and process-wide state the
/// providers read. The public entry points use the real process; tests inject
/// their own.
pub(crate) struct CredentialEnv<'a> {
    /// `process.env[name]`, empty values included.
    pub(crate) var: &'a (dyn Fn(&str) -> Option<String> + Sync),
    /// `os.homedir()`: the last fallback of `getHomeDir`.
    pub(crate) os_home_dir: Option<String>,
    pub(crate) state: &'a SdkProcessState,
}

impl CredentialEnv<'_> {
    /// `process.env[name]`.
    pub(crate) fn var(&self, name: &str) -> Option<String> {
        (self.var)(name)
    }

    /// `process.env[name]` when truthy (set and non-empty).
    pub(crate) fn truthy_var(&self, name: &str) -> Option<String> {
        self.var(name).filter(|value| !value.is_empty())
    }

    /// `getHomeDir()` of `@smithy/core/config`: `HOME`, `USERPROFILE`,
    /// `HOMEDRIVE` + `HOMEPATH`, then `os.homedir()`.
    pub(crate) fn home_dir(&self) -> String {
        if let Some(home) = self.truthy_var("HOME") {
            return home;
        }
        if let Some(profile) = self.truthy_var("USERPROFILE") {
            return profile;
        }
        if let Some(path) = self.truthy_var("HOMEPATH") {
            let drive = self.var("HOMEDRIVE").unwrap_or_else(|| "C:/".to_owned());
            return format!("{drive}{path}");
        }
        self.os_home_dir.clone().unwrap_or_default()
    }

    /// `join(getHomeDir(), ...parts)`.
    pub(crate) fn home_path(&self, parts: &[&str]) -> String {
        let home = self.home_dir();
        let mut all = vec![home.as_str()];
        all.extend_from_slice(parts);
        node_path_join(&all)
    }
}

/// The Bedrock client config the SDK passes to `defaultProvider` as
/// `callerClientConfig` / `parentClientConfig`.
#[derive(Debug, Clone, Copy)]
pub(crate) struct CallerClientConfig<'a> {
    /// `config.profile`.
    pub(crate) profile: Option<&'a str>,
    /// The resolved client region (`await config.region()`).
    pub(crate) region: &'a str,
    /// `config.requestHandler`.
    pub(crate) request_handler: &'a BedrockRequestHandler,
}

/// A provider rejection: the thrown error and its `tryNextLink` flag (errors
/// that are not `ProviderError`s never let a chain continue).
#[derive(Debug, Clone)]
pub(crate) struct ProviderFailure {
    pub(crate) error: Thrown,
    pub(crate) try_next_link: bool,
}

pub(crate) type ProviderResult<T> = Result<T, ProviderFailure>;

impl ProviderFailure {
    fn named(name: &str, message: impl Into<String>, try_next_link: bool) -> Self {
        Self {
            error: ErrorObject::named(name, message).thrown(),
            try_next_link,
        }
    }

    /// `new CredentialsProviderError(message)` (`tryNextLink` defaults to true).
    pub(crate) fn credentials(message: impl Into<String>) -> Self {
        Self::named("CredentialsProviderError", message, true)
    }

    /// `new CredentialsProviderError(message, { tryNextLink: false })`.
    pub(crate) fn credentials_final(message: impl Into<String>) -> Self {
        Self::named("CredentialsProviderError", message, false)
    }

    /// `new ProviderError(message)`.
    pub(crate) fn provider(message: impl Into<String>) -> Self {
        Self::named("ProviderError", message, true)
    }

    /// `new TokenProviderError(message, tryNextLink)`.
    pub(crate) fn token(message: impl Into<String>, try_next_link: bool) -> Self {
        Self::named("TokenProviderError", message, try_next_link)
    }

    /// Any other thrown error (no `tryNextLink`).
    pub(crate) fn thrown(error: Thrown) -> Self {
        Self {
            error,
            try_next_link: false,
        }
    }

    /// A thrown `ErrorObject`.
    pub(crate) fn error(error: ErrorObject) -> Self {
        Self::thrown(error.thrown())
    }

    /// `error.message`.
    pub(crate) fn message(&self) -> String {
        self.error.to_string()
    }
}

/// One `defaultProvider()` call: the environment, the caller's client config,
/// the abort signal, and the chain's shared `init` state.
pub(crate) struct Resolution<'a> {
    pub(crate) env: &'a CredentialEnv<'a>,
    pub(crate) caller: CallerClientConfig<'a>,
    pub(crate) signal: Option<&'a AbortSignal>,
    /// The region of `init.roleAssumer`, fixed by the first assume-role
    /// profile the chain resolves (`region ?? parentClientConfig.region`).
    pub(crate) role_assumer_region: OnceLock<String>,
}

impl Resolution<'_> {
    /// Run `future` unless the signal aborts first (then its reason).
    pub(crate) async fn abortable<F: Future>(&self, future: F) -> ProviderResult<F::Output> {
        let Some(signal) = self.signal else {
            return Ok(future.await);
        };
        tokio::select! {
            biased;
            reason = signal.cancelled() => Err(ProviderFailure::thrown(reason)),
            output = future => Ok(output),
        }
    }

    /// `setTimeout` delay, abortable.
    pub(crate) async fn sleep(&self, millis: f64) -> ProviderResult<()> {
        let duration = Duration::from_secs_f64(millis.max(0.0) / 1000.0);
        self.abortable(tokio::time::sleep(duration)).await
    }

    /// `getProfileName({ profile: init.profile })`.
    pub(crate) fn profile_name(&self) -> String {
        get_profile_name(self.env, self.caller.profile)
    }
}

/// SDK `defaultProvider({ profile })()`.
///
/// `client_region` is the Bedrock client's resolved region and
/// `request_handler` its request handler: the SDK passes the whole client
/// config to the chain (the STS role assumers default to that region and
/// reuse a non-HTTP/2 handler).
///
/// # Errors
///
/// The chain's terminal error (`CredentialsProviderError: Could not load
/// credentials from any providers`, or the first error that stops the chain),
/// or the signal's reason when it aborts.
pub(crate) async fn resolve_default_credentials(
    profile: Option<&str>,
    client_region: &str,
    request_handler: &BedrockRequestHandler,
    signal: Option<&AbortSignal>,
) -> Result<AwsCredentials, Thrown> {
    let var = |name: &str| std::env::var(name).ok();
    let env = process_env(&var);
    let caller = CallerClientConfig {
        profile,
        region: client_region,
        request_handler,
    };
    default_provider(&env, caller, signal).await
}

/// SDK default region provider for a client whose `region` is unset
/// (`loadConfig(NODE_REGION_CONFIG_OPTIONS, { ...NODE_REGION_CONFIG_FILE_OPTIONS,
/// profile })`): `AWS_REGION`, the profile's `region` (credentials file
/// first), the EC2 instance metadata region, else `Region is missing`.
///
/// # Errors
///
/// `Error: Region is missing`, or the signal's reason when it aborts.
pub(crate) async fn resolve_default_region(
    profile: Option<&str>,
    signal: Option<&AbortSignal>,
) -> Result<String, Thrown> {
    let var = |name: &str| std::env::var(name).ok();
    let env = process_env(&var);
    default_region(&env, profile, signal).await
}

fn process_env(var: &(dyn Fn(&str) -> Option<String> + Sync)) -> CredentialEnv<'_> {
    CredentialEnv {
        var,
        os_home_dir: std::env::home_dir().map(|path| path.to_string_lossy().into_owned()),
        state: &PROCESS_STATE,
    }
}

/// The region loader over an injected environment.
pub(crate) async fn default_region(
    env: &CredentialEnv<'_>,
    profile: Option<&str>,
    signal: Option<&AbortSignal>,
) -> Result<String, Thrown> {
    let configured = load_config(
        env,
        profile,
        PreferredFile::Credentials,
        |env| env.var("AWS_REGION"),
        |profile, _| profile.get("region").map(str::to_owned),
    )
    .await;
    if let Some(region) = configured {
        return Ok(region);
    }
    let lookup = imds::instance_metadata_region(env);
    let region = match signal {
        None => lookup.await,
        Some(signal) => tokio::select! {
            biased;
            reason = signal.cancelled() => return Err(reason),
            region = lookup => region,
        },
    };
    region.ok_or_else(|| ErrorObject::new("Region is missing").thrown())
}

/// The links of `defaultProvider`, in order.
#[derive(Debug, Clone, Copy)]
enum ChainLink {
    Env,
    Sso,
    Ini,
    Process,
    TokenFile,
    Remote,
    Final,
}

const DEFAULT_CHAIN: [ChainLink; 7] = [
    ChainLink::Env,
    ChainLink::Sso,
    ChainLink::Ini,
    ChainLink::Process,
    ChainLink::TokenFile,
    ChainLink::Remote,
    ChainLink::Final,
];

/// `defaultProvider(init)()` over an injected environment.
pub(crate) async fn default_provider(
    env: &CredentialEnv<'_>,
    caller: CallerClientConfig<'_>,
    signal: Option<&AbortSignal>,
) -> Result<AwsCredentials, Thrown> {
    let resolution = Resolution {
        env,
        caller,
        signal,
        role_assumer_region: OnceLock::new(),
    };
    let mut last_error = None;
    for link in DEFAULT_CHAIN {
        match run_link(&resolution, link).await {
            Ok(credentials) => return Ok(credentials),
            Err(failure) if failure.try_next_link => last_error = Some(failure.error),
            Err(failure) => return Err(failure.error),
        }
    }
    // The final link never lets the chain continue.
    Err(last_error.unwrap_or_else(|| ErrorObject::new("No providers in chain").thrown()))
}

async fn run_link(resolution: &Resolution<'_>, link: ChainLink) -> ProviderResult<AwsCredentials> {
    match link {
        ChainLink::Env => {
            let profile = resolution
                .caller
                .profile
                .map(str::to_owned)
                .or_else(|| resolution.env.var("AWS_PROFILE"));
            if profile.is_some_and(|profile| !profile.is_empty()) {
                // The SDK also prints a one-time console warning when the
                // static env keys are set too; this port does not write to
                // the terminal.
                return Err(ProviderFailure::credentials(
                    "AWS_PROFILE is set, skipping fromEnv provider.",
                ));
            }
            from_env(resolution.env)
        }
        // `init` is the Bedrock client config: it never carries `ssoStartUrl`,
        // `ssoAccountId`, `ssoRegion`, `ssoRoleName`, or `ssoSession`, so SSO
        // profiles resolve through `fromIni`.
        ChainLink::Sso => Err(ProviderFailure::credentials(
            "Skipping SSO provider in default chain (inputs do not include SSO fields).",
        )),
        ChainLink::Ini => ini_profile::from_ini(resolution).await,
        ChainLink::Process => {
            let profile_name = resolution.profile_name();
            process::from_process(resolution, &profile_name).await
        }
        ChainLink::TokenFile => {
            sts::from_token_file(resolution, sts::TokenFileInit::default()).await
        }
        ChainLink::Remote => remote_provider(resolution).await,
        ChainLink::Final => Err(ProviderFailure::credentials_final(
            "Could not load credentials from any providers",
        )),
    }
}

/// `fromEnv()` of `@aws-sdk/credential-provider-env`.
pub(crate) fn from_env(env: &CredentialEnv<'_>) -> ProviderResult<AwsCredentials> {
    match (
        env.truthy_var("AWS_ACCESS_KEY_ID"),
        env.truthy_var("AWS_SECRET_ACCESS_KEY"),
    ) {
        (Some(access_key_id), Some(secret_access_key)) => Ok(AwsCredentials {
            access_key_id,
            secret_access_key,
            session_token: env.truthy_var("AWS_SESSION_TOKEN"),
        }),
        _ => Err(ProviderFailure::credentials(
            "Unable to find environment variable credentials.",
        )),
    }
}

/// `remoteProvider(init)()` of `@aws-sdk/credential-provider-node`.
async fn remote_provider(resolution: &Resolution<'_>) -> ProviderResult<AwsCredentials> {
    let env = resolution.env;
    if env
        .truthy_var("AWS_CONTAINER_CREDENTIALS_RELATIVE_URI")
        .is_some()
        || env
            .truthy_var("AWS_CONTAINER_CREDENTIALS_FULL_URI")
            .is_some()
    {
        return container::from_http_then_container_metadata(resolution).await;
    }
    if env
        .truthy_var("AWS_EC2_METADATA_DISABLED")
        .is_some_and(|value| value != "false")
    {
        return Err(ProviderFailure::credentials(
            "EC2 Instance Metadata Service access disabled",
        ));
    }
    imds::from_instance_metadata(resolution).await
}
