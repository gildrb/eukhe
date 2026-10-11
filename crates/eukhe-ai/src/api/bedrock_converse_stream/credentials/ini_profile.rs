//! `fromIni` of `@aws-sdk/credential-provider-ini`: `resolveProfileData`
//! over the merged shared files (assume-role, static keys, web identity,
//! `credential_process`, SSO, and `aws login` profiles).

use futures::future::BoxFuture;
use futures::FutureExt;

use super::super::client_config::AwsCredentials;
use super::js_compat::{js_parse_int, now_ms};
use super::shared_ini::{js_key_order, parse_known_files, IniFile, IniSection};
use super::sts::{assume_role, from_token_file, AssumeRoleParams, TokenFileInit};
use super::{
    container, from_env, imds, login, process, sso, ProviderFailure, ProviderResult, Resolution,
};
use crate::utils::diagnostics::ErrorObject;
use crate::utils::js::number_to_js_string;

/// `isStaticCredsProfile`.
fn is_static_creds_profile(data: Option<&IniSection>) -> bool {
    data.is_some_and(|data| {
        data.get("aws_access_key_id").is_some() && data.get("aws_secret_access_key").is_some()
    })
}

/// `isAssumeRoleWithSourceProfile || isCredentialSourceProfile` behind
/// `isAssumeRoleProfile`.
fn is_assume_role_profile(data: Option<&IniSection>) -> bool {
    data.is_some_and(|data| {
        data.get("role_arn").is_some()
            && (data.get("source_profile").is_some() != data.get("credential_source").is_some())
    })
}

/// `isWebIdentityProfile`.
fn is_web_identity_profile(data: Option<&IniSection>) -> bool {
    data.is_some_and(|data| {
        data.get("web_identity_token_file").is_some() && data.get("role_arn").is_some()
    })
}

/// `isSsoProfile`.
fn is_sso_profile(data: Option<&IniSection>) -> bool {
    data.is_some_and(|data| {
        [
            "sso_start_url",
            "sso_account_id",
            "sso_session",
            "sso_region",
            "sso_role_name",
        ]
        .iter()
        .any(|key| data.get(key).is_some())
    })
}

/// `isCredentialSourceWithoutRoleArn`.
fn is_credential_source_without_role_arn(data: Option<&IniSection>) -> bool {
    data.is_some_and(|data| {
        data.get("role_arn").is_none() && data.get("credential_source").is_some()
    })
}

/// `resolveStaticCredentials(profile)`.
fn static_credentials(data: &IniSection) -> AwsCredentials {
    AwsCredentials {
        access_key_id: data.get("aws_access_key_id").unwrap_or_default().to_owned(),
        secret_access_key: data
            .get("aws_secret_access_key")
            .unwrap_or_default()
            .to_owned(),
        session_token: data.get("aws_session_token").map(str::to_owned),
    }
}

/// `credential_source` providers of `resolveCredentialSource`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum CredentialSource {
    EcsContainer,
    Ec2InstanceMetadata,
    Environment,
}

fn credential_source(value: &str, profile_name: &str) -> ProviderResult<CredentialSource> {
    match value {
        "EcsContainer" => Ok(CredentialSource::EcsContainer),
        "Ec2InstanceMetadata" => Ok(CredentialSource::Ec2InstanceMetadata),
        "Environment" => Ok(CredentialSource::Environment),
        other => Err(ProviderFailure::credentials(format!(
            "Unsupported credential source in profile {profile_name}. Got {other}, expected EcsContainer or Ec2InstanceMetadata or Environment."
        ))),
    }
}

async fn resolve_credential_source(
    resolution: &Resolution<'_>,
    source: CredentialSource,
) -> ProviderResult<AwsCredentials> {
    match source {
        CredentialSource::EcsContainer => {
            container::from_http_then_container_metadata(resolution).await
        }
        CredentialSource::Ec2InstanceMetadata => imds::from_instance_metadata(resolution).await,
        CredentialSource::Environment => from_env(resolution.env),
    }
}

/// `resolveAssumeRoleCredentials(profileName, profiles, …)`.
async fn resolve_assume_role_credentials(
    resolution: &Resolution<'_>,
    profile_name: &str,
    profiles: &IniFile,
    visited: &[String],
) -> ProviderResult<AwsCredentials> {
    let Some(data) = profiles.get(profile_name) else {
        return Err(ProviderFailure::error(ErrorObject::named(
            "TypeError",
            "Cannot destructure property 'source_profile' of 'profileData' as it is undefined.",
        )));
    };
    let source_profile = data.get("source_profile");
    let region = resolution
        .role_assumer_region
        .get_or_init(|| {
            data.get("region")
                .unwrap_or(resolution.caller.region)
                .to_owned()
        })
        .clone();
    if let Some(source_profile) = source_profile {
        if visited.iter().any(|visited| visited == source_profile) {
            let names = js_key_order(visited.iter().map(String::as_str)).join(", ");
            return Err(ProviderFailure::credentials(format!(
                "Detected a cycle attempting to resolve credentials for profile {}. Profiles visited: {names}",
                resolution.profile_name()
            )));
        }
    }
    // The SDK starts the source provider before the MFA check below; here it
    // starts after it, so an MFA failure never leaves a provider running.
    let source = match source_profile {
        Some(source_profile) => SourceCredentials::Profile(source_profile.to_owned()),
        None => SourceCredentials::Provider(credential_source(
            data.get("credential_source").unwrap_or("undefined"),
            profile_name,
        )?),
    };
    let resolve_source = || async {
        match &source {
            SourceCredentials::Profile(source_profile) => {
                let mut next_visited = visited.to_vec();
                next_visited.push(source_profile.clone());
                let recursive = is_credential_source_without_role_arn(profiles.get(source_profile));
                resolve_profile_data(
                    resolution,
                    source_profile,
                    profiles,
                    next_visited,
                    recursive,
                )
                .await
            }
            SourceCredentials::Provider(provider) => {
                resolve_credential_source(resolution, *provider).await
            }
        }
    };
    if is_credential_source_without_role_arn(Some(data)) {
        return resolve_source().await;
    }
    let duration = data.get("duration_seconds").unwrap_or("3600");
    let params = AssumeRoleParams {
        role_arn: data.get("role_arn").unwrap_or_default().to_owned(),
        role_session_name: data.get("role_session_name").map_or_else(
            || format!("aws-sdk-js-{}", number_to_js_string(now_ms())),
            str::to_owned,
        ),
        external_id: data.get("external_id").map(str::to_owned),
        duration_seconds: js_parse_int(duration, Some(10)),
    };
    if data.get("mfa_serial").is_some() {
        return Err(ProviderFailure::credentials_final(format!(
            "Profile {profile_name} requires multi-factor authentication, but no MFA code callback was provided."
        )));
    }
    let source_credentials = resolve_source().await?;
    assume_role(resolution, &region, &source_credentials, &params).await
}

/// Where an assume-role profile's source credentials come from.
enum SourceCredentials {
    Profile(String),
    Provider(CredentialSource),
}

/// `resolveProfileData(profileName, profiles, …, visitedProfiles,
/// isAssumeRoleRecursiveCall)`.
fn resolve_profile_data<'a>(
    resolution: &'a Resolution<'a>,
    profile_name: &'a str,
    profiles: &'a IniFile,
    visited: Vec<String>,
    assume_role_recursive_call: bool,
) -> BoxFuture<'a, ProviderResult<AwsCredentials>> {
    async move {
        let data = profiles.get(profile_name);
        if !visited.is_empty() && is_static_creds_profile(data) {
            return Ok(static_credentials(data.unwrap_or(&IniSection::default())));
        }
        if assume_role_recursive_call || is_assume_role_profile(data) {
            return resolve_assume_role_credentials(resolution, profile_name, profiles, &visited)
                .await;
        }
        if let Some(data) = data.filter(|data| is_static_creds_profile(Some(data))) {
            return Ok(static_credentials(data));
        }
        if let Some(data) = data.filter(|data| is_web_identity_profile(Some(data))) {
            return from_token_file(
                resolution,
                TokenFileInit {
                    web_identity_token_file: data.get("web_identity_token_file").map(str::to_owned),
                    role_arn: data.get("role_arn").map(str::to_owned),
                    role_session_name: data.get("role_session_name").map(str::to_owned),
                },
            )
            .await;
        }
        if data.is_some_and(|data| data.get("credential_process").is_some()) {
            return process::from_process(resolution, profile_name).await;
        }
        if is_sso_profile(data) {
            return sso::from_sso_profile(resolution, profile_name).await;
        }
        if data.is_some_and(|data| data.get("login_session").is_some()) {
            return login::from_login_credentials(resolution, profile_name).await;
        }
        Err(ProviderFailure::credentials(format!(
            "Could not resolve credentials using profile: [{profile_name}] in configuration/credentials file(s)."
        )))
    }
    .boxed()
}

/// `fromIni(init)()`.
///
/// # Errors
///
/// The profile's resolution error (`Could not resolve credentials using
/// profile` lets the chain continue).
pub(crate) async fn from_ini(resolution: &Resolution<'_>) -> ProviderResult<AwsCredentials> {
    let profiles = parse_known_files(resolution.env).await;
    let profile_name = resolution.profile_name();
    resolve_profile_data(resolution, &profile_name, &profiles, Vec::new(), false).await
}
