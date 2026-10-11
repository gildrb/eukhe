//! `fromProcess` of `@aws-sdk/credential-provider-process`: run the profile's
//! `credential_process` through the shell (Node `child_process.exec`) and
//! read its `Version: 1` JSON.

use std::process::Stdio;

use eukhe_types::pi_ai::JsonValue;
use tokio::io::{AsyncRead, AsyncReadExt};
use tokio::process::Command;

use super::super::client_config::AwsCredentials;
use super::js_compat::{js_date_from_json, json_property, json_truthy, now_ms};
use super::shared_ini::{get_profile_name, parse_known_files, IniFile};
use super::{ProviderFailure, ProviderResult, Resolution};
use crate::utils::diagnostics::ErrorObject;
use crate::utils::js::{js_to_string, js_trim};
use crate::utils::json_parse::js_json_parse;

/// `exec`'s default `maxBuffer` (bytes per output stream).
const MAX_BUFFER: usize = 1024 * 1024;

/// Read the `name` stream (`stdout` / `stderr`) up to `limit` bytes; the
/// error message once it exceeds the limit or the read fails.
async fn read_limited(
    mut stream: impl AsyncRead + Unpin,
    name: &str,
    limit: usize,
) -> Result<Vec<u8>, String> {
    let mut collected = Vec::new();
    let mut chunk = vec![0_u8; 8192];
    loop {
        let read = stream
            .read(&mut chunk)
            .await
            .map_err(|error| format!("{name} {error}"))?;
        if read == 0 {
            return Ok(collected);
        }
        collected.extend_from_slice(&chunk[..read]);
        if collected.len() > limit {
            return Err(format!("{name} maxBuffer length exceeded"));
        }
    }
}

/// Node `promisify(exec)(command)`: stdout on a zero exit, else the error
/// message (`Command failed: <command>\n<stderr>`).
async fn exec(command: &str) -> Result<String, String> {
    let mut child = Command::new("/bin/sh")
        .arg("-c")
        .arg(command)
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .kill_on_drop(true)
        .spawn()
        .map_err(|error| format!("spawn /bin/sh {error}"))?;
    // exec leaves the child's stdin pipe open.
    let stdin = child.stdin.take();
    let (Some(stdout), Some(stderr)) = (child.stdout.take(), child.stderr.take()) else {
        return Err("spawn /bin/sh: missing stdio pipes".to_owned());
    };
    let output = tokio::try_join!(
        read_limited(stdout, "stdout", MAX_BUFFER),
        read_limited(stderr, "stderr", MAX_BUFFER),
    );
    let (stdout, stderr) = match output {
        Ok(output) => output,
        Err(message) => {
            child.start_kill().ok();
            return Err(message);
        }
    };
    let status = child.wait().await.map_err(|error| error.to_string())?;
    drop(stdin);
    let stdout = String::from_utf8_lossy(&stdout).into_owned();
    if status.success() {
        Ok(stdout)
    } else {
        let stderr = String::from_utf8_lossy(&stderr);
        Err(format!("Command failed: {command}\n{stderr}"))
    }
}

/// `String(value)` of a credential field.
fn field_string(value: &JsonValue) -> String {
    js_to_string(value)
}

/// `getValidatedProcessCredentials(profileName, data, profiles)`.
fn validated_process_credentials(
    profile_name: &str,
    data: &JsonValue,
) -> Result<AwsCredentials, ErrorObject> {
    let version = json_property(data, "Version")?;
    // JS `data.Version !== 1`: exact equality with the number 1.
    let is_version_one =
        version.and_then(JsonValue::as_f64).map(f64::to_bits) == Some(1_f64.to_bits());
    if !is_version_one {
        return Err(ErrorObject::new(format!(
            "Profile {profile_name} credential_process did not return Version 1."
        )));
    }
    let (Some(access_key_id), Some(secret_access_key)) = (
        json_property(data, "AccessKeyId")?,
        json_property(data, "SecretAccessKey")?,
    ) else {
        return Err(ErrorObject::new(format!(
            "Profile {profile_name} credential_process returned invalid credentials."
        )));
    };
    let expiration = json_property(data, "Expiration")?;
    if json_truthy(expiration) {
        let expire_time = expiration.map_or(f64::NAN, js_date_from_json);
        if expire_time < now_ms() {
            return Err(ErrorObject::new(format!(
                "Profile {profile_name} credential_process returned expired credentials."
            )));
        }
    }
    let session_token = json_property(data, "SessionToken")?;
    Ok(AwsCredentials {
        access_key_id: field_string(access_key_id),
        secret_access_key: field_string(secret_access_key),
        session_token: json_truthy(session_token)
            .then(|| session_token.map(field_string))
            .flatten(),
    })
}

/// `resolveProcessCredentials(profileName, profiles)`.
async fn resolve_process_credentials(
    resolution: &Resolution<'_>,
    profile_name: &str,
    profiles: &IniFile,
) -> ProviderResult<AwsCredentials> {
    let Some(profile) = profiles.get(profile_name) else {
        return Err(ProviderFailure::credentials(format!(
            "Profile {profile_name} could not be found in shared credentials file."
        )));
    };
    let Some(command) = profile.get("credential_process") else {
        return Err(ProviderFailure::credentials(format!(
            "Profile {profile_name} did not contain credential_process."
        )));
    };
    let stdout = resolution
        .abortable(exec(command))
        .await?
        .map_err(ProviderFailure::credentials)?;
    let data = js_json_parse(js_trim(&stdout)).map_err(|_| {
        ProviderFailure::credentials(format!(
            "Profile {profile_name} credential_process returned invalid JSON."
        ))
    })?;
    validated_process_credentials(profile_name, &data)
        .map_err(|error| ProviderFailure::credentials(error.message))
}

/// `fromProcess({ profile })()`: `profile` is the explicit profile (`None`
/// falls back to `AWS_PROFILE` / `default`).
///
/// # Errors
///
/// `CredentialsProviderError`s (all let the chain continue), or the signal's
/// reason.
pub(crate) async fn from_process(
    resolution: &Resolution<'_>,
    profile: &str,
) -> ProviderResult<AwsCredentials> {
    let profiles = parse_known_files(resolution.env).await;
    let profile_name = get_profile_name(resolution.env, Some(profile));
    resolve_process_credentials(resolution, &profile_name, &profiles).await
}
