//! `NodeAuth` of the `@google/genai` Node build: an API key header, or
//! `google-auth-library` Application Default Credentials (ADC) with the
//! `cloud-platform` scope.
//!
//! The ADC subset ported: an explicit `keyFilename`, then the
//! `GOOGLE_APPLICATION_CREDENTIALS` file, then gcloud's well-known
//! `application_default_credentials.json`, then the GCE metadata server.
//! Credential files of type `authorized_user` (OAuth refresh token) and
//! `service_account` (RS256 JWT-bearer grant, the `gtoken` flow) are
//! supported; the other `google-auth-library` credential types
//! (`external_account`, `impersonated_service_account`,
//! `external_account_authorized_user`, `gdch_service_account`) fail with an
//! error naming the type. `GOOGLE_CLOUD_QUOTA_PROJECT` / `quota_project_id`
//! become `x-goog-user-project`. A client is created per request in the TS
//! adapters, so tokens are not cached across requests.

use std::path::{Path, PathBuf};
use std::time::Duration;

use base64::Engine as _;
use eukhe_chord::context::AbortSignal;
use eukhe_types::pi_ai::{JsonObject, JsonValue};
use serde_json::json;

use super::{append_header, has_header, HTTP_CLIENT};
use crate::utils::diagnostics::{ErrorObject, Thrown};
use crate::utils::js::json_stringify;
use crate::utils::json_parse::json_parse;

const GOOGLE_API_KEY_HEADER: &str = "x-goog-api-key";
const REQUIRED_VERTEX_AI_SCOPE: &str = "https://www.googleapis.com/auth/cloud-platform";
const GOOGLE_TOKEN_URL: &str = "https://oauth2.googleapis.com/token";
const JWT_BEARER_GRANT_TYPE: &str = "urn:ietf:params:oauth:grant-type:jwt-bearer";
const NO_ADC_FOUND: &str = "Could not load the default credentials. Browse to https://cloud.google.com/docs/authentication/getting-started for more information.";
/// gcp-metadata's availability probe timeout.
const METADATA_PROBE_TIMEOUT: Duration = Duration::from_millis(3000);

/// `googleAuthOptions` the adapters pass (`{ keyFilename }`).
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct GoogleAuthOptions {
    pub key_filename: String,
}

/// The SDK's request authentication.
pub(super) enum NodeAuth {
    ApiKey(String),
    GoogleAuth(Option<GoogleAuthOptions>),
}

fn error(message: impl Into<String>) -> Thrown {
    ErrorObject::new(message).thrown()
}

impl NodeAuth {
    pub(super) fn new(api_key: Option<String>, options: Option<GoogleAuthOptions>) -> Self {
        match api_key {
            Some(api_key) => Self::ApiKey(api_key),
            None => Self::GoogleAuth(options),
        }
    }

    /// `addAuthHeaders(headers, url)`: never overrides a header already set.
    pub(super) async fn add_auth_headers(
        &self,
        headers: &mut Vec<(String, String)>,
        _url: &str,
        signal: Option<&AbortSignal>,
    ) -> Result<(), Thrown> {
        match self {
            Self::ApiKey(api_key) => {
                if api_key.starts_with("auth_tokens/") {
                    return Err(error(
                        "Ephemeral tokens are only supported by the live API.",
                    ));
                }
                if !has_header(headers, GOOGLE_API_KEY_HEADER) {
                    append_header(headers, GOOGLE_API_KEY_HEADER, api_key);
                }
                Ok(())
            }
            Self::GoogleAuth(options) => {
                let credential = get_client(options.as_ref(), signal).await?;
                for (name, value) in credential.request_headers() {
                    if !has_header(headers, &name) {
                        append_header(headers, &name, &value);
                    }
                }
                Ok(())
            }
        }
    }
}

/// A resolved credential with its access token.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) struct AccessCredential {
    pub(super) access_token: String,
    pub(super) quota_project_id: Option<String>,
}

impl AccessCredential {
    /// `client.getRequestHeaders()`: `authorization` plus the shared
    /// `x-goog-user-project`.
    fn request_headers(&self) -> Vec<(String, String)> {
        let mut headers = vec![(
            "authorization".to_owned(),
            format!("Bearer {}", self.access_token),
        )];
        if let Some(project) = self.quota_project_id.as_ref().filter(|p| !p.is_empty()) {
            headers.push(("x-goog-user-project".to_owned(), project.clone()));
        }
        headers
    }
}

fn process_env(name: &str) -> Option<String> {
    std::env::var(name).ok().filter(|value| !value.is_empty())
}

/// `googleAuth.getClient()` + an access token.
async fn get_client(
    options: Option<&GoogleAuthOptions>,
    signal: Option<&AbortSignal>,
) -> Result<AccessCredential, Thrown> {
    let quota_override = process_env("GOOGLE_CLOUD_QUOTA_PROJECT");
    let mut credential = if let Some(options) = options.filter(|o| !o.key_filename.is_empty()) {
        let path = absolute(Path::new(&options.key_filename));
        let json = read_credential_file(&path)?;
        credential_from_json(&json, signal).await?
    } else {
        application_default(signal).await?
    };
    if quota_override.is_some() {
        credential.quota_project_id = quota_override;
    }
    Ok(credential)
}

/// `path.resolve(p)`.
fn absolute(path: &Path) -> PathBuf {
    if path.is_absolute() {
        path.to_path_buf()
    } else {
        std::env::current_dir().map_or_else(|_| path.to_path_buf(), |cwd| cwd.join(path))
    }
}

/// `fs.createReadStream(path)` + `JSON.parse`.
fn read_credential_file(path: &Path) -> Result<JsonValue, Thrown> {
    let text = std::fs::read_to_string(path).map_err(|io_error| {
        let message = match io_error.kind() {
            std::io::ErrorKind::NotFound => format!(
                "ENOENT: no such file or directory, open '{}'",
                path.display()
            ),
            std::io::ErrorKind::PermissionDenied => {
                format!("EACCES: permission denied, open '{}'", path.display())
            }
            _ => format!("{io_error}, open '{}'", path.display()),
        };
        error(message)
    })?;
    json_parse(&text)
        .map_err(|parse_error| ErrorObject::named("SyntaxError", parse_error.message).thrown())
}

/// `_getApplicationCredentialsFromFilePath(filePath)`.
fn read_application_credentials(path: &str) -> Result<JsonValue, Thrown> {
    if path.is_empty() {
        return Err(error("The file path is invalid."));
    }
    let resolved = std::fs::canonicalize(path)
        .ok()
        .filter(|resolved| resolved.is_file())
        .ok_or_else(|| {
            error(format!(
                "The file at {path} does not exist, or it is not a file. ENOENT: no such file or directory, lstat '{path}'"
            ))
        })?;
    read_credential_file(&resolved)
}

/// `getApplicationDefaultAsync()`.
async fn application_default(signal: Option<&AbortSignal>) -> Result<AccessCredential, Thrown> {
    let env_path = process_env("GOOGLE_APPLICATION_CREDENTIALS")
        .or_else(|| process_env("google_application_credentials"));
    if let Some(path) = env_path {
        let json = read_application_credentials(&path).map_err(|cause| {
            error(format!(
                "Unable to read the credential file specified by the GOOGLE_APPLICATION_CREDENTIALS environment variable: {cause}"
            ))
        })?;
        return credential_from_json(&json, signal).await;
    }
    let config_dir = process_env("CLOUDSDK_CONFIG")
        .map(PathBuf::from)
        .or_else(|| {
            process_env("HOME").map(|home| Path::new(&home).join(".config").join("gcloud"))
        });
    if let Some(config_dir) = config_dir {
        let location = config_dir.join("application_default_credentials.json");
        if location.exists() {
            let json = read_application_credentials(&location.to_string_lossy())?;
            return credential_from_json(&json, signal).await;
        }
    }
    if is_gce(signal).await {
        return compute_credential(signal).await;
    }
    Err(error(NO_ADC_FOUND))
}

fn string_field<'a>(json: &'a JsonValue, key: &str) -> Option<&'a str> {
    json.get(key)
        .and_then(JsonValue::as_str)
        .filter(|value| !value.is_empty())
}

fn required_field<'a>(json: &'a JsonValue, key: &str) -> Result<&'a str, Thrown> {
    string_field(json, key).ok_or_else(|| {
        error(format!(
            "The incoming JSON object does not contain a {key} field"
        ))
    })
}

/// `googleAuth.fromJSON(json)` + the client's first token.
async fn credential_from_json(
    json: &JsonValue,
    signal: Option<&AbortSignal>,
) -> Result<AccessCredential, Thrown> {
    let quota_project_id = string_field(json, "quota_project_id").map(str::to_owned);
    match json.get("type").and_then(JsonValue::as_str) {
        Some("authorized_user") => {
            let client_id = required_field(json, "client_id")?;
            let client_secret = required_field(json, "client_secret")?;
            let refresh_token = required_field(json, "refresh_token")?;
            let tokens = post_form(
                GOOGLE_TOKEN_URL,
                &[
                    ("refresh_token", refresh_token),
                    ("client_id", client_id),
                    ("client_secret", client_secret),
                    ("grant_type", "refresh_token"),
                ],
                signal,
            )
            .await?;
            Ok(AccessCredential {
                access_token: access_token(&tokens)?,
                quota_project_id,
            })
        }
        Some(
            kind @ ("external_account"
            | "impersonated_service_account"
            | "external_account_authorized_user"
            | "gdch_service_account"),
        ) => Err(error(format!(
            "Unsupported Google credential type for Vertex AI: {kind}"
        ))),
        _ => {
            let client_email = required_field(json, "client_email")?;
            let private_key = required_field(json, "private_key")?;
            let assertion = sign_jwt_assertion(client_email, private_key, crate::utils::now_ms())?;
            let tokens = post_form(
                GOOGLE_TOKEN_URL,
                &[
                    ("grant_type", JWT_BEARER_GRANT_TYPE),
                    ("assertion", &assertion),
                ],
                signal,
            )
            .await?;
            Ok(AccessCredential {
                access_token: access_token(&tokens)?,
                quota_project_id,
            })
        }
    }
}

fn access_token(tokens: &JsonValue) -> Result<String, Thrown> {
    string_field(tokens, "access_token")
        .map(str::to_owned)
        .ok_or_else(|| error("No access token returned by the Google token endpoint"))
}

fn base64url(bytes: &[u8]) -> String {
    base64::engine::general_purpose::URL_SAFE_NO_PAD.encode(bytes)
}

/// The `gtoken` JWT-bearer assertion: `{ alg: "RS256" }` header and
/// `{ iss, scope, aud, exp, iat }` payload, RS256-signed.
pub(super) fn sign_jwt_assertion(
    client_email: &str,
    private_key_pem: &str,
    now_ms: u64,
) -> Result<String, Thrown> {
    let iat = now_ms / 1000;
    let header = json_stringify(&json!({ "alg": "RS256" }));
    let mut payload = JsonObject::new();
    payload.insert("iss".into(), client_email.into());
    payload.insert("scope".into(), REQUIRED_VERTEX_AI_SCOPE.into());
    payload.insert("aud".into(), GOOGLE_TOKEN_URL.into());
    payload.insert("exp".into(), (iat + 3600).into());
    payload.insert("iat".into(), iat.into());
    let payload = json_stringify(&JsonValue::Object(payload));
    let signing_input = format!(
        "{}.{}",
        base64url(header.as_bytes()),
        base64url(payload.as_bytes())
    );
    let der = pem_to_der(private_key_pem)?;
    let key_pair = ring::signature::RsaKeyPair::from_pkcs8(&der)
        .map_err(|rejected| error(format!("Invalid service account private key: {rejected}")))?;
    let mut signature = vec![0; key_pair.public().modulus_len()];
    key_pair
        .sign(
            &ring::signature::RSA_PKCS1_SHA256,
            &ring::rand::SystemRandom::new(),
            signing_input.as_bytes(),
            &mut signature,
        )
        .map_err(|_| error("Failed to sign the service account JWT"))?;
    Ok(format!("{signing_input}.{}", base64url(&signature)))
}

/// The DER bytes of a `-----BEGIN PRIVATE KEY-----` PEM block.
fn pem_to_der(pem: &str) -> Result<Vec<u8>, Thrown> {
    let body: String = pem
        .lines()
        .map(str::trim)
        .filter(|line| !line.starts_with("-----"))
        .collect();
    base64::engine::general_purpose::STANDARD
        .decode(body)
        .map_err(|decode_error| {
            error(format!(
                "Invalid service account private key: {decode_error}"
            ))
        })
}

/// A form POST to a token endpoint; the parsed JSON response.
async fn post_form(
    url: &str,
    fields: &[(&str, &str)],
    signal: Option<&AbortSignal>,
) -> Result<JsonValue, Thrown> {
    let form = {
        let mut serializer = url::form_urlencoded::Serializer::new(String::new());
        for (name, value) in fields {
            serializer.append_pair(name, value);
        }
        serializer.finish()
    };
    let request = HTTP_CLIENT
        .post(url)
        .header("content-type", "application/x-www-form-urlencoded")
        .body(form);
    let (status, text) = send_buffered(request, signal).await?;
    let body = json_parse(&text).ok();
    if !(200..300).contains(&status) {
        let detail = body.as_ref().and_then(|body| {
            let code = string_field(body, "error")?;
            Some(match string_field(body, "error_description") {
                Some(description) => format!("{code}: {description}"),
                None => code.to_owned(),
            })
        });
        let message = detail.unwrap_or_else(|| format!("Request failed with status code {status}"));
        return Err(ErrorObject {
            status: Some(Some(JsonValue::from(status))),
            ..ErrorObject::named("GaxiosError", message)
        }
        .thrown());
    }
    body.ok_or_else(|| error(format!("Invalid token endpoint response: {text}")))
}

async fn send_buffered(
    request: reqwest::RequestBuilder,
    signal: Option<&AbortSignal>,
) -> Result<(u16, String), Thrown> {
    let exchange = async {
        let response = request
            .send()
            .await
            .map_err(|_| ErrorObject::named("TypeError", "fetch failed").thrown())?;
        let status = response.status().as_u16();
        let text = response
            .text()
            .await
            .map_err(|_| ErrorObject::named("TypeError", "terminated").thrown())?;
        Ok((status, text))
    };
    match signal {
        Some(signal) => tokio::select! {
            biased;
            reason = signal.cancelled() => Err(reason),
            result = exchange => result,
        },
        None => exchange.await,
    }
}

fn metadata_base() -> String {
    let host = process_env("GCE_METADATA_HOST")
        .or_else(|| process_env("GCE_METADATA_IP"))
        .unwrap_or_else(|| "169.254.169.254".to_owned());
    format!("http://{host}/computeMetadata/v1")
}

/// `gcpMetadata.getGCPResidency() || await gcpMetadata.isAvailable()`.
async fn is_gce(signal: Option<&AbortSignal>) -> bool {
    let serverless = ["CLOUD_RUN_JOB", "FUNCTION_NAME", "K_SERVICE"]
        .iter()
        .any(|name| process_env(name).is_some());
    let google_bios = std::fs::read_to_string("/sys/class/dmi/id/bios_vendor")
        .is_ok_and(|vendor| vendor.contains("Google"));
    if serverless || google_bios {
        return true;
    }
    let probe = HTTP_CLIENT
        .get(format!("{}/instance", metadata_base()))
        .header("Metadata-Flavor", "Google")
        .timeout(METADATA_PROBE_TIMEOUT)
        .send();
    let available = async {
        probe.await.is_ok_and(|response| {
            response
                .headers()
                .get("metadata-flavor")
                .is_some_and(|flavor| flavor == "Google")
        })
    };
    match signal {
        Some(signal) => tokio::select! {
            biased;
            _ = signal.cancelled() => false,
            available = available => available,
        },
        None => available.await,
    }
}

/// The `Compute` client: the default service account's token from the
/// metadata server.
async fn compute_credential(signal: Option<&AbortSignal>) -> Result<AccessCredential, Thrown> {
    let request = HTTP_CLIENT
        .get(format!(
            "{}/instance/service-accounts/default/token?scopes={REQUIRED_VERTEX_AI_SCOPE}",
            metadata_base()
        ))
        .header("Metadata-Flavor", "Google");
    let (status, text) = send_buffered(request, signal).await?;
    if !(200..300).contains(&status) {
        return Err(error(format!(
            "Could not refresh access token: Unsuccessful response status code. Request failed with status code {status}"
        )));
    }
    let tokens = json_parse(&text)
        .map_err(|parse_error| ErrorObject::named("SyntaxError", parse_error.message).thrown())?;
    Ok(AccessCredential {
        access_token: access_token(&tokens)?,
        quota_project_id: None,
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn api_key_header_is_added_once() {
        let auth = NodeAuth::new(Some("key".to_owned()), None);
        let mut headers = vec![("content-type".to_owned(), "application/json".to_owned())];
        let runtime = tokio::runtime::Builder::new_current_thread()
            .build()
            .unwrap();
        runtime
            .block_on(auth.add_auth_headers(&mut headers, "https://x", None))
            .unwrap();
        runtime
            .block_on(auth.add_auth_headers(&mut headers, "https://x", None))
            .unwrap();
        assert_eq!(
            headers,
            vec![
                ("content-type".to_owned(), "application/json".to_owned()),
                ("x-goog-api-key".to_owned(), "key".to_owned()),
            ]
        );
    }

    #[test]
    fn ephemeral_tokens_are_rejected() {
        let auth = NodeAuth::new(Some("auth_tokens/abc".to_owned()), None);
        let mut headers = Vec::new();
        let runtime = tokio::runtime::Builder::new_current_thread()
            .build()
            .unwrap();
        let error = runtime
            .block_on(auth.add_auth_headers(&mut headers, "https://x", None))
            .unwrap_err();
        assert_eq!(
            error.to_string(),
            "Ephemeral tokens are only supported by the live API."
        );
    }

    #[test]
    fn missing_key_file_reports_enoent() {
        let runtime = tokio::runtime::Builder::new_current_thread()
            .build()
            .unwrap();
        let options = GoogleAuthOptions {
            key_filename: "/nonexistent/eukhe-google-key.json".to_owned(),
        };
        let error = runtime
            .block_on(get_client(Some(&options), None))
            .unwrap_err();
        assert_eq!(
            error.to_string(),
            "ENOENT: no such file or directory, open '/nonexistent/eukhe-google-key.json'"
        );
    }

    #[test]
    fn credential_files_require_their_fields() {
        let runtime = tokio::runtime::Builder::new_current_thread()
            .build()
            .unwrap();
        let error = runtime
            .block_on(credential_from_json(
                &json!({ "type": "authorized_user" }),
                None,
            ))
            .unwrap_err();
        assert_eq!(
            error.to_string(),
            "The incoming JSON object does not contain a client_id field"
        );
        let error = runtime
            .block_on(credential_from_json(
                &json!({ "type": "service_account" }),
                None,
            ))
            .unwrap_err();
        assert_eq!(
            error.to_string(),
            "The incoming JSON object does not contain a client_email field"
        );
    }

    #[test]
    fn quota_project_becomes_user_project_header() {
        let credential = AccessCredential {
            access_token: "token".to_owned(),
            quota_project_id: Some("billing".to_owned()),
        };
        assert_eq!(
            credential.request_headers(),
            vec![
                ("authorization".to_owned(), "Bearer token".to_owned()),
                ("x-goog-user-project".to_owned(), "billing".to_owned()),
            ]
        );
    }
}
