//! The request path of the `@google/genai` npm SDK (v2.21.0) that the
//! Google wire APIs use (`new GoogleGenAI(options)` followed by
//! `client.models.generateContentStream(params)`): client option resolution
//! (Gemini API vs Vertex AI, express mode, base URLs and API versions),
//! header assembly, authentication (API key or Application Default
//! Credentials), the request-body transforms, `ApiError` construction for
//! non-2xx responses, and the server-sent-event stream decoding.
//!
//! Not a TS module of pi-ai: pi-ai links the SDK. SDK features pi-ai never
//! reaches (automatic function calling with callable tools, MCP tools,
//! retry options, request timeouts, file uploads, live/websocket APIs) are
//! not reproduced.

mod auth;
mod response;
mod transform;

use std::sync::LazyLock;

use eukhe_chord::context::AbortSignal;
#[cfg(test)]
use eukhe_types::pi_ai::JsonObject;
use eukhe_types::pi_ai::{IndexMap, JsonValue};
#[cfg(test)]
use serde_json::json;

use crate::utils::diagnostics::{ErrorObject, Thrown};

pub(crate) use auth::GoogleAuthOptions;
use auth::NodeAuth;
pub(crate) use response::GenerateContentStream;

/// `SDK_VERSION` of the pinned `@google/genai` package.
pub(crate) const SDK_VERSION: &str = "2.21.0";

/// `process.version` of the Node runtime the TS reference runs on. The
/// Rust port has no Node runtime; the SDK's `gl-node/<version>` client label
/// keeps the reference runtime's value.
const NODE_VERSION: &str = "v26.10.0";

const VERTEX_AI_API_DEFAULT_VERSION: &str = "v1beta1";
const GOOGLE_AI_API_DEFAULT_VERSION: &str = "v1beta";

static HTTP_CLIENT: LazyLock<reqwest::Client> = LazyLock::new(reqwest::Client::new);

/// SDK `ResourceScope`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum ResourceScope {
    /// The base URL already addresses the collection: no
    /// `projects/<p>/locations/<l>` prefix is added.
    Collection,
}

impl ResourceScope {
    #[cfg(test)]
    const fn as_str(self) -> &'static str {
        match self {
            Self::Collection => "COLLECTION",
        }
    }
}

/// SDK `HttpOptions` (the fields pi-ai sets).
#[derive(Debug, Clone, Default, PartialEq)]
pub(crate) struct HttpOptions {
    pub base_url: Option<String>,
    pub base_url_resource_scope: Option<ResourceScope>,
    pub api_version: Option<String>,
    pub headers: Option<IndexMap<String, String>>,
}

impl HttpOptions {
    /// Whether no field is set (`Object.keys(httpOptions).length === 0`).
    pub(crate) fn is_empty(&self) -> bool {
        self.base_url.is_none()
            && self.base_url_resource_scope.is_none()
            && self.api_version.is_none()
            && self.headers.is_none()
    }

    #[cfg(test)]
    fn to_json(&self) -> JsonValue {
        let mut object = JsonObject::new();
        if let Some(base_url) = &self.base_url {
            object.insert("baseUrl".into(), base_url.clone().into());
        }
        if let Some(scope) = self.base_url_resource_scope {
            object.insert("baseUrlResourceScope".into(), scope.as_str().into());
        }
        if let Some(api_version) = &self.api_version {
            object.insert("apiVersion".into(), api_version.clone().into());
        }
        if let Some(headers) = &self.headers {
            object.insert(
                "headers".into(),
                JsonValue::Object(
                    headers
                        .iter()
                        .map(|(name, value)| (name.clone(), value.clone().into()))
                        .collect(),
                ),
            );
        }
        JsonValue::Object(object)
    }
}

/// SDK `GoogleGenAIOptions` (the fields pi-ai sets).
#[derive(Debug, Clone, Default, PartialEq)]
pub(crate) struct GoogleGenAiOptions {
    pub vertexai: bool,
    pub api_key: Option<String>,
    pub project: Option<String>,
    pub location: Option<String>,
    pub api_version: Option<String>,
    pub google_auth_options: Option<GoogleAuthOptions>,
    pub http_options: Option<HttpOptions>,
}

impl GoogleGenAiOptions {
    /// The constructor argument as the JS object the TS adapters build (what
    /// the mocked SDK records).
    #[cfg(test)]
    pub(crate) fn to_json(&self) -> JsonValue {
        let mut object = JsonObject::new();
        if self.vertexai {
            object.insert("vertexai".into(), true.into());
        }
        if let Some(api_key) = &self.api_key {
            object.insert("apiKey".into(), api_key.clone().into());
        }
        if let Some(project) = &self.project {
            object.insert("project".into(), project.clone().into());
        }
        if let Some(location) = &self.location {
            object.insert("location".into(), location.clone().into());
        }
        if let Some(api_version) = &self.api_version {
            object.insert("apiVersion".into(), api_version.clone().into());
        }
        if let Some(auth) = &self.google_auth_options {
            object.insert(
                "googleAuthOptions".into(),
                json!({ "keyFilename": auth.key_filename }),
            );
        }
        if let Some(http_options) = &self.http_options {
            object.insert("httpOptions".into(), http_options.to_json());
        }
        JsonValue::Object(object)
    }
}

/// `getEnv(name)`: the trimmed process environment value.
fn get_env(name: &str) -> Option<String> {
    std::env::var(name)
        .ok()
        .map(|value| value.trim().to_owned())
}

/// JS truthiness of an optional string.
fn truthy(value: Option<&String>) -> bool {
    value.is_some_and(|value| !value.is_empty())
}

/// `getApiKeyFromEnv()`.
fn get_api_key_from_env() -> Option<String> {
    let google = get_env("GOOGLE_API_KEY").filter(|key| !key.is_empty());
    let gemini = get_env("GEMINI_API_KEY").filter(|key| !key.is_empty());
    google.or(gemini)
}

/// The resolved `ApiClient` HTTP options.
#[derive(Debug, Clone, PartialEq)]
struct ClientHttpOptions {
    base_url: String,
    api_version: String,
    base_url_resource_scope: Option<ResourceScope>,
    /// `httpOptions.headers` in object-key order.
    headers: IndexMap<String, String>,
}

/// The resolved `apiKey` / `project` / `location` of a client.
struct Credentials {
    api_key: Option<String>,
    project: Option<String>,
    location: Option<String>,
}

impl Credentials {
    /// The `GoogleGenAI` constructor's precedence rules between explicit
    /// options and the `GOOGLE_API_KEY`/`GEMINI_API_KEY`,
    /// `GOOGLE_CLOUD_PROJECT`, and `GOOGLE_CLOUD_LOCATION` environment.
    fn resolve(options: &GoogleGenAiOptions) -> Self {
        let env_api_key = get_api_key_from_env();
        let env_project = get_env("GOOGLE_CLOUD_PROJECT");
        let env_location = get_env("GOOGLE_CLOUD_LOCATION");
        let env_project_or_location = truthy(env_project.as_ref()) || truthy(env_location.as_ref());
        let mut credentials = Self {
            api_key: options.api_key.clone().or_else(|| env_api_key.clone()),
            project: options.project.clone().or(env_project),
            location: options.location.clone().or(env_location),
        };
        if !options.vertexai {
            return credentials;
        }
        let explicit_project_or_location =
            truthy(options.project.as_ref()) || truthy(options.location.as_ref());
        let explicit_api_key = truthy(options.api_key.as_ref());
        if !explicit_project_or_location && env_project_or_location && explicit_api_key {
            // Explicit api_key takes precedence over implicit project/location.
            credentials.project = None;
            credentials.location = None;
        } else if (explicit_project_or_location && !explicit_api_key && env_api_key.is_some())
            || (!explicit_project_or_location
                && !explicit_api_key
                && env_project_or_location
                && env_api_key.is_some())
        {
            // Explicit project/location takes precedence over implicit
            // api_key; implicit project/location over implicit api_key.
            credentials.api_key = None;
        }
        if !truthy(credentials.location.as_ref()) && !truthy(credentials.api_key.as_ref()) {
            credentials.location = Some("global".to_owned());
        }
        credentials
    }

    /// The Vertex AI part of the `ApiClient` constructor: the default base
    /// URL, clearing project/location for a bare custom base URL.
    fn vertex_base_url(
        &mut self,
        custom_base_url: Option<String>,
    ) -> Result<Option<String>, Thrown> {
        if !truthy(self.location.as_ref())
            && !truthy(self.api_key.as_ref())
            && custom_base_url.is_none()
        {
            self.location = Some("global".to_owned());
        }
        let project_and_location = truthy(self.project.as_ref()) && truthy(self.location.as_ref());
        let has_auth = project_and_location || truthy(self.api_key.as_ref());
        if !has_auth && custom_base_url.is_none() {
            return Err(ErrorObject::new(
                "Authentication is not set up. Please provide either a project and location, or an API key, or a custom base URL.",
            )
            .thrown());
        }
        if custom_base_url.is_some() && !has_auth {
            self.project = None;
            self.location = None;
            return Ok(custom_base_url);
        }
        let location = self.location.as_deref().unwrap_or_default();
        Ok(
            if (truthy(self.api_key.as_ref()) && !truthy(self.project.as_ref()))
                || location == "global"
            {
                // Vertex Express or global endpoint case.
                Some("https://aiplatform.googleapis.com/".to_owned())
            } else if project_and_location && (location == "us" || location == "eu") {
                Some(format!("https://aiplatform.{location}.rep.googleapis.com/"))
            } else if project_and_location {
                Some(format!("https://{location}-aiplatform.googleapis.com/"))
            } else {
                None
            },
        )
    }
}

/// The default headers patched with the user's `httpOptions`
/// (`patchHttpOptions(initHttpOptions, options.httpOptions)`).
fn patch_http_options(
    base_url: Option<String>,
    api_version: String,
    user: Option<HttpOptions>,
) -> Result<ClientHttpOptions, Thrown> {
    let version_header = format!("google-genai-sdk/{SDK_VERSION} gl-node/{NODE_VERSION}");
    let mut headers = IndexMap::new();
    headers.insert("User-Agent".to_owned(), version_header.clone());
    headers.insert("x-goog-api-client".to_owned(), version_header);
    headers.insert("Content-Type".to_owned(), "application/json".to_owned());
    let mut base_url = base_url;
    let mut api_version = api_version;
    let mut base_url_resource_scope = None;
    if let Some(user) = user {
        if let Some(user_base_url) = user.base_url {
            base_url = Some(user_base_url);
        }
        if let Some(user_api_version) = user.api_version {
            api_version = user_api_version;
        }
        base_url_resource_scope = user.base_url_resource_scope;
        if let Some(user_headers) = user.headers {
            headers.extend(user_headers);
        }
    }
    let Some(base_url) = base_url else {
        return Err(ErrorObject::new("HTTP options are not correctly set.").thrown());
    };
    Ok(ClientHttpOptions {
        base_url,
        api_version,
        base_url_resource_scope,
        headers,
    })
}

/// A `GoogleGenAI` client: the resolved `ApiClient` state plus its auth.
pub(crate) struct GoogleGenAi {
    vertexai: bool,
    project: Option<String>,
    location: Option<String>,
    http_options: ClientHttpOptions,
    auth: NodeAuth,
}

impl GoogleGenAi {
    /// `new GoogleGenAI(options)` (Node build).
    ///
    /// # Errors
    ///
    /// The SDK constructor errors: project/location on the Gemini API
    /// backend, or no usable Vertex AI authentication.
    pub(crate) fn new(options: GoogleGenAiOptions) -> Result<Self, Thrown> {
        #[cfg(test)]
        mock::record_constructor_call(&options);

        let vertexai = options.vertexai;
        if (truthy(options.project.as_ref()) || truthy(options.location.as_ref())) && !vertexai {
            return Err(ErrorObject::new(
                "Project and location are not supported for Gemini API backend.",
            )
            .thrown());
        }
        let mut credentials = Credentials::resolve(&options);

        let GoogleGenAiOptions {
            api_version,
            google_auth_options,
            http_options,
            ..
        } = options;
        let mut user_http_options = http_options;
        let env_base_url = if vertexai {
            get_env("GOOGLE_VERTEX_BASE_URL")
        } else {
            get_env("GOOGLE_GEMINI_BASE_URL")
        };
        let configured_base_url = user_http_options
            .as_ref()
            .and_then(|http| http.base_url.clone())
            .filter(|base_url| !base_url.is_empty());
        if let Some(base_url) = configured_base_url
            .or(env_base_url)
            .filter(|base_url| !base_url.is_empty())
        {
            user_http_options
                .get_or_insert_with(HttpOptions::default)
                .base_url = Some(base_url);
        }
        let custom_base_url = user_http_options
            .as_ref()
            .and_then(|http| http.base_url.clone());
        let (init_base_url, init_api_version) = if vertexai {
            (
                credentials.vertex_base_url(custom_base_url)?,
                api_version.unwrap_or_else(|| VERTEX_AI_API_DEFAULT_VERSION.to_owned()),
            )
        } else {
            (
                Some("https://generativelanguage.googleapis.com/".to_owned()),
                api_version.unwrap_or_else(|| GOOGLE_AI_API_DEFAULT_VERSION.to_owned()),
            )
        };
        let http_options = patch_http_options(init_base_url, init_api_version, user_http_options)?;
        let Credentials {
            api_key,
            project,
            location,
        } = credentials;
        Ok(Self {
            vertexai,
            project,
            location,
            http_options,
            auth: NodeAuth::new(api_key, google_auth_options),
        })
    }

    /// `getRequestUrlInternal` + `constructUrl` for a request path.
    fn construct_url(&self, path: &str) -> Result<url::Url, Thrown> {
        let http = &self.http_options;
        let base_url = http.base_url.strip_suffix('/').unwrap_or(&http.base_url);
        let mut elements = vec![base_url.to_owned()];
        if !http.api_version.is_empty() {
            elements.push(http.api_version.clone());
        }
        if self.should_prepend_vertex_project_path(path) {
            elements.push(format!(
                "projects/{}/locations/{}",
                self.project.as_deref().unwrap_or("undefined"),
                self.location.as_deref().unwrap_or("undefined")
            ));
        }
        if !path.is_empty() {
            elements.push(path.to_owned());
        }
        let joined = elements.join("/");
        url::Url::parse(&joined)
            .map_err(|_| ErrorObject::named("TypeError", "Invalid URL").thrown())
    }

    /// `shouldPrependVertexProjectPath` for a POST request.
    fn should_prepend_vertex_project_path(&self, path: &str) -> bool {
        if self.http_options.base_url_resource_scope == Some(ResourceScope::Collection) {
            return false;
        }
        if !self.vertexai {
            return false;
        }
        if !truthy(self.project.as_ref()) || !truthy(self.location.as_ref()) {
            return false;
        }
        !path.starts_with("projects/")
    }

    /// `getHeadersInternal`: `httpOptions.headers` appended into a `Headers`
    /// (case-insensitive; repeated names combine with `", "`), then the auth
    /// headers.
    async fn request_headers(
        &self,
        url: &str,
        signal: Option<&AbortSignal>,
    ) -> Result<Vec<(String, String)>, Thrown> {
        let mut headers: Vec<(String, String)> = Vec::new();
        for (name, value) in &self.http_options.headers {
            append_header(&mut headers, name, value);
        }
        self.auth
            .add_auth_headers(&mut headers, url, signal)
            .await?;
        Ok(headers)
    }

    /// `client.models.generateContentStream(params)`: resolves once the
    /// response headers arrive and the status is OK.
    ///
    /// # Errors
    ///
    /// Parameter-transform errors, auth errors, network errors (`TypeError:
    /// fetch failed`), the abort reason, and `ApiError` for non-2xx responses.
    pub(crate) async fn generate_content_stream(
        &self,
        params: &JsonValue,
        signal: Option<&AbortSignal>,
    ) -> Result<GenerateContentStream, Thrown> {
        #[cfg(test)]
        if let Some(chunks) = mock::stream_chunks() {
            return Ok(GenerateContentStream::from_chunks(chunks));
        }

        let request = if self.vertexai {
            transform::generate_content_parameters_to_vertex(params)?
        } else {
            transform::generate_content_parameters_to_mldev(params)?
        };
        let path = format!("{}:streamGenerateContent?alt=sse", request.model);
        let url = self.construct_url(&path)?;
        let headers = self.request_headers(url.as_str(), signal).await?;
        let body = crate::utils::js::json_stringify(&JsonValue::Object(request.body));
        response::stream_api_call(&HTTP_CLIENT, url, headers, body, signal, self.vertexai).await
    }
}

/// `Headers.append(name, value)` on an ordered header list.
fn append_header(headers: &mut Vec<(String, String)>, name: &str, value: &str) {
    let lowered = name.to_lowercase();
    match headers
        .iter_mut()
        .find(|(existing, _)| *existing == lowered)
    {
        Some((_, existing)) => {
            existing.push_str(", ");
            existing.push_str(value);
        }
        None => headers.push((lowered, value.to_owned())),
    }
}

/// `headers.get(name) !== null` on an ordered header list.
fn has_header(headers: &[(String, String)], name: &str) -> bool {
    let lowered = name.to_lowercase();
    headers.iter().any(|(existing, _)| *existing == lowered)
}

#[cfg(test)]
pub(crate) mod mock {
    //! The mocked `@google/genai` module (TS `vi.mock("@google/genai")`):
    //! records `GoogleGenAI` constructor calls and answers
    //! `generateContentStream` with canned chunks. Installing the mock takes
    //! a process-wide test lock, so mock-using tests run one at a time.

    use std::sync::{Arc, LazyLock, Mutex, PoisonError};

    use eukhe_types::pi_ai::JsonValue;

    use super::GoogleGenAiOptions;

    #[derive(Default)]
    struct MockState {
        constructor_calls: Vec<JsonValue>,
        chunks: Vec<JsonValue>,
    }

    type SharedState = Arc<Mutex<MockState>>;

    static MOCK: Mutex<Option<SharedState>> = Mutex::new(None);
    static SERIAL: LazyLock<Arc<tokio::sync::Mutex<()>>> =
        LazyLock::new(|| Arc::new(tokio::sync::Mutex::new(())));

    fn current() -> Option<SharedState> {
        MOCK.lock().unwrap_or_else(PoisonError::into_inner).clone()
    }

    pub(super) fn record_constructor_call(options: &GoogleGenAiOptions) {
        if let Some(state) = current() {
            state
                .lock()
                .unwrap_or_else(PoisonError::into_inner)
                .constructor_calls
                .push(options.to_json());
        }
    }

    pub(super) fn stream_chunks() -> Option<Vec<JsonValue>> {
        current().map(|state| {
            state
                .lock()
                .unwrap_or_else(PoisonError::into_inner)
                .chunks
                .clone()
        })
    }

    /// Holds the test lock and the installed mock; removes it when dropped.
    pub(crate) struct GoogleGenAiMock {
        state: SharedState,
        _serial: tokio::sync::OwnedMutexGuard<()>,
    }

    impl GoogleGenAiMock {
        /// The recorded constructor arguments.
        pub(crate) fn constructor_calls(&self) -> Vec<JsonValue> {
            self.state
                .lock()
                .unwrap_or_else(PoisonError::into_inner)
                .constructor_calls
                .clone()
        }
    }

    impl Drop for GoogleGenAiMock {
        fn drop(&mut self) {
            *MOCK.lock().unwrap_or_else(PoisonError::into_inner) = None;
        }
    }

    /// Take the test lock without mocking the SDK (tests that drive the real
    /// client against a local server).
    pub(crate) async fn serial() -> tokio::sync::OwnedMutexGuard<()> {
        Arc::clone(&SERIAL).lock_owned().await
    }

    /// Mock the SDK with `chunks` until the guard drops.
    pub(crate) async fn install(chunks: Vec<JsonValue>) -> GoogleGenAiMock {
        let serial = serial().await;
        let state: SharedState = Arc::new(Mutex::new(MockState {
            constructor_calls: Vec::new(),
            chunks,
        }));
        *MOCK.lock().unwrap_or_else(PoisonError::into_inner) = Some(Arc::clone(&state));
        GoogleGenAiMock {
            state,
            _serial: serial,
        }
    }
}
