//! Tests of the default credential and region providers: shared-file parsing,
//! profile selection, every chain link against local mock servers, and the
//! terminal errors (expected values verified against the JS SDK).

use std::collections::HashMap;
use std::fmt::Write as _;
use std::sync::{Arc, Mutex, PoisonError};

use base64::Engine as _;
use eukhe_chord::context::AbortController;
use tokio::io::{AsyncReadExt, AsyncWriteExt};
use tokio::net::TcpListener;

use super::js_compat::{js_date_parse, parse_rfc3339_date_time, to_iso_string};
use super::shared_ini::{get_config_data, merge_config_files, parse_ini, IniFile, IniSection};
use super::shared_ini::{InvalidProfileName, SharedConfigFiles};
use super::{default_provider, default_region, CallerClientConfig, CredentialEnv, SdkProcessState};
use crate::api::bedrock_converse_stream::client_config::{AwsCredentials, BedrockRequestHandler};
use crate::utils::diagnostics::{error_name, ErrorObject, Thrown};

/// One canned HTTP response.
#[derive(Clone)]
struct MockResponse {
    status: u16,
    headers: Vec<(&'static str, &'static str)>,
    body: String,
}

fn reply(status: u16, body: &str) -> MockResponse {
    MockResponse {
        status,
        headers: Vec::new(),
        body: body.to_owned(),
    }
}

/// One request the mock server received.
#[derive(Debug, Clone)]
struct RecordedRequest {
    method: String,
    target: String,
    headers: HashMap<String, String>,
    body: String,
}

/// A local HTTP/1.1 server answering requests with `responses` in order
/// (the last one repeats).
struct MockServer {
    base_url: String,
    requests: Arc<Mutex<Vec<RecordedRequest>>>,
}

impl MockServer {
    async fn start(responses: Vec<MockResponse>) -> Self {
        let listener = TcpListener::bind("127.0.0.1:0")
            .await
            .expect("bind mock server");
        let address = listener.local_addr().expect("mock server address");
        let requests = Arc::new(Mutex::new(Vec::new()));
        let recorded = Arc::clone(&requests);
        tokio::spawn(async move {
            let mut index = 0;
            while let Ok((mut socket, _)) = listener.accept().await {
                let Some(request) = read_request(&mut socket).await else {
                    continue;
                };
                recorded
                    .lock()
                    .unwrap_or_else(PoisonError::into_inner)
                    .push(request);
                let response = &responses[index.min(responses.len() - 1)];
                index += 1;
                let mut head = format!(
                    "HTTP/1.1 {} Mock\r\ncontent-length: {}\r\nconnection: close\r\n",
                    response.status,
                    response.body.len()
                );
                for (name, value) in &response.headers {
                    let _ = write!(head, "{name}: {value}\r\n");
                }
                head.push_str("\r\n");
                let _ = socket.write_all(head.as_bytes()).await;
                let _ = socket.write_all(response.body.as_bytes()).await;
                let _ = socket.shutdown().await;
            }
        });
        Self {
            base_url: format!("http://{address}"),
            requests,
        }
    }

    fn requests(&self) -> Vec<RecordedRequest> {
        self.requests
            .lock()
            .unwrap_or_else(PoisonError::into_inner)
            .clone()
    }
}

async fn read_request(socket: &mut tokio::net::TcpStream) -> Option<RecordedRequest> {
    let mut buffer = Vec::new();
    let mut chunk = [0_u8; 4096];
    let head_end = loop {
        let read = socket.read(&mut chunk).await.ok()?;
        if read == 0 {
            return None;
        }
        buffer.extend_from_slice(&chunk[..read]);
        if let Some(position) = buffer.windows(4).position(|window| window == b"\r\n\r\n") {
            break position;
        }
    };
    let head = String::from_utf8_lossy(&buffer[..head_end]).into_owned();
    let mut lines = head.split("\r\n");
    let mut request_line = lines.next()?.split(' ');
    let method = request_line.next()?.to_owned();
    let target = request_line.next()?.to_owned();
    let headers: HashMap<String, String> = lines
        .filter_map(|line| line.split_once(':'))
        .map(|(name, value)| (name.trim().to_ascii_lowercase(), value.trim().to_owned()))
        .collect();
    let length: usize = headers
        .get("content-length")
        .and_then(|value| value.parse().ok())
        .unwrap_or(0);
    let mut body = buffer[head_end + 4..].to_vec();
    while body.len() < length {
        let read = socket.read(&mut chunk).await.ok()?;
        if read == 0 {
            break;
        }
        body.extend_from_slice(&chunk[..read]);
    }
    Some(RecordedRequest {
        method,
        target,
        headers,
        body: String::from_utf8_lossy(&body).into_owned(),
    })
}

/// An isolated environment: variables, a temp home with `.aws` files, and
/// fresh process state.
struct TestEnv {
    vars: HashMap<String, String>,
    home: tempfile::TempDir,
    state: SdkProcessState,
}

impl TestEnv {
    fn new() -> Self {
        let home = tempfile::tempdir().expect("temp home");
        let mut vars = HashMap::new();
        vars.insert(
            "HOME".to_owned(),
            home.path().to_string_lossy().into_owned(),
        );
        // No test may reach the real metadata service.
        vars.insert("AWS_EC2_METADATA_DISABLED".to_owned(), "true".to_owned());
        Self {
            vars,
            home,
            state: SdkProcessState::default(),
        }
    }

    fn set(&mut self, name: &str, value: &str) -> &mut Self {
        self.vars.insert(name.to_owned(), value.to_owned());
        self
    }

    fn remove(&mut self, name: &str) -> &mut Self {
        self.vars.remove(name);
        self
    }

    fn path(&self, relative: &str) -> String {
        self.home
            .path()
            .join(relative)
            .to_string_lossy()
            .into_owned()
    }

    fn write(&self, relative: &str, contents: &str) -> String {
        let path = self.home.path().join(relative);
        std::fs::create_dir_all(path.parent().expect("parent")).expect("create dirs");
        std::fs::write(&path, contents).expect("write file");
        path.to_string_lossy().into_owned()
    }

    fn config(&self, contents: &str) {
        self.write(".aws/config", contents);
    }

    fn credentials(&self, contents: &str) {
        self.write(".aws/credentials", contents);
    }

    async fn resolve_with(
        &self,
        profile: Option<&str>,
        handler: &BedrockRequestHandler,
        signal: Option<&eukhe_chord::context::AbortSignal>,
    ) -> Result<AwsCredentials, Thrown> {
        let vars = &self.vars;
        let var = move |name: &str| vars.get(name).cloned();
        let env = CredentialEnv {
            var: &var,
            os_home_dir: None,
            state: &self.state,
        };
        let caller = CallerClientConfig {
            profile,
            region: "us-west-2",
            request_handler: handler,
        };
        default_provider(&env, caller, signal).await
    }

    async fn resolve(&self, profile: Option<&str>) -> Result<AwsCredentials, Thrown> {
        self.resolve_with(profile, &BedrockRequestHandler::Default, None)
            .await
    }

    async fn region(&self, profile: Option<&str>) -> Result<String, Thrown> {
        let vars = &self.vars;
        let var = move |name: &str| vars.get(name).cloned();
        let env = CredentialEnv {
            var: &var,
            os_home_dir: None,
            state: &self.state,
        };
        default_region(&env, profile, None).await
    }
}

fn keys(access: &str, secret: &str, token: Option<&str>) -> AwsCredentials {
    AwsCredentials {
        access_key_id: access.to_owned(),
        secret_access_key: secret.to_owned(),
        session_token: token.map(str::to_owned),
    }
}

/// `(name, message)` of a thrown error.
fn described(error: &Thrown) -> (String, String) {
    (error_name(error.as_ref()), error.to_string())
}

fn final_error() -> (String, String) {
    (
        "CredentialsProviderError".to_owned(),
        "Could not load credentials from any providers".to_owned(),
    )
}

const STS_SUCCESS: &str = "<AssumeRoleResponse xmlns=\"https://sts.amazonaws.com/doc/2011-06-15/\"><AssumeRoleResult><Credentials><AccessKeyId>ASIAX</AccessKeyId><SecretAccessKey>sec&amp;ret</SecretAccessKey><SessionToken>tok</SessionToken><Expiration>2030-01-01T00:00:00Z</Expiration></Credentials><AssumedRoleUser><Arn>arn:aws:sts::123456789012:assumed-role/Dev/x</Arn></AssumedRoleUser></AssumeRoleResult></AssumeRoleResponse>";

#[test]
fn parse_ini_handles_comments_sub_sections_and_prefixes() {
    let text = "# comment\n[default]\nregion = us-east-1 ; trailing comment\naws_access_key_id=AKID#notcomment\n\n[profile dev]\ns3 =\n  max_concurrent_requests = 10\nrole_arn = arn\n[sso-session my]\nsso_region = eu-west-1\n[services svc]\nsts =\n  endpoint_url = http://x\n[weird name]\nkey = v\n[profile \"quoted\"]\na = b\n[profile default]\nregion = eu-west-2\n[2]\nz = 1\n[empty]\n";
    let parsed = parse_ini(text).expect("parses");
    assert_eq!(
        parsed,
        IniFile::from_sections(vec![
            (
                "default",
                IniSection::from_pairs(&[
                    ("region", "us-east-1"),
                    ("aws_access_key_id", "AKID#notcomment"),
                ]),
            ),
            (
                "profile.dev",
                IniSection::from_pairs(&[
                    ("s3.max_concurrent_requests", "10"),
                    ("role_arn", "arn")
                ]),
            ),
            (
                "sso-session.my",
                IniSection::from_pairs(&[("sso_region", "eu-west-1")])
            ),
            (
                "services.svc",
                IniSection::from_pairs(&[("sts.endpoint_url", "http://x")])
            ),
            ("profile.quoted", IniSection::from_pairs(&[("a", "b")])),
            (
                "profile.default",
                IniSection::from_pairs(&[("region", "eu-west-2")])
            ),
            ("2", IniSection::from_pairs(&[("z", "1")])),
        ])
    );
    // Same result as the SDK's loadSharedConfigFiles for this file.
    assert_eq!(
        get_config_data(&parsed),
        IniFile::from_sections(vec![
            (
                "default",
                IniSection::from_pairs(&[("region", "eu-west-2")])
            ),
            (
                "dev",
                IniSection::from_pairs(&[
                    ("s3.max_concurrent_requests", "10"),
                    ("role_arn", "arn")
                ]),
            ),
            (
                "sso-session.my",
                IniSection::from_pairs(&[("sso_region", "eu-west-1")])
            ),
            (
                "services.svc",
                IniSection::from_pairs(&[("sts.endpoint_url", "http://x")])
            ),
            ("quoted", IniSection::from_pairs(&[("a", "b")])),
        ])
    );
}

#[test]
fn parse_ini_rejects_proto_sections() {
    assert_eq!(
        parse_ini("[profile __proto__]\na = b\n"),
        Err(InvalidProfileName(
            "Found invalid profile name \"profile __proto__\"".to_owned()
        ))
    );
}

#[test]
fn merge_config_files_prefers_credentials_values() {
    let files = SharedConfigFiles {
        config_file: IniFile::from_sections(vec![(
            "dev",
            IniSection::from_pairs(&[("region", "eu-west-1"), ("role_arn", "arn")]),
        )]),
        credentials_file: IniFile::from_sections(vec![
            (
                "dev",
                IniSection::from_pairs(&[("role_arn", "override"), ("extra", "1")]),
            ),
            ("other", IniSection::from_pairs(&[("a", "b")])),
        ]),
    };
    assert_eq!(
        merge_config_files(&files),
        IniFile::from_sections(vec![
            (
                "dev",
                IniSection::from_pairs(&[
                    ("region", "eu-west-1"),
                    ("role_arn", "override"),
                    ("extra", "1"),
                ]),
            ),
            ("other", IniSection::from_pairs(&[("a", "b")])),
        ])
    );
}

#[test]
fn js_dates_parse_and_format_like_v8() {
    // Exact JS time values (integral milliseconds) compare bit-for-bit.
    let time = |text: &str| js_date_parse(text).to_bits();
    assert_eq!(
        time("2030-01-01T00:00:00Z"),
        1_893_456_000_000_f64.to_bits()
    );
    assert_eq!(
        time("2030-01-01T01:00:00.5+01:00"),
        1_893_456_000_500_f64.to_bits()
    );
    assert_eq!(time("2030-01-01"), 1_893_456_000_000_f64.to_bits());
    assert!(js_date_parse("not a date").is_nan());
    assert_eq!(
        to_iso_string(1_893_456_000_500.0).expect("valid"),
        "2030-01-01T00:00:00.500Z"
    );
    assert_eq!(
        to_iso_string(f64::NAN),
        Err(ErrorObject::named("RangeError", "Invalid time value"))
    );
    assert_eq!(
        parse_rfc3339_date_time("2030-02-30T00:00:00Z"),
        Err(ErrorObject::named(
            "TypeError",
            "Invalid day for February in 2030: 30"
        ))
    );
    assert_eq!(
        parse_rfc3339_date_time("2030-01-01T00:00:00+01:00"),
        Err(ErrorObject::named(
            "TypeError",
            "Invalid RFC-3339 date-time value"
        ))
    );
}

#[tokio::test]
async fn env_credentials_resolve_without_a_profile() {
    let mut env = TestEnv::new();
    env.set("AWS_ACCESS_KEY_ID", "AKENV")
        .set("AWS_SECRET_ACCESS_KEY", "SKENV")
        .set("AWS_SESSION_TOKEN", "STENV");
    assert_eq!(
        env.resolve(None).await.expect("env credentials"),
        keys("AKENV", "SKENV", Some("STENV"))
    );
}

#[tokio::test]
async fn env_link_is_skipped_when_a_profile_is_set() {
    let mut env = TestEnv::new();
    env.set("AWS_ACCESS_KEY_ID", "AKENV")
        .set("AWS_SECRET_ACCESS_KEY", "SKENV");
    env.credentials("[dev]\naws_access_key_id = AKDEV\naws_secret_access_key = SKDEV\n");
    assert_eq!(
        env.resolve(Some("dev")).await.expect("profile keys"),
        keys("AKDEV", "SKDEV", None)
    );
    env.set("AWS_PROFILE", "dev");
    assert_eq!(
        env.resolve(None).await.expect("AWS_PROFILE keys"),
        keys("AKDEV", "SKDEV", None)
    );
}

#[tokio::test]
async fn profile_name_falls_back_to_aws_profile_then_default() {
    let mut env = TestEnv::new();
    env.config(
        "[default]\naws_access_key_id = AKDEF\naws_secret_access_key = SKDEF\n[profile p2]\naws_access_key_id = AK2\naws_secret_access_key = SK2\naws_session_token = ST2\n",
    );
    assert_eq!(
        env.resolve(None).await.expect("default"),
        keys("AKDEF", "SKDEF", None)
    );
    env.set("AWS_PROFILE", "p2");
    assert_eq!(
        env.resolve(None).await.expect("p2"),
        keys("AK2", "SK2", Some("ST2"))
    );
    env.set("AWS_PROFILE", "");
    assert_eq!(
        env.resolve(None).await.expect("empty"),
        keys("AKDEF", "SKDEF", None)
    );
}

#[tokio::test]
async fn no_source_ends_with_the_sdk_terminal_error() {
    let env = TestEnv::new();
    let error = env.resolve(None).await.expect_err("nothing configured");
    assert_eq!(described(&error), final_error());
}

#[tokio::test]
async fn credential_process_output_is_validated() {
    let env = TestEnv::new();
    env.config(concat!(
        "[profile proc]\n",
        "credential_process = sh -c 'printf \"%s\" \"$0\"' '{\"Version\": 1, \"AccessKeyId\": \"AKP\", \"SecretAccessKey\": \"SKP\", \"SessionToken\": \"STP\", \"Expiration\": \"2999-01-01T00:00:00Z\"}'\n",
        "[profile expired]\n",
        "credential_process = printf '{\"Version\": 1, \"AccessKeyId\": \"A\", \"SecretAccessKey\": \"S\", \"Expiration\": \"2000-01-01T00:00:00Z\"}'\n",
        "[profile badversion]\n",
        "credential_process = printf '{\"Version\": 2}'\n",
    ));
    assert_eq!(
        env.resolve(Some("proc"))
            .await
            .expect("process credentials"),
        keys("AKP", "SKP", Some("STP"))
    );
    for profile in ["expired", "badversion"] {
        let error = env.resolve(Some(profile)).await.expect_err("rejected");
        assert_eq!(described(&error), final_error(), "{profile}");
    }
}

#[tokio::test]
async fn assume_role_signs_with_the_source_profile() {
    let sts = MockServer::start(vec![reply(200, STS_SUCCESS)]).await;
    let mut env = TestEnv::new();
    env.set("AWS_ENDPOINT_URL_STS", &sts.base_url);
    env.config(
        "[profile dev]\nrole_arn = arn:aws:iam::123456789012:role/Dev\nsource_profile = base\nexternal_id = ext id&1\nrole_session_name = s~n.x\nduration_seconds = 900\nregion = eu-central-1\n",
    );
    env.credentials("[base]\naws_access_key_id = AKIDBASE\naws_secret_access_key = SECRETBASE\n");
    assert_eq!(
        env.resolve(Some("dev")).await.expect("assumed"),
        keys("ASIAX", "sec&ret", Some("tok"))
    );
    let requests = sts.requests();
    assert_eq!(requests.len(), 1);
    let request = &requests[0];
    assert_eq!(
        (request.method.as_str(), request.target.as_str()),
        ("POST", "/")
    );
    assert_eq!(
        request.body,
        "Action=AssumeRole&Version=2011-06-15&RoleArn=arn%3Aaws%3Aiam%3A%3A123456789012%3Arole%2FDev&RoleSessionName=s~n.x&DurationSeconds=900&ExternalId=ext%20id%261"
    );
    assert_eq!(
        request.headers.get("content-type").map(String::as_str),
        Some("application/x-www-form-urlencoded")
    );
    assert_eq!(
        request.headers.get("amz-sdk-request").map(String::as_str),
        Some("attempt=1; max=3")
    );
    let authorization = request.headers.get("authorization").expect("signed");
    assert!(
        authorization.starts_with("AWS4-HMAC-SHA256 Credential=AKIDBASE/")
            && authorization.contains("/eu-central-1/sts/aws4_request"),
        "{authorization}"
    );
}

#[tokio::test]
async fn assume_role_defaults_to_the_client_region_and_stops_on_service_errors() {
    let sts = MockServer::start(vec![reply(
        403,
        "<ErrorResponse><Error><Type>Sender</Type><Code>AccessDenied</Code><Message>not authorized &amp; stuff</Message></Error></ErrorResponse>",
    )])
    .await;
    let mut env = TestEnv::new();
    env.set("AWS_ENDPOINT_URL_STS", &sts.base_url);
    env.config("[profile dev]\nrole_arn = arn:aws:iam::1:role/Dev\nsource_profile = base\n[profile base]\naws_access_key_id = AK\naws_secret_access_key = SK\n");
    let error = env.resolve(Some("dev")).await.expect_err("denied");
    assert_eq!(
        described(&error),
        (
            "AccessDenied".to_owned(),
            "not authorized & stuff".to_owned()
        )
    );
    let requests = sts.requests();
    assert_eq!(requests.len(), 1, "client errors are not retried");
    assert!(requests[0].body.contains("RoleSessionName=aws-sdk-js-"));
    assert!(requests[0].body.ends_with("&DurationSeconds=3600"));
    assert!(requests[0]
        .headers
        .get("authorization")
        .is_some_and(|value| value.contains("/us-west-2/sts/aws4_request")));
}

#[tokio::test]
async fn transient_sts_errors_retry_up_to_max_attempts() {
    let sts = MockServer::start(vec![reply(
        500,
        "<ErrorResponse><Error><Code>InternalFailure</Code><Message>boom</Message></Error></ErrorResponse>",
    )])
    .await;
    let mut env = TestEnv::new();
    env.set("AWS_ENDPOINT_URL_STS", &sts.base_url)
        .set("AWS_MAX_ATTEMPTS", "2");
    env.config("[profile dev]\nrole_arn = arn:aws:iam::1:role/Dev\nsource_profile = base\n[profile base]\naws_access_key_id = AK\naws_secret_access_key = SK\n");
    let error = env.resolve(Some("dev")).await.expect_err("failing");
    assert_eq!(
        described(&error),
        ("InternalFailure".to_owned(), "boom".to_owned())
    );
    let attempts: Vec<_> = sts
        .requests()
        .iter()
        .map(|request| request.headers.get("amz-sdk-request").cloned())
        .collect();
    assert_eq!(
        attempts,
        vec![
            Some("attempt=1; max=2".to_owned()),
            Some("attempt=2; max=2".to_owned())
        ]
    );
}

#[tokio::test]
async fn mfa_profiles_fail_without_a_code_provider() {
    let env = TestEnv::new();
    env.config("[profile dev]\nrole_arn = arn:aws:iam::1:role/Dev\nsource_profile = base\nmfa_serial = arn:mfa\n[profile base]\naws_access_key_id = AK\naws_secret_access_key = SK\n");
    let error = env.resolve(Some("dev")).await.expect_err("mfa");
    assert_eq!(
        described(&error),
        (
            "CredentialsProviderError".to_owned(),
            "Profile dev requires multi-factor authentication, but no MFA code callback was provided."
                .to_owned()
        )
    );
}

#[tokio::test]
async fn credential_source_environment_feeds_assume_role() {
    let sts = MockServer::start(vec![reply(200, STS_SUCCESS)]).await;
    let mut env = TestEnv::new();
    env.set("AWS_ENDPOINT_URL_STS", &sts.base_url)
        .set("AWS_ACCESS_KEY_ID", "AKENV")
        .set("AWS_SECRET_ACCESS_KEY", "SKENV");
    env.config(
        "[profile dev]\nrole_arn = arn:aws:iam::1:role/Dev\ncredential_source = Environment\n",
    );
    assert_eq!(
        env.resolve(Some("dev")).await.expect("assumed"),
        keys("ASIAX", "sec&ret", Some("tok"))
    );
    assert!(sts.requests()[0]
        .headers
        .get("authorization")
        .is_some_and(|value| value.starts_with("AWS4-HMAC-SHA256 Credential=AKENV/")));
}

#[tokio::test]
async fn web_identity_token_file_assumes_role_unsigned() {
    let sts = MockServer::start(vec![reply(
        200,
        "<AssumeRoleWithWebIdentityResponse><AssumeRoleWithWebIdentityResult><Credentials><AccessKeyId>AW</AccessKeyId><SecretAccessKey>SW</SecretAccessKey><SessionToken>TW</SessionToken><Expiration>2030-01-01T00:00:00Z</Expiration></Credentials></AssumeRoleWithWebIdentityResult></AssumeRoleWithWebIdentityResponse>",
    )])
    .await;
    let mut env = TestEnv::new();
    let token_file = env.write("token", "eyJ.tok\n");
    env.set("AWS_ENDPOINT_URL_STS", &sts.base_url)
        .set("AWS_WEB_IDENTITY_TOKEN_FILE", &token_file)
        .set("AWS_ROLE_ARN", "arn:aws:iam::1:role/W")
        .set("AWS_ROLE_SESSION_NAME", "my-session");
    assert_eq!(
        env.resolve(None).await.expect("web identity"),
        keys("AW", "SW", Some("TW"))
    );
    let request = &sts.requests()[0];
    assert_eq!(
        request.body,
        "Action=AssumeRoleWithWebIdentity&Version=2011-06-15&RoleArn=arn%3Aaws%3Aiam%3A%3A1%3Arole%2FW&RoleSessionName=my-session&WebIdentityToken=eyJ.tok%0A"
    );
    assert!(!request.headers.contains_key("authorization"));
}

#[tokio::test]
async fn web_identity_service_errors_map_modeled_names() {
    let sts = MockServer::start(vec![reply(
        400,
        "<ErrorResponse><Error><Code>InvalidIdentityToken</Code><Message>bad</Message></Error></ErrorResponse>",
    )])
    .await;
    let mut env = TestEnv::new();
    let token_file = env.write("token", "tok");
    env.set("AWS_ENDPOINT_URL_STS", &sts.base_url)
        .set("AWS_WEB_IDENTITY_TOKEN_FILE", &token_file)
        .set("AWS_ROLE_ARN", "arn:aws:iam::1:role/W");
    let error = env.resolve(None).await.expect_err("rejected");
    assert_eq!(
        described(&error),
        ("InvalidIdentityTokenException".to_owned(), "bad".to_owned())
    );
}

#[tokio::test]
async fn container_credentials_use_the_full_uri_and_token() {
    let server = MockServer::start(vec![reply(
        200,
        "{\"AccessKeyId\":\"AKC\",\"SecretAccessKey\":\"SKC\",\"Token\":\"TC\",\"Expiration\":\"2030-01-01T00:00:00Z\"}",
    )])
    .await;
    let mut env = TestEnv::new();
    env.set(
        "AWS_CONTAINER_CREDENTIALS_FULL_URI",
        &format!("{}/creds?x=1", server.base_url),
    )
    .set("AWS_CONTAINER_AUTHORIZATION_TOKEN", "Bearer abc");
    assert_eq!(
        env.resolve(None).await.expect("container"),
        keys("AKC", "SKC", Some("TC"))
    );
    let request = &server.requests()[0];
    assert_eq!(
        (request.method.as_str(), request.target.as_str()),
        ("GET", "/creds?x=1")
    );
    assert_eq!(
        request.headers.get("authorization").map(String::as_str),
        Some("Bearer abc")
    );
}

#[tokio::test]
async fn container_hosts_outside_the_allow_list_fall_through() {
    let mut env = TestEnv::new();
    env.set(
        "AWS_CONTAINER_CREDENTIALS_FULL_URI",
        "http://example.com/creds",
    );
    let error = env.resolve(None).await.expect_err("rejected host");
    assert_eq!(described(&error), final_error());
}

#[tokio::test]
async fn instance_metadata_uses_an_imdsv2_token() {
    let imds = MockServer::start(vec![
        reply(200, "imds-token"),
        reply(200, "my-role\n"),
        reply(
            200,
            "{\"Code\":\"Success\",\"AccessKeyId\":\"AKI\",\"SecretAccessKey\":\"SKI\",\"Token\":\"TI\",\"Expiration\":\"2030-01-01T00:00:00Z\"}",
        ),
    ])
    .await;
    let mut env = TestEnv::new();
    env.remove("AWS_EC2_METADATA_DISABLED")
        .set("AWS_EC2_METADATA_SERVICE_ENDPOINT", &imds.base_url);
    assert_eq!(
        env.resolve(None).await.expect("imds"),
        keys("AKI", "SKI", Some("TI"))
    );
    let requests = imds.requests();
    let summary: Vec<_> = requests
        .iter()
        .map(|request| (request.method.clone(), request.target.clone()))
        .collect();
    assert_eq!(
        summary,
        vec![
            ("PUT".to_owned(), "/latest/api/token".to_owned()),
            (
                "GET".to_owned(),
                "/latest/meta-data/iam/security-credentials/".to_owned()
            ),
            (
                "GET".to_owned(),
                "/latest/meta-data/iam/security-credentials/my-role".to_owned()
            ),
        ]
    );
    assert_eq!(
        requests[0]
            .headers
            .get("x-aws-ec2-metadata-token-ttl-seconds")
            .map(String::as_str),
        Some("21600")
    );
    assert_eq!(
        requests[2]
            .headers
            .get("x-aws-ec2-metadata-token")
            .map(String::as_str),
        Some("imds-token")
    );
}

#[tokio::test]
async fn instance_metadata_v1_fallback_can_be_blocked() {
    let imds = MockServer::start(vec![reply(403, "")]).await;
    let mut env = TestEnv::new();
    env.remove("AWS_EC2_METADATA_DISABLED")
        .set("AWS_EC2_METADATA_SERVICE_ENDPOINT", &imds.base_url)
        .set("AWS_EC2_METADATA_V1_DISABLED", "true");
    let error = env.resolve(None).await.expect_err("blocked");
    assert_eq!(described(&error), final_error());
    assert_eq!(imds.requests().len(), 1, "only the token request is sent");
}

#[tokio::test]
async fn sso_profiles_exchange_the_cached_token() {
    let sso = MockServer::start(vec![reply(
        200,
        "{\"roleCredentials\":{\"accessKeyId\":\"AS\",\"secretAccessKey\":\"SS\",\"sessionToken\":\"TS\",\"expiration\":1893456000000}}",
    )])
    .await;
    let mut env = TestEnv::new();
    env.set("AWS_ENDPOINT_URL_SSO", &sso.base_url);
    env.config("[profile sso]\nsso_start_url = https://x.awsapps.com/start\nsso_region = eu-west-1\nsso_account_id = 1234\nsso_role_name = Role Name\n");
    // sha1("https://x.awsapps.com/start")
    let cache_name = hex::encode(<sha1::Sha1 as sha2::Digest>::digest(
        b"https://x.awsapps.com/start",
    ));
    env.write(
        &format!(".aws/sso/cache/{cache_name}.json"),
        "{\"accessToken\":\"at\",\"expiresAt\":\"2999-01-01T00:00:00Z\"}",
    );
    assert_eq!(
        env.resolve(Some("sso")).await.expect("sso"),
        keys("AS", "SS", Some("TS"))
    );
    let request = &sso.requests()[0];
    assert_eq!(
        request.target,
        "/federation/credentials?account_id=1234&role_name=Role%20Name"
    );
    assert_eq!(
        request
            .headers
            .get("x-amz-sso_bearer_token")
            .map(String::as_str),
        Some("at")
    );
}

#[tokio::test]
async fn expired_sso_tokens_stop_the_chain() {
    let env = TestEnv::new();
    env.config("[profile sso]\nsso_start_url = https://y/start\nsso_region = eu-west-1\nsso_account_id = 1\nsso_role_name = R\n");
    let cache_name = hex::encode(<sha1::Sha1 as sha2::Digest>::digest(b"https://y/start"));
    env.write(
        &format!(".aws/sso/cache/{cache_name}.json"),
        "{\"accessToken\":\"at\",\"expiresAt\":\"2000-01-01T00:00:00Z\"}",
    );
    let error = env.resolve(Some("sso")).await.expect_err("expired");
    assert_eq!(
        described(&error),
        (
            "CredentialsProviderError".to_owned(),
            "The SSO session associated with this profile has expired. To refresh this SSO session run aws sso login with the corresponding profile.".to_owned()
        )
    );
}

#[tokio::test]
async fn sso_session_tokens_refresh_through_oidc() {
    let server = MockServer::start(vec![
        reply(
            200,
            "{\"accessToken\":\"new\",\"expiresIn\":3600,\"refreshToken\":\"rt2\",\"tokenType\":\"Bearer\"}",
        ),
        reply(
            200,
            "{\"roleCredentials\":{\"accessKeyId\":\"AS\",\"secretAccessKey\":\"SS\",\"sessionToken\":\"TS\",\"expiration\":1893456000000}}",
        ),
    ])
    .await;
    let mut env = TestEnv::new();
    env.set("AWS_ENDPOINT_URL_SSO", &server.base_url)
        .set("AWS_ENDPOINT_URL_SSO_OIDC", &server.base_url);
    env.config("[profile sso]\nsso_session = my-sso\nsso_account_id = 1234\nsso_role_name = R\n[sso-session my-sso]\nsso_region = us-east-2\nsso_start_url = https://y/start\n");
    let cache_name = hex::encode(<sha1::Sha1 as sha2::Digest>::digest(b"my-sso"));
    let cache_path = env.write(
        &format!(".aws/sso/cache/{cache_name}.json"),
        "{\"accessToken\":\"old\",\"expiresAt\":\"2020-01-01T00:00:00Z\",\"clientId\":\"cid\",\"clientSecret\":\"cs\",\"refreshToken\":\"rt\",\"region\":\"us-east-2\"}",
    );
    assert_eq!(
        env.resolve(Some("sso")).await.expect("sso"),
        keys("AS", "SS", Some("TS"))
    );
    let requests = server.requests();
    assert_eq!(
        (requests[0].target.as_str(), requests[0].body.as_str()),
        (
            "/token",
            "{\"clientId\":\"cid\",\"clientSecret\":\"cs\",\"grantType\":\"refresh_token\",\"refreshToken\":\"rt\"}"
        )
    );
    assert_eq!(
        requests[1]
            .headers
            .get("x-amz-sso_bearer_token")
            .map(String::as_str),
        Some("new")
    );
    let cached = std::fs::read_to_string(cache_path).expect("cache rewritten");
    assert!(
        cached.contains("\"accessToken\": \"new\"") && cached.contains("\"refreshToken\": \"rt2\"")
    );
}

/// A P-256 SEC1 key (with its public point), as `aws login` caches it.
const DPOP_KEY: &str = "-----BEGIN EC PRIVATE KEY-----\nMHcCAQEEIBpNafBRH4IQ3YnTklf8pnFmgv5CTMRBtUohp7ET6qSaoAoGCCqGSM49\nAwEHoUQDQgAESlOJYP2KIyw+KRnpYZH7NFAxX8tiSJpSc4NDzp1yIlp/BiVJW7Nx\nUGXaYc5qDBDViW0mRu678QM2L0xSRV8owA==\n-----END EC PRIVATE KEY-----\n";

#[tokio::test]
async fn login_sessions_refresh_with_a_dpop_proof() {
    let server = MockServer::start(vec![reply(
        200,
        "{\"accessToken\":{\"accessKeyId\":\"A2\",\"secretAccessKey\":\"S2\",\"sessionToken\":\"T2\"},\"refreshToken\":\"rt2\",\"expiresIn\":900,\"tokenType\":\"aws_sigv4\"}",
    )])
    .await;
    let mut env = TestEnv::new();
    let cache_dir = env.path("login");
    env.set("AWS_ENDPOINT_URL_SIGNIN", &server.base_url)
        .set("AWS_LOGIN_CACHE_DIRECTORY", &cache_dir);
    let session = "arn:aws:signin:us-east-1::session/x";
    env.config(&format!(
        "[profile lp]\nlogin_session = {session}\nregion = us-east-1\n"
    ));
    let token = serde_json::json!({
        "accessToken": {
            "accessKeyId": "AK", "secretAccessKey": "SK", "sessionToken": "ST",
            "accountId": "123456789012", "expiresAt": "2020-01-01T00:00:00Z",
        },
        "clientId": "arn:aws:signin:::devtools/same-device",
        "refreshToken": "rt",
        "dpopKey": DPOP_KEY,
    });
    let hash = hex::encode(<sha2::Sha256 as sha2::Digest>::digest(session.as_bytes()));
    env.write(&format!("login/{hash}.json"), &token.to_string());
    assert_eq!(
        env.resolve(Some("lp")).await.expect("login"),
        keys("A2", "S2", Some("T2"))
    );
    let request = &server.requests()[0];
    assert_eq!(
        (request.target.as_str(), request.body.as_str()),
        (
            "/v1/token",
            "{\"clientId\":\"arn:aws:signin:::devtools/same-device\",\"grantType\":\"refresh_token\",\"refreshToken\":\"rt\"}"
        )
    );
    let proof = request.headers.get("dpop").expect("dpop header");
    let parts: Vec<&str> = proof.split('.').collect();
    assert_eq!(parts.len(), 3);
    let header = base64::engine::general_purpose::URL_SAFE_NO_PAD
        .decode(parts[0])
        .expect("header");
    assert_eq!(
        String::from_utf8(header).expect("utf8"),
        "{\"alg\":\"ES256\",\"typ\":\"dpop+jwt\",\"jwk\":{\"kty\":\"EC\",\"crv\":\"P-256\",\"x\":\"SlOJYP2KIyw-KRnpYZH7NFAxX8tiSJpSc4NDzp1yIlo\",\"y\":\"fwYlSVuzcVBl2mHOagwQ1YltJkbuu_EDNi9MUkVfKMA\"}}"
    );
}

#[tokio::test]
async fn aborted_signals_return_their_reason() {
    let imds = MockServer::start(vec![reply(200, "token")]).await;
    let mut env = TestEnv::new();
    env.remove("AWS_EC2_METADATA_DISABLED")
        .set("AWS_EC2_METADATA_SERVICE_ENDPOINT", &imds.base_url);
    let controller = AbortController::new();
    controller.abort(Some(ErrorObject::named("AbortError", "stop").thrown()));
    let signal = controller.signal();
    let error = env
        .resolve_with(None, &BedrockRequestHandler::Default, Some(&signal))
        .await
        .expect_err("aborted");
    assert_eq!(
        described(&error),
        ("AbortError".to_owned(), "stop".to_owned())
    );
}

#[tokio::test]
async fn region_comes_from_env_then_profile_then_metadata() {
    let mut env = TestEnv::new();
    env.config("[default]\nregion = eu-west-1\n[profile other]\nregion = ap-south-1\n");
    env.credentials("[other]\nregion = ca-central-1\n");
    assert_eq!(env.region(None).await.expect("config"), "eu-west-1");
    assert_eq!(
        env.region(Some("other")).await.expect("credentials wins"),
        "ca-central-1"
    );
    env.set("AWS_REGION", "us-east-2");
    assert_eq!(env.region(Some("other")).await.expect("env"), "us-east-2");
    env.remove("AWS_REGION");
    let error = env.region(Some("missing")).await.expect_err("missing");
    assert_eq!(
        described(&error),
        ("Error".to_owned(), "Region is missing".to_owned())
    );

    let imds = MockServer::start(vec![reply(200, "token"), reply(200, " sa-east-1\n")]).await;
    env.remove("AWS_EC2_METADATA_DISABLED")
        .set("AWS_EC2_METADATA_SERVICE_ENDPOINT", &imds.base_url);
    assert_eq!(
        env.region(Some("missing")).await.expect("imds"),
        "sa-east-1"
    );
}
