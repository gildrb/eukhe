//! The `AuthStorage` unit battery (moved with its concern): the candidate
//! memo + staleness machinery, the runtime/stored/environment/fallback
//! precedence, and the OAuth refresh contract (the hermetic `ScriptedEnv`
//! seam against the ambient env).

use super::*;

/// Fixed environment credential source: hermetic against the ambient
/// process env (a provider key the test box exports).
struct ScriptedEnv(HashMap<String, String>);

impl EnvCredentialSource for ScriptedEnv {
    fn key_names(&self, provider: &str) -> Option<Vec<String>> {
        // The provider's env-var table, filtered to the scripted values (the
        // lookup also consults the process env; the filter keeps it hermetic).
        let scripted: eukhe_types::pi_ai::ProviderEnv = self
            .0
            .iter()
            .map(|(name, value)| (name.clone(), value.clone()))
            .collect();
        let names = eukhe_ai::env_api_keys::find_env_keys(provider, Some(&scripted))?
            .into_iter()
            .filter(|name| self.0.get(name).is_some_and(|value| !value.is_empty()))
            .collect::<Vec<_>>();
        (!names.is_empty()).then_some(names)
    }

    fn api_key(&self, provider: &str) -> Option<String> {
        let first = self.key_names(provider)?.into_iter().next()?;
        self.0.get(&first).cloned().filter(|v| !v.is_empty())
    }

    fn ambient_identity_material(&self, provider: &str) -> String {
        format!("{provider}:scripted-ambient")
    }
}

fn storage_with(data: &serde_json::Value) -> AuthStorage {
    storage_with_env(data, ScriptedEnv(HashMap::new()))
}

fn storage_with_env(data: &serde_json::Value, env: ScriptedEnv) -> AuthStorage {
    let data = AuthStorageData(data.as_object().cloned().unwrap_or_default());
    AuthStorage::in_memory_with_env(&data, Arc::new(NoOAuth), Arc::new(env))
}

#[test]
fn runtime_override_wins() {
    // Runtime beats stored; ambient env of the test
    // process cannot interfere (stored outranks env for these).
    let mut auth = storage_with(&serde_json::json!({
        "anthropic": { "type": "api_key", "key": "stored-key" }
    }));
    assert_eq!(auth.get_api_key("anthropic").as_deref(), Some("stored-key"));
    auth.set_runtime_api_key("anthropic", "runtime-key".to_string());
    assert_eq!(
        auth.get_api_key("anthropic").as_deref(),
        Some("runtime-key")
    );
    auth.remove_runtime_api_key("anthropic");
    assert_eq!(auth.get_api_key("anthropic").as_deref(), Some("stored-key"));
}

#[test]
fn stale_marking_skips_source_and_clears() {
    let mut auth = storage_with(&serde_json::json!({
        "anthropic": { "type": "api_key", "key": "sk-stale" }
    }));
    assert!(auth.mark_auth_stale("anthropic"));
    // The stored credential is now skipped.
    assert_eq!(auth.get_api_key("anthropic"), None);
    let status = auth.get_auth_status("anthropic");
    assert_eq!(status.source, Some(AuthSource::Stale));
    // Explicit clear re-enables it.
    auth.clear_auth_stale("anthropic");
    assert_eq!(auth.get_api_key("anthropic").as_deref(), Some("sk-stale"));
}

#[test]
fn candidate_memos_supersede_exactly_when_material_changes() {
    // The memo is keyed by the hashed material itself (TS #2479's
    // `authCandidateMemos`): a changed env value must re-resolve to the
    // new fingerprint, so a stale marking from the old value never gates
    // the new one, and the same value keeps serving the same
    // resolution.
    let mut auth = storage_with_env(
        &serde_json::json!({}),
        ScriptedEnv(HashMap::from([(
            "ANTHROPIC_API_KEY".to_string(),
            "sk-one".to_string(),
        )])),
    );
    assert_eq!(auth.get_api_key("anthropic").as_deref(), Some("sk-one"));
    assert!(auth.mark_auth_stale("anthropic"));
    assert_eq!(
        auth.get_api_key("anthropic"),
        None,
        "the marked value is gated"
    );
    // A changed value changes the memo key: the rebuilt candidate's
    // value fingerprint differs from the stale token's, so the new
    // value resolves.
    auth.env_credentials = Arc::new(ScriptedEnv(HashMap::from([(
        "ANTHROPIC_API_KEY".to_string(),
        "sk-two".to_string(),
    )])));
    assert_eq!(
        auth.get_api_key("anthropic").as_deref(),
        Some("sk-two"),
        "the memo must not serve the superseded candidate"
    );
    // The marked material's candidate re-serves when its value returns.
    auth.env_credentials = Arc::new(ScriptedEnv(HashMap::from([(
        "ANTHROPIC_API_KEY".to_string(),
        "sk-one".to_string(),
    )])));
    assert_eq!(auth.get_api_key("anthropic"), None);
    auth.clear_auth_stale("anthropic");
    assert_eq!(auth.get_api_key("anthropic").as_deref(), Some("sk-one"));
    // The stored arm: replacing the credential changes the hashed
    // material, so a stale marking of the old key never gates the new
    // one.
    let mut auth = storage_with(&serde_json::json!({
        "anthropic": { "type": "api_key", "key": "sk-old" }
    }));
    assert!(auth.mark_auth_stale("anthropic"));
    auth.set(
        "anthropic",
        AuthCredential::ApiKey {
            key: "sk-new".into(),
        },
    )
    .unwrap();
    assert!(
        auth.has_auth("anthropic"),
        "the replaced credential is not the stale-marked material"
    );
}

#[test]
fn set_and_remove_credentials() {
    let mut auth = storage_with(&serde_json::json!({}));
    auth.set(
        "anthropic",
        AuthCredential::ApiKey {
            key: "sk-ant".into(),
        },
    )
    .unwrap();
    assert!(auth.has("anthropic"));
    assert!(auth.has_auth("anthropic"));
    assert_eq!(auth.get_api_key("anthropic").as_deref(), Some("sk-ant"));
    auth.logout("anthropic").unwrap();
    assert!(!auth.has("anthropic"));
    assert_eq!(auth.get_api_key("anthropic"), None);
}

#[test]
fn command_keys_resolve() {
    let mut auth = storage_with(&serde_json::json!({
        "anthropic": { "type": "api_key", "key": "!echo cmd-key" }
    }));
    assert_eq!(auth.get_api_key("anthropic").as_deref(), Some("cmd-key"));
}

#[test]
fn fallback_resolver_last_resort() {
    let mut auth = storage_with(&serde_json::json!({}));
    auth.set_fallback_resolver(Arc::new(|provider| {
        (provider == "custom").then(|| "fb-key".to_string())
    }));
    assert_eq!(auth.get_api_key("custom").as_deref(), Some("fb-key"));
}

/// The bytes and the mode of a file: the two things a refused write must
/// not change.
fn file_state(path: &std::path::Path) -> (Vec<u8>, u32) {
    use std::os::unix::fs::PermissionsExt;
    // Read the mode with `metadata` and the bytes after a chmod to 0600,
    // because a 000 file cannot be read. Put the mode back after.
    let mode = std::fs::metadata(path).unwrap().permissions().mode() & 0o777;
    std::fs::set_permissions(path, std::fs::Permissions::from_mode(0o600)).unwrap();
    let bytes = std::fs::read(path).unwrap();
    std::fs::set_permissions(path, std::fs::Permissions::from_mode(mode)).unwrap();
    (bytes, mode)
}

fn api_key(key: &str) -> AuthCredential {
    AuthCredential::ApiKey {
        key: key.to_owned(),
    }
}

#[test]
fn set_over_an_unreadable_auth_file_is_refused_and_writes_nothing() {
    use std::os::unix::fs::PermissionsExt;
    let dir = tempfile::tempdir().unwrap();
    let path = dir.path().join("auth.json");
    let document = r#"{ "a": { "type": "api_key", "key": "ka" } }"#;
    std::fs::write(&path, document).unwrap();
    // The file is readable at load. It becomes unreadable after.
    let mut auth = AuthStorage::create(dir.path());
    std::fs::set_permissions(&path, std::fs::Permissions::from_mode(0o000)).unwrap();
    let Err(read_error) = std::fs::read(&path) else {
        eprintln!("skipped: this user (root) can read a 000 file");
        return;
    };
    let before = file_state(&path);
    let result = auth
        .set("b", api_key("kb"))
        .map_err(|error| error.to_string());
    assert_eq!(
        (result, file_state(&path)),
        (
            Err(format!(
                "Failed to write {}: Failed to read {}: {read_error}",
                path.display(),
                path.display()
            )),
            before,
        )
    );
    // A storage that loads an unreadable file records a load error, and
    // its write is refused too. A new path: the process read cache still
    // holds the readable copy of the first one.
    let dir = tempfile::tempdir().unwrap();
    let path = dir.path().join("auth.json");
    std::fs::write(&path, document).unwrap();
    std::fs::set_permissions(&path, std::fs::Permissions::from_mode(0o000)).unwrap();
    let before = file_state(&path);
    let mut auth = AuthStorage::create(dir.path());
    let load_error = format!("Failed to read {}: {read_error}", path.display());
    assert_eq!(
        auth.load_error().map(ToString::to_string),
        Some(load_error.clone())
    );
    assert_eq!(
        (
            auth.remove("a").map_err(|error| error.to_string()),
            file_state(&path)
        ),
        (
            Err(format!(
                "Failed to write {}: the document failed to load: {load_error}",
                path.display()
            )),
            before,
        )
    );
}

#[test]
fn set_over_an_invalid_auth_file_is_refused_and_writes_nothing() {
    let dir = tempfile::tempdir().unwrap();
    let path = dir.path().join("auth.json");
    let broken = r#"{ "a": { "type": "api_key", "key": "ka" },"#;
    let parse_error = serde_json::from_str::<serde_json::Value>(broken)
        .unwrap_err()
        .to_string();
    // The file breaks after the load (an editor mid-save).
    let mut auth = AuthStorage::create(dir.path());
    std::fs::write(&path, broken).unwrap();
    let before = file_state(&path);
    assert_eq!(
        (
            auth.set("b", api_key("kb"))
                .map_err(|error| error.to_string()),
            file_state(&path)
        ),
        (
            Err(format!("Failed to write {}: {parse_error}", path.display())),
            before.clone(),
        )
    );
    // The file is broken at load.
    let mut auth = AuthStorage::create(dir.path());
    assert_eq!(
        (
            auth.set("b", api_key("kb"))
                .map_err(|error| error.to_string()),
            file_state(&path)
        ),
        (
            Err(format!(
                "Failed to write {}: the document failed to load: {parse_error}",
                path.display()
            )),
            before,
        )
    );
}

#[test]
fn set_keeps_every_other_credential_as_read() {
    let dir = tempfile::tempdir().unwrap();
    let path = dir.path().join("auth.json");
    let a = serde_json::json!({ "type": "api_key", "key": "ka", "note": "kept as is" });
    let c = serde_json::json!({
        "type": "oauth", "access": "ac", "refresh": "rc", "expires": 7, "extra": [1, 2]
    });
    std::fs::write(
        &path,
        serde_json::to_string(&serde_json::json!({ "a": a, "c": c })).unwrap(),
    )
    .unwrap();
    let mut auth = AuthStorage::create(dir.path());
    auth.set("b", api_key("kb")).unwrap();
    let written: serde_json::Value =
        serde_json::from_str(&std::fs::read_to_string(&path).unwrap()).unwrap();
    // Each entry written as one credential is rewritten as its one account,
    // every field kept.
    assert_eq!(
        written,
        serde_json::json!({
            "a": { "accounts": [{
                "type": "api_key", "key": "ka", "note": "kept as is", "identity": "key"
            }] },
            "b": { "accounts": [{ "type": "api_key", "key": "kb", "identity": "key" }] },
            "c": { "accounts": [c] },
        })
    );
}

/// A scripted OAuth integration for the refresh-flow tests: counts
/// refresh calls, optionally delays inside the fetch, and serves a
/// fixed fresh credential.
struct CountingOAuth {
    calls: std::sync::atomic::AtomicUsize,
    delay_ms: u64,
}

impl CountingOAuth {
    fn fetched_credential() -> AuthCredential {
        AuthCredential::Oauth {
            access: "fetched-access".into(),
            refresh: Some("fetched-refresh".into()),
            expires: now_epoch_ms() + 3_600_000,
            account_id: None,
            enterprise_url: None,
            endpoint: None,
            token_endpoint: None,
            client_id: None,
            resource: None,
            issuer: None,
        }
    }
}

impl OAuthIntegration for CountingOAuth {
    fn api_key_for(&self, _provider: &str, credential: &AuthCredential) -> Option<String> {
        match credential {
            AuthCredential::Oauth { access, .. } => Some(access.clone()),
            _ => None,
        }
    }

    fn refresh(
        &self,
        _provider: &str,
        _credentials: &AuthStorageData,
    ) -> Result<AuthCredential, OAuthRefreshError> {
        self.calls.fetch_add(1, std::sync::atomic::Ordering::SeqCst);
        if self.delay_ms > 0 {
            std::thread::sleep(std::time::Duration::from_millis(self.delay_ms));
        }
        Ok(Self::fetched_credential())
    }
}

fn oauth_credential(access: &str, expires: i64) -> AuthCredential {
    AuthCredential::Oauth {
        access: access.into(),
        refresh: Some("test-refresh".into()),
        expires,
        account_id: None,
        enterprise_url: None,
        endpoint: None,
        token_endpoint: None,
        client_id: None,
        resource: None,
        issuer: None,
    }
}

fn expired_oauth(access: &str) -> AuthCredential {
    oauth_credential(access, 1000)
}

fn storage_over_backend_with(
    oauth: Arc<dyn OAuthIntegration>,
    provider: &str,
    credential: &AuthCredential,
) -> (AuthStorage, Arc<dyn AuthStorageBackend>) {
    let backend: Arc<dyn AuthStorageBackend> =
        Arc::new(crate::auth::storage::InMemoryAuthStorageBackend::default());
    let mut data = AuthStorageData::default();
    data.insert(provider, credential);
    let seed = serde_json::to_string_pretty(&data.0).unwrap_or_default();
    backend
        .with_lock(&mut |current| {
            let _ = current;
            Ok(((), Some(seed.clone())))
        })
        .ok();
    (
        AuthStorage::from_storage(Arc::clone(&backend), oauth),
        backend,
    )
}

#[test]
fn an_unexpired_oauth_credential_serves_without_a_fetch() {
    let oauth = Arc::new(CountingOAuth {
        calls: std::sync::atomic::AtomicUsize::new(0),
        delay_ms: 0,
    });
    let (mut auth, _backend) = storage_over_backend_with(
        oauth.clone(),
        "x-fast",
        &oauth_credential("live-access", now_epoch_ms() + 3_600_000),
    );
    assert_eq!(auth.get_api_key("x-fast").as_deref(), Some("live-access"));
    assert_eq!(
        oauth.calls.load(std::sync::atomic::Ordering::SeqCst),
        0,
        "the unexpired credential serves without a token fetch"
    );
}

#[test]
fn the_token_fetch_holds_no_document_lock_and_a_peer_write_keeps_its_fresher_credential() {
    // The fetch runs outside every lock: a locked writer lands
    // mid-fetch, and the write phase keeps the peer's fresher
    // credential instead of overwriting it with this attempt's own
    // fetched token.
    let oauth = Arc::new(CountingOAuth {
        calls: std::sync::atomic::AtomicUsize::new(0),
        delay_ms: 120,
    });
    let (mut auth, backend) =
        storage_over_backend_with(oauth.clone(), "x-peer", &expired_oauth("old-access"));
    let writer_backend = Arc::clone(&backend);
    let (wrote_tx, wrote_rx) = std::sync::mpsc::channel::<std::time::Duration>();
    std::thread::spawn(move || {
        // Mid-fetch: the resolving thread is inside the token fetch.
        std::thread::sleep(std::time::Duration::from_millis(40));
        let mut peer = AuthStorageData::default();
        peer.insert(
            "x-peer",
            &oauth_credential("peer-access", now_epoch_ms() + 3_600_000),
        );
        let content = serde_json::to_string_pretty(&peer.0).unwrap_or_default();
        let t0 = std::time::Instant::now();
        writer_backend
            .with_lock(&mut |current| {
                let _ = current;
                Ok(((), Some(content.clone())))
            })
            .ok();
        wrote_tx
            .send(t0.elapsed())
            .expect("the test main thread still waits for the write");
    });
    let api_key = auth.get_api_key("x-peer");
    let write_wall = wrote_rx
        .recv_timeout(std::time::Duration::from_secs(3))
        .expect("the peer's locked write completed; a token fetch must not hold the document lock");
    assert!(
        write_wall < std::time::Duration::from_millis(60),
        "the concurrent locked write waited {write_wall:?}: the fetch holds no lock"
    );
    assert_eq!(
        api_key.as_deref(),
        Some("peer-access"),
        "the peer's fresher credential wins over this attempt's own fetch"
    );
    let stored = auth.get_all().credential("x-peer").unwrap();
    let AuthCredential::Oauth { access, .. } = stored else {
        panic!("the stored credential stays OAuth");
    };
    assert_eq!(access, "peer-access");
    assert_eq!(
        oauth.calls.load(std::sync::atomic::Ordering::SeqCst),
        1,
        "exactly one fetch ran"
    );
}

/// A scripted OAuth integration whose token fetch reports that it started
/// and then blocks until the test answers it: a test keeps a flight in
/// flight for as long as it needs. With the answer channel closed, a fetch
/// fails at once.
struct GatedOAuth {
    calls: std::sync::atomic::AtomicUsize,
    started: std::sync::Mutex<std::sync::mpsc::Sender<()>>,
    answers: std::sync::Mutex<std::sync::mpsc::Receiver<GateAnswer>>,
}

/// How a gated token fetch ends.
enum GateAnswer {
    Credential,
    Panic,
}

impl OAuthIntegration for GatedOAuth {
    fn api_key_for(&self, _provider: &str, credential: &AuthCredential) -> Option<String> {
        match credential {
            AuthCredential::Oauth { access, .. } => Some(access.clone()),
            _ => None,
        }
    }

    fn refresh(
        &self,
        _provider: &str,
        _credentials: &AuthStorageData,
    ) -> Result<AuthCredential, OAuthRefreshError> {
        let failed = |text: &str| OAuthRefreshError::Flow(Arc::new(std::io::Error::other(text)));
        self.calls.fetch_add(1, std::sync::atomic::Ordering::SeqCst);
        self.started
            .lock()
            .unwrap()
            .send(())
            .map_err(|_| failed("the test stopped listening"))?;
        let answer = self.answers.lock().unwrap().recv();
        match answer {
            Ok(GateAnswer::Credential) => Ok(CountingOAuth::fetched_credential()),
            Ok(GateAnswer::Panic) => panic!("the token endpoint client panicked"),
            Err(_) => Err(failed("the test answers no more fetches")),
        }
    }
}

/// A gated integration over an expired `x-flight` credential, its backend,
/// and the test's ends of the gate.
fn gated_flight() -> (
    Arc<GatedOAuth>,
    Arc<dyn AuthStorageBackend>,
    std::sync::mpsc::Receiver<()>,
    std::sync::mpsc::Sender<GateAnswer>,
) {
    let (started, started_rx) = std::sync::mpsc::channel();
    let (answer_tx, answers) = std::sync::mpsc::channel();
    let oauth = Arc::new(GatedOAuth {
        calls: std::sync::atomic::AtomicUsize::new(0),
        started: std::sync::Mutex::new(started),
        answers: std::sync::Mutex::new(answers),
    });
    let (_, backend) =
        storage_over_backend_with(oauth.clone(), "x-flight", &expired_oauth("old-access"));
    (oauth, backend, started_rx, answer_tx)
}

/// A caller that resolves `x-flight` on its own thread, as a session does.
fn resolve_on_thread(
    oauth: &Arc<GatedOAuth>,
    backend: &Arc<dyn AuthStorageBackend>,
) -> std::thread::JoinHandle<AuthApiKeyResult> {
    let oauth: Arc<dyn OAuthIntegration> = oauth.clone();
    let backend = Arc::clone(backend);
    std::thread::spawn(move || {
        AuthStorage::from_storage(backend, oauth)
            .get_api_key_with_source_token("x-flight", /*include_fallback*/ true)
    })
}

#[test]
fn a_second_refresh_joins_the_first_flight_instead_of_fetching_again() {
    // The first caller's fetch is in flight when the second caller
    // arrives: the second joins the flight and serves its credential
    // without a fetch of its own.
    let (oauth, backend, started, answers) = gated_flight();
    let leader = resolve_on_thread(&oauth, &backend);
    started.recv().expect("the leader's fetch started");
    let joiner = resolve_on_thread(&oauth, &backend);
    backend.flights().wait_for_joiners("x-flight", 1);
    answers.send(GateAnswer::Credential).unwrap();
    drop(answers);
    let keys = [leader.join().unwrap(), joiner.join().unwrap()].map(|result| result.api_key);
    assert_eq!(
        (keys, oauth.calls.load(std::sync::atomic::Ordering::SeqCst)),
        (
            [
                Some("fetched-access".to_string()),
                Some("fetched-access".to_string())
            ],
            1
        ),
        "one flight per provider: the second caller served the first's fresh credential"
    );
}

#[test]
fn a_leader_that_panics_lands_its_flight_with_a_failure() {
    // The leader's fetch panics while a second caller waits for the
    // flight: the flight lands with a failure, and the waiting caller
    // gets it instead of waiting forever.
    let (oauth, backend, started, answers) = gated_flight();
    let leader = resolve_on_thread(&oauth, &backend);
    started.recv().expect("the leader's fetch started");
    let joiner = resolve_on_thread(&oauth, &backend);
    backend.flights().wait_for_joiners("x-flight", 1);
    answers.send(GateAnswer::Panic).unwrap();
    assert!(leader.join().is_err(), "the leader's fetch panicked");
    let served = joiner.join().unwrap();
    assert_eq!(
        (
            served.api_key,
            served.refresh_error.map(|error| error.to_string())
        ),
        (
            None,
            Some(
                "OAuth token refresh failed for \"x-flight\": the token refresh of x-flight \
                 ended without an outcome"
                    .to_string()
            )
        )
    );
}

fn read_file(path: &std::path::Path) -> serde_json::Value {
    serde_json::from_str(&std::fs::read_to_string(path).unwrap()).unwrap()
}

/// An auth file written before accounts loads: each provider's one
/// credential is its one account, rewritten as an account list in place;
/// an MCP server's entry stays as it was.
#[test]
fn a_single_account_file_loads_and_migrates_in_place() {
    let dir = tempfile::tempdir().unwrap();
    let path = dir.path().join("auth.json");
    std::fs::write(
        &path,
        serde_json::json!({
            "openai": { "type": "api_key", "key": "sk-openai-123456" },
            "mcp:linear": { "type": "mcp_static_token", "bearer": "b" },
        })
        .to_string(),
    )
    .unwrap();
    let mut auth = AuthStorage::create_with_oauth(dir.path(), Arc::new(NoOAuth));
    assert_eq!(
        (auth.get_api_key("openai"), read_file(&path),),
        (
            Some("sk-openai-123456".to_owned()),
            serde_json::json!({
                "openai": { "accounts": [
                    { "type": "api_key", "key": "sk-openai-123456", "identity": "key ...123456" }
                ] },
                "mcp:linear": { "type": "mcp_static_token", "bearer": "b" },
            }),
        )
    );
}

/// A login adds an account and keeps the others; a login again as the
/// same identity replaces its account; a logout removes only the account
/// it names, the provider going with its last.
#[test]
fn logins_add_accounts_and_a_logout_removes_only_its_account() {
    let dir = tempfile::tempdir().unwrap();
    let path = dir.path().join("auth.json");
    let mut auth = AuthStorage::create_with_oauth(dir.path(), Arc::new(NoOAuth));
    let key = |key: &str| AuthCredential::ApiKey {
        key: key.to_owned(),
    };
    let labels = [
        auth.add_account("p", key("sk-aaaa-111111"), "").unwrap(),
        auth.add_account("p", key("sk-bbbb-222222"), "").unwrap(),
        auth.add_account("p", key("sk-cccc-333333"), "").unwrap(),
        auth.add_account("p", key("sk-dddd-222222"), "").unwrap(),
    ];
    let removed = [
        auth.remove_account("p", &AccountSelector::Place(2))
            .unwrap(),
        auth.remove_account("p", &AccountSelector::Identity("key ...nobody".to_owned()))
            .unwrap(),
    ];
    let after_one = read_file(&path);
    let last = [
        auth.remove_account("p", &AccountSelector::Identity("key ...111111".to_owned()))
            .unwrap(),
        auth.remove_account("p", &AccountSelector::Place(1))
            .unwrap(),
    ];
    assert_eq!(
        (labels, removed, after_one, last, read_file(&path)),
        (
            [
                "key ...111111".to_owned(),
                "key ...222222".to_owned(),
                "key ...333333".to_owned(),
                "key ...222222".to_owned(),
            ],
            [Some("key ...222222".to_owned()), None],
            serde_json::json!({ "p": { "accounts": [
                { "type": "api_key", "key": "sk-aaaa-111111", "identity": "key ...111111" },
                { "type": "api_key", "key": "sk-cccc-333333", "identity": "key ...333333" },
            ] } }),
            [
                Some("key ...111111".to_owned()),
                Some("key ...333333".to_owned())
            ],
            serde_json::json!({}),
        )
    );
}
