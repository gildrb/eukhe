//! The API-key lookup + OAuth refresh arm (moved with its concern): the
//! resolution walk over the candidate sources (runtime override, prime
//! inference env-before-stored, stored, environment, fallback) with the
//! staleness gate, the OAuth expiry refresh under the per-provider
//! single-flight, and the passthrough `get_api_key` (TS getApiKey).

use super::{
    now_epoch_ms, parse_storage_data, refresh_flight, resolve_config_value,
    resolve_config_value_uncached, AuthApiKeyResult, AuthCredential, AuthStorage,
    PRIME_INFERENCE_PROVIDER_ID,
};

impl AuthStorage {
    pub fn get_api_key_with_source_token(
        &mut self,
        provider_id: &str,
        include_fallback: bool,
    ) -> AuthApiKeyResult {
        // 1. Runtime override.
        if let Some(candidate) = self.runtime_candidate(provider_id) {
            if !self.is_stale(provider_id, &candidate) {
                if let Some(api_key) = self.runtime_overrides.get(provider_id).cloned() {
                    return AuthApiKeyResult {
                        api_key: Some(api_key),
                        source_token: Self::token_for(provider_id, &candidate),
                        credential_type: Some("api_key"),
                        refresh_error: None,
                    };
                }
            }
        }

        let env_key = self.env_credentials.api_key(provider_id);
        let env_candidate = self.environment_candidate(provider_id);

        // 2. Prime-inference: environment before stored.
        if provider_id == PRIME_INFERENCE_PROVIDER_ID {
            if let (Some(api_key), Some(candidate)) = (env_key.clone(), env_candidate.clone()) {
                if !self.is_stale(provider_id, &candidate) {
                    return AuthApiKeyResult {
                        api_key: Some(api_key),
                        source_token: Self::token_for(provider_id, &candidate),
                        credential_type: Some("api_key"),
                        refresh_error: None,
                    };
                }
            }
        }

        // 3. Stored credential.
        if let Some(credential) = self.data.credential(provider_id) {
            if let Some(candidate) = self.stored_candidate(provider_id) {
                if !self.is_stale(provider_id, &candidate) {
                    match &credential {
                        AuthCredential::ApiKey { key, .. } => {
                            let has_stale_record =
                                !self.matching_stale(provider_id, &candidate).is_empty();
                            let api_key = if key.starts_with('!') && has_stale_record {
                                resolve_config_value_uncached(key)
                            } else {
                                resolve_config_value(key)
                            };
                            return AuthApiKeyResult {
                                api_key,
                                source_token: Self::token_for(provider_id, &candidate),
                                credential_type: Some("api_key"),
                                refresh_error: None,
                            };
                        }
                        AuthCredential::Oauth { expires, .. } => {
                            if now_epoch_ms() < *expires {
                                return AuthApiKeyResult {
                                    api_key: self.oauth.api_key_for(provider_id, &credential),
                                    source_token: Self::token_for(provider_id, &candidate),
                                    credential_type: Some("oauth"),
                                    refresh_error: None,
                                };
                            }
                            let error = match self.refresh_oauth(provider_id) {
                                Ok(refreshed) => {
                                    let candidate = self.stored_candidate(provider_id);
                                    return AuthApiKeyResult {
                                        api_key: self.oauth.api_key_for(provider_id, &refreshed),
                                        source_token: candidate
                                            .and_then(|c| Self::token_for(provider_id, &c)),
                                        credential_type: Some("oauth"),
                                        refresh_error: None,
                                    };
                                }
                                Err(cause) => format!(
                                    "OAuth token refresh failed for \"{provider_id}\": {cause}"
                                ),
                            };
                            // The reason rides the result, not `errors`: that
                            // channel reports the caller's own writes (login
                            // and remove flows drain it after a `set`). A
                            // peer may have refreshed meanwhile: reload first.
                            self.reload();
                            let fresh = self.data.credential(provider_id).filter(|credential| {
                                matches!(
                                    credential,
                                    AuthCredential::Oauth { expires, .. } if now_epoch_ms() < *expires
                                )
                            });
                            if let Some(fresh) = fresh {
                                let candidate = self.stored_candidate(provider_id);
                                return AuthApiKeyResult {
                                    api_key: self.oauth.api_key_for(provider_id, &fresh),
                                    source_token: candidate
                                        .and_then(|c| Self::token_for(provider_id, &c)),
                                    credential_type: Some("oauth"),
                                    refresh_error: None,
                                };
                            }
                            // Keep the credential for a later /login retry;
                            // discovery skips the provider.
                            return AuthApiKeyResult {
                                refresh_error: Some(error),
                                ..AuthApiKeyResult::default()
                            };
                        }
                        // A pasted MCP static token IS the api key for its
                        // `mcp:<server>` provider: the bearer value, used
                        // verbatim (no resolution, no expiry).
                        AuthCredential::McpStaticToken { bearer, .. } => {
                            return AuthApiKeyResult {
                                api_key: Some(bearer.clone()),
                                source_token: Self::token_for(provider_id, &candidate),
                                credential_type: Some("mcp_static_token"),
                                refresh_error: None,
                            };
                        }
                    }
                }
            }
        }

        // 4. Environment for non-prime-inference providers.
        if provider_id != PRIME_INFERENCE_PROVIDER_ID {
            if let (Some(api_key), Some(candidate)) = (env_key, env_candidate) {
                if !self.is_stale(provider_id, &candidate) {
                    return AuthApiKeyResult {
                        api_key: Some(api_key),
                        source_token: Self::token_for(provider_id, &candidate),
                        credential_type: None,
                        refresh_error: None,
                    };
                }
            }
        }

        // 5. Fallback resolver.
        if include_fallback {
            if let Some(candidate) = self.fallback_candidate(provider_id) {
                if !self.is_stale(provider_id, &candidate) {
                    let api_key = self
                        .fallback_resolver
                        .as_ref()
                        .and_then(|resolver| resolver(provider_id));
                    return AuthApiKeyResult {
                        api_key,
                        source_token: Self::token_for(provider_id, &candidate),
                        credential_type: None,
                        refresh_error: None,
                    };
                }
            }
        }

        AuthApiKeyResult::default()
    }

    pub fn get_api_key(&mut self, provider_id: &str) -> Option<String> {
        self.get_api_key_with_source_token(provider_id, true)
            .api_key
    }

    /// Refresh an expired OAuth credential, returning the new credential on
    /// success and why the refresh failed otherwise (the caller reloads,
    /// serves a peer's fresh credential, or surfaces the reason).
    ///
    /// Load-then-lock shape: the token fetch is a network round trip and
    /// never runs under the document lock. The TS product runs the same
    /// refresh inside its `withLockAsync` (its single-threaded runtime
    /// pays nothing for holding the lock across the `await`); this engine
    /// is threaded, and the port's [`FileAuthStorageBackend::with_lock`]
    /// spans the whole critical section, so a fetch under the lock stalls
    /// every other same-process auth read and write for the round trip.
    /// The phases:
    ///
    /// 1. LOAD: the current document through the consolidated read arm
    ///    (no document lock; a cache miss pays the read arm's one short
    ///    locked read).
    /// 2. FETCH: the OAuth integration's token call outside every lock,
    ///    behind [`refresh_flight`]'s per-provider single-flight gate. The
    ///    expiry is re-checked under the gate: the first flight may have
    ///    just written a fresh credential, and a second fetch would waste
    ///    a single-use refresh token. In-process callers therefore join
    ///    one flight per provider — the same serialization TS's
    ///    single-threaded runtime gives its locked refresh.
    /// 3. WRITE: the same locked read-modify-write the TS product runs,
    ///    now holding the lock only for the re-read, the insert, and the
    ///    atomic write. A peer that refreshed while this fetch ran keeps
    ///    its fresher credential: this attempt writes nothing and serves
    ///    the peer's.
    fn refresh_oauth(&mut self, provider_id: &str) -> Result<AuthCredential, String> {
        // LOAD: no document lock.
        let content = self
            .storage
            .read()
            .map_err(|error| format!("could not read the auth file: {error:#}"))?;
        let data = parse_storage_data(content.as_deref())
            .map_err(|error| format!("could not parse the auth file: {error:#}"))?;
        let Some(credential) = data.credential(provider_id) else {
            return Err(format!("no stored credential for {provider_id}"));
        };
        let AuthCredential::Oauth { expires, .. } = &credential else {
            return Err(format!(
                "the stored credential for {provider_id} is not OAuth"
            ));
        };
        if now_epoch_ms() < *expires {
            self.reload();
            return Ok(credential);
        }
        // FETCH: outside every lock, one flight per provider.
        let new_credential = {
            let _flight = refresh_flight(provider_id);
            // The gate may have just released a flight that wrote a fresh
            // credential; re-check before spending a refresh token. An
            // unreadable document here fetches from the loaded one.
            let content = self.storage.read().unwrap_or_default();
            if let Some(credential) = parse_storage_data(content.as_deref())
                .ok()
                .and_then(|data| data.credential(provider_id))
                .filter(|credential| {
                    matches!(
                        credential,
                        AuthCredential::Oauth { expires, .. } if now_epoch_ms() < *expires
                    )
                })
            {
                self.reload();
                return Ok(credential);
            }
            self.oauth.refresh(provider_id, &data)?
        };
        // WRITE: the locked read-modify-write, holding the document lock
        // only for the re-read, insert, and atomic write.
        let mut refreshed = new_credential.clone();
        self.storage
            .with_lock(&mut |current| {
                let mut data = parse_storage_data(current.as_deref())?;
                if let Some(credential) = data.credential(provider_id).filter(|credential| {
                    matches!(
                        credential,
                        AuthCredential::Oauth { expires, .. } if now_epoch_ms() < *expires
                    )
                }) {
                    // A peer refreshed while this fetch ran: its fresher
                    // credential stands and this attempt writes nothing.
                    refreshed = credential;
                    return Ok(((), None));
                }
                data.insert(provider_id, &new_credential);
                let content = serde_json::to_string_pretty(&data.0)?;
                Ok(((), Some(content)))
            })
            .map_err(|error| format!("could not save the refreshed credential: {error:#}"))?;
        // Reload from what we wrote: the in-memory snapshot must not
        // serve the pre-refresh credential to a later read (a rotated
        // refresh token is single-use).
        self.reload();
        Ok(refreshed)
    }
}
