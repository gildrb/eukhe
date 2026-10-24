//! The Prime Inference credential writes (moved with its concern): the
//! locked read/modify/write of the prime-inference credential, the api-key
//! store with its team selection, the team rebind, and the stored team
//! read (TS setPrimeInferenceApiKey / setPrimeInferenceTeamSelection /
//! getPrimeInferenceTeamSelection). The methods stay inherent on
//! `AuthStorage`: the impl owns the private lock and reload machinery they
//! wrap.

use super::*;

impl AuthStorage {
    /// TS `updatePrimeInferenceCredential`: one locked read/modify/write of
    /// the prime-inference credential (the compiled core decides the write:
    /// `edit_storage_data`); an update returning `None` leaves the document
    /// untouched. A document that failed to load reads as broken. `true`
    /// when the locked run completed (TS returns normally; a write failure
    /// throws, so the callers must not treat a failed run as applied).
    fn update_prime_inference_credential(
        &mut self,
        update: impl FnOnce(Option<AuthCredential>) -> Option<AuthCredential>,
    ) -> bool {
        if self.load_error.is_some()
            && config::rmw(
                config::Read::<String, serde_json::Value>::Broken,
                config::Edit::Delete(PRIME_INFERENCE_PROVIDER_ID.to_string()),
            )
            .is_none()
        {
            return false;
        }
        let mut update = Some(update);
        let result = self.storage.with_lock(&mut |current| {
            let mut failure = None;
            let data = edit_storage_data(current.as_deref(), |data| {
                let existing = data.credential(PRIME_INFERENCE_PROVIDER_ID);
                let credential = (update.take().expect("the lock runs the update once"))(existing)?;
                let mut entry = match serde_json::to_value(&credential) {
                    Ok(entry) => entry,
                    Err(error) => {
                        failure = Some(error);
                        return None;
                    }
                };
                // TS writes `primeTeam: null` explicitly for the personal
                // account (`{ ...credential, primeTeam: null }`); the
                // declarative serde skips a `None` field, so the prime write
                // restores the key. The generic `set` keeps the TS omit
                // shape for other providers' keys.
                if let serde_json::Value::Object(map) = &mut entry {
                    map.entry("primeTeam")
                        .or_insert_with(|| serde_json::Value::Null);
                }
                Some(config::Edit::Set(
                    PRIME_INFERENCE_PROVIDER_ID.to_string(),
                    entry,
                ))
            })?;
            if let Some(error) = failure {
                return Err(error.into());
            }
            let content = data
                .map(|data| serde_json::to_string_pretty(&data.0))
                .transpose()?;
            Ok(((), content))
        });
        if let Err(error) = result {
            self.errors.push(error.to_string());
            return false;
        }
        self.reload();
        true
    }

    /// TS `setPrimeInferenceApiKey`: store the key and its team selection.
    ///
    /// The key arrives from outside (the browser login's challenge result or
    /// a paste), so it is stored only as a literal token: an empty key, a
    /// leading `!` (the `resolve_config_value` shell-command form, reserved
    /// for values the user writes into auth.json by hand), or whitespace and
    /// control characters are refused with an error and nothing is written.
    pub fn set_prime_inference_api_key(&mut self, api_key: &str, team: PrimeTeamAssignment) {
        if api_key.is_empty()
            || api_key.starts_with('!')
            || api_key
                .chars()
                .any(|ch| ch.is_whitespace() || ch.is_control())
        {
            self.errors.push(
                "Refusing to store the Prime API key: it must be a non-empty token without a leading '!', whitespace, or control characters".to_string(),
            );
            return;
        }
        let api_key = api_key.to_string();
        let applied = self.update_prime_inference_credential(|existing| {
            let prime_team = match team {
                PrimeTeamAssignment::Team(team) => Some(team),
                PrimeTeamAssignment::PersonalAccount => None,
                // TS `undefined`: keep the stored team on the same key.
                PrimeTeamAssignment::PreserveWhenKeyMatches => match existing {
                    Some(AuthCredential::ApiKey {
                        key,
                        prime_team: stored,
                    }) if key == api_key => stored,
                    _ => None,
                },
            };
            Some(AuthCredential::ApiKey {
                key: api_key,
                prime_team,
            })
        });
        // TS: the stale clear sits after the write and never runs on a
        // failed one — a failed replacement must not re-enable the
        // server-rejected credential.
        if applied {
            self.clear_stale_auth_source(PRIME_INFERENCE_PROVIDER_ID, AuthSource::Stored);
        }
    }

    /// TS `setPrimeInferenceTeamSelection`: rebind the stored key's team;
    /// `expected_api_key: None` skips the key check (TS `undefined`).
    pub fn set_prime_inference_team_selection(
        &mut self,
        team: Option<PrimeTeamCredential>,
        expected_api_key: Option<&str>,
    ) {
        self.update_prime_inference_credential(|existing| {
            let Some(AuthCredential::ApiKey { key, .. }) = existing else {
                return None;
            };
            if let Some(expected) = expected_api_key {
                if key != expected {
                    return None;
                }
            }
            Some(AuthCredential::ApiKey {
                key,
                prime_team: team,
            })
        });
    }

    /// TS `getPrimeInferenceTeamSelection`: the stored team selection, or
    /// [`StoredPrimeTeam::NotSelected`] when `PRIME_TEAM_ID` pins the team
    /// or no api-key credential is stored. Fleet divergence (P5): the stored
    /// primeTeam survives runtime and environment API-key overrides — TS
    /// returns `undefined` when those are the active source, which forced
    /// dogfood daemons to pin `PRIME_TEAM_ID` in the environment; the stored
    /// login's team is used with whichever key is active instead.
    pub fn get_prime_inference_team_selection(&self) -> StoredPrimeTeam {
        if self
            .env_credentials
            .prime_team_id()
            .and_then(|value| {
                let trimmed = value.trim().to_string();
                (!trimmed.is_empty()).then_some(trimmed)
            })
            .is_some()
        {
            return StoredPrimeTeam::NotSelected;
        }
        match self.data.credential(PRIME_INFERENCE_PROVIDER_ID) {
            Some(AuthCredential::ApiKey { prime_team, .. }) => match prime_team {
                Some(team) => StoredPrimeTeam::Team(team),
                None => StoredPrimeTeam::PersonalAccount,
            },
            _ => StoredPrimeTeam::NotSelected,
        }
    }
}
