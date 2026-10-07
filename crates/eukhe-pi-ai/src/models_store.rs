//! Persistent dynamic model catalogs keyed by provider id. Port of
//! `models-store.ts`.

use std::collections::HashMap;
use std::sync::{Mutex, PoisonError};

use eukhe_chord::context::AbortSignal;
use eukhe_types::pi_ai::AnyModel;
use futures::future::BoxFuture;
use serde::{Deserialize, Deserializer, Serialize};

use crate::utils::diagnostics::Thrown;

/// One provider's persisted catalog: TS `ModelsStoreEntry`.
#[derive(Debug, Clone, Default, PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ModelsStoreEntry {
    /// Persisted models of every type. Deserialization drops models whose
    /// `type` this version does not know (stores written by newer versions),
    /// the TS `withKnownModelTypes`.
    #[serde(deserialize_with = "deserialize_known_models")]
    pub models: Vec<AnyModel>,
    /// Unix timestamp from the remote catalog's Last-Modified header.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub last_modified: Option<f64>,
    /// Unix timestamp of the last completed remote check.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub checked_at: Option<f64>,
    /// Opaque validator from the remote catalog's `ETag` header, stored
    /// verbatim (quotes included) and echoed back as If-None-Match.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub etag: Option<String>,
}

const KNOWN_MODEL_TYPES: [&str; 3] = ["chat", "image", "classifier"];

/// Models without `type` are chat models; other unknown types are skipped.
fn deserialize_known_models<'de, D: Deserializer<'de>>(
    deserializer: D,
) -> Result<Vec<AnyModel>, D::Error> {
    let values = Vec::<serde_json::Value>::deserialize(deserializer)?;
    values
        .into_iter()
        .filter(|value| match value.get("type") {
            None => true,
            Some(model_type) => model_type
                .as_str()
                .is_some_and(|model_type| KNOWN_MODEL_TYPES.contains(&model_type)),
        })
        .map(|value| serde_json::from_value(value).map_err(serde::de::Error::custom))
        .collect()
}

/// Options of every [`ModelsStore`] operation.
#[derive(Debug, Clone, Default)]
pub struct ModelsStoreOperationOptions {
    pub signal: Option<AbortSignal>,
}

/// Persistent model catalogs keyed by provider id. Implementations fail only
/// on storage failure; `read` resolves `None` for missing entries. `Models`
/// serializes writes per provider and passes the refresh signal so a
/// superseded or cancelled refresh can stop waiting on storage.
pub trait ModelsStore: Send + Sync {
    fn read(
        &self,
        provider_id: &str,
        options: ModelsStoreOperationOptions,
    ) -> BoxFuture<'_, Result<Option<ModelsStoreEntry>, Thrown>>;
    fn write(
        &self,
        provider_id: &str,
        entry: ModelsStoreEntry,
        options: ModelsStoreOperationOptions,
    ) -> BoxFuture<'_, Result<(), Thrown>>;
    fn delete(
        &self,
        provider_id: &str,
        options: ModelsStoreOperationOptions,
    ) -> BoxFuture<'_, Result<(), Thrown>>;
}

/// In-memory [`ModelsStore`]: TS `InMemoryModelsStore`.
#[derive(Debug, Default)]
pub struct InMemoryModelsStore {
    entries: Mutex<HashMap<String, ModelsStoreEntry>>,
}

impl InMemoryModelsStore {
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    fn entries(&self) -> std::sync::MutexGuard<'_, HashMap<String, ModelsStoreEntry>> {
        self.entries.lock().unwrap_or_else(PoisonError::into_inner)
    }
}

fn throw_if_aborted(options: &ModelsStoreOperationOptions) -> Result<(), Thrown> {
    options
        .signal
        .as_ref()
        .map_or(Ok(()), AbortSignal::throw_if_aborted)
}

impl ModelsStore for InMemoryModelsStore {
    fn read(
        &self,
        provider_id: &str,
        options: ModelsStoreOperationOptions,
    ) -> BoxFuture<'_, Result<Option<ModelsStoreEntry>, Thrown>> {
        let result = throw_if_aborted(&options).map(|()| self.entries().get(provider_id).cloned());
        Box::pin(async move { result })
    }

    fn write(
        &self,
        provider_id: &str,
        entry: ModelsStoreEntry,
        options: ModelsStoreOperationOptions,
    ) -> BoxFuture<'_, Result<(), Thrown>> {
        let result = throw_if_aborted(&options).map(|()| {
            self.entries().insert(provider_id.to_owned(), entry);
        });
        Box::pin(async move { result })
    }

    fn delete(
        &self,
        provider_id: &str,
        options: ModelsStoreOperationOptions,
    ) -> BoxFuture<'_, Result<(), Thrown>> {
        let result = throw_if_aborted(&options).map(|()| {
            self.entries().remove(provider_id);
        });
        Box::pin(async move { result })
    }
}
