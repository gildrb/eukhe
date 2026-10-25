//! Durable MCP connection records (port of
//! `packages/coding-agent/src/core/mcp/connection-store.ts`, the record
//! core): the verified connection state per connectionId — the stable alias
//! the kernel dispatches through — plus the catalog serviceId it connects
//! and the endpoint the verification ran against. Tokens never live here.
//!
//! The record endpoint is the ENDPOINT PIN: an installed connection keeps
//! its approved endpoint for dispatch and management even if the catalog
//! later changes the service URL, and the resolver pins vanished sources
//! from it. Writes are locked read-modify-write (the auth-storage pattern:
//! lockfile + atomic temp-file rename at mode 0600); the compiled core
//! decides what a write writes (`laws/config.bend`: a broken file is never
//! written, every other record stays).

use std::collections::HashMap;
use std::path::{Path, PathBuf};
use std::time::{SystemTime, UNIX_EPOCH};

use eukhe_bend::rules::config;
use serde::{Deserialize, Serialize};

use crate::settings::storage::{atomic_write_with, AtomicWriteOptions};

/// The connections file version.
const FILE_VERSION: u8 = 1;
/// One connection's verified state.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct McpConnectionRecord {
    /// Auth key suffix (`mcp:<connectionId>`) and the kernel dispatch id.
    pub connection_id: String,
    /// Catalog service id; deliberately distinct from the connectionId
    /// (`acme-2` aliases keep their parent's service id).
    pub service_id: String,
    /// Endpoint the record's verification ran against (the pin).
    pub endpoint: String,
    pub label: String,
    pub status: McpConnectionStatus,
    pub created_at: u64,
    pub updated_at: u64,
    /// Epoch ms of the last successful handshake + tools/list.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub verified_at: Option<u64>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub tool_count: Option<usize>,
    /// Fixed, safe failure category (never URLs or server-controlled text).
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub last_error: Option<String>,
    /// Opaque one-time ownership nonce for a pending login attempt.
    #[serde(rename = "attemptId", default, skip_serializing_if = "Option::is_none")]
    pub attempt_id: Option<String>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub enum McpConnectionStatus {
    Connected,
    Pending,
    Error,
}

impl McpConnectionStatus {
    pub fn as_str(self) -> &'static str {
        match self {
            McpConnectionStatus::Connected => "connected",
            McpConnectionStatus::Pending => "pending",
            McpConnectionStatus::Error => "error",
        }
    }
}

/// The connections file: `{ "version": 1, "connections": { id: record } }`.
#[derive(Debug, Deserialize)]
#[serde(deny_unknown_fields)]
struct ConnectionsFile {
    version: u8,
    #[serde(default)]
    connections: HashMap<String, McpConnectionRecord>,
}

/// Durable connection-record store. One instance per process is fine: every
/// mutating op re-reads the latest on-disk state under the lockfile and
/// applies only this call's change, so the interactive client and the daemon
/// worker can both mutate the file.
#[derive(Debug)]
pub struct McpConnectionStore {
    path: PathBuf,
    records: HashMap<String, McpConnectionRecord>,
    /// Why the last load could not use the file. The store then serves no
    /// records and refuses every write until the file is good again.
    load_error: Option<String>,
}

/// The result of one read of the connections file.
enum DiskRead {
    /// The file does not exist.
    Missing,
    /// The file holds a good document of the current version.
    Parsed(HashMap<String, McpConnectionRecord>),
    /// The file exists but this build cannot use it. Nothing may write it.
    Broken(String),
}

fn now_ms() -> u64 {
    SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .map(|since| since.as_millis() as u64)
        .unwrap_or_default()
}

/// A structurally valid record (matching the TS `sanitizeRecord` checks).
fn record_valid(record: &McpConnectionRecord) -> bool {
    !record.connection_id.is_empty()
        && !record.service_id.is_empty()
        && !record.endpoint.is_empty()
        && !record.label.is_empty()
        && record.created_at > 0
        && record.updated_at > 0
}

impl McpConnectionStore {
    /// Open the store at `<agent-dir>/mcp-connections.json` and load the
    /// latest records from disk. A missing file is an empty store. A file
    /// that cannot be used sets [`Self::load_error`].
    pub fn open(path: impl Into<PathBuf>) -> Self {
        let mut store = Self {
            path: path.into(),
            records: HashMap::new(),
            load_error: None,
        };
        store.load();
        store
    }

    /// In-memory store (tests, embedded hosts).
    pub fn in_memory() -> Self {
        Self {
            path: PathBuf::new(),
            records: HashMap::new(),
            load_error: None,
        }
    }

    /// Re-read the latest on-disk state (another process may have written).
    /// A file that cannot be used clears the records and sets
    /// [`Self::load_error`].
    pub fn load(&mut self) {
        if self.path.as_os_str().is_empty() {
            return;
        }
        match read_records(&self.path) {
            DiskRead::Missing => {
                self.records = HashMap::new();
                self.load_error = None;
            }
            DiskRead::Parsed(records) => {
                self.records = records;
                self.load_error = None;
            }
            DiskRead::Broken(reason) => {
                self.records = HashMap::new();
                self.load_error = Some(reason);
            }
        }
    }

    /// Why the last read of the file could not use it, if it could not.
    /// The records are empty then.
    pub fn load_error(&self) -> Option<&str> {
        self.load_error.as_deref()
    }

    /// All records, sorted by connectionId (deterministic order).
    pub fn records(&self) -> Vec<McpConnectionRecord> {
        let mut records: Vec<McpConnectionRecord> = self.records.values().cloned().collect();
        records.sort_by(|a, b| a.connection_id.cmp(&b.connection_id));
        records
    }

    /// One record by connectionId.
    pub fn get(&self, connection_id: &str) -> Option<&McpConnectionRecord> {
        self.records.get(connection_id)
    }

    /// Insert or update one record (locked read-modify-write: the on-disk
    /// state wins for every OTHER id first). Install paths and tests that
    /// build records by hand.
    #[cfg(test)]
    pub fn upsert(&mut self, record: &McpConnectionRecord) -> Result<(), anyhow::Error> {
        self.with_disk_state(|_| {
            Some(config::Edit::Set(
                record.connection_id.clone(),
                record.clone(),
            ))
        })
    }

    /// Remove one record entirely (disconnect keeps nothing behind).
    pub fn remove(&mut self, connection_id: &str) -> Result<(), anyhow::Error> {
        self.with_disk_state(|_| Some(config::Edit::Delete(connection_id.to_string())))
    }

    /// Apply one verification outcome under the shared guard: a stale probe
    /// (the credential changed) never marks a newer grant or a logged-out
    /// connection verified — the result is discarded and the caller is
    /// told. A fresh install (no record yet) commits only when the probe's
    /// credential is still the stored one; a vanished record (removed
    /// mid-probe) commits nothing.
    pub fn apply_verify_result(
        &mut self,
        record: &McpConnectionRecord,
        still_current: bool,
    ) -> Result<bool, anyhow::Error> {
        let connection_id = record.connection_id.clone();
        let mut committed = false;
        self.with_disk_state(|records| {
            let commit = match records.get(&connection_id) {
                None => still_current,
                Some(existing) => existing.attempt_id.is_none() && still_current,
            };
            committed = commit;
            commit.then(|| config::Edit::Set(connection_id.clone(), record.clone()))
        })?;
        Ok(committed)
    }

    /// Locked read-modify-write: reload the disk state, let `change` pick
    /// its edit from it, let the compiled core decide what to write
    /// ([`config::rmw`]), write it back atomically. An in-memory store
    /// keeps the core's answer as its records. A file that cannot be used
    /// is an error, and nothing is written.
    fn with_disk_state(
        &mut self,
        change: impl FnOnce(
            &HashMap<String, McpConnectionRecord>,
        ) -> Option<config::Edit<String, McpConnectionRecord>>,
    ) -> Result<(), anyhow::Error> {
        if self.path.as_os_str().is_empty() {
            if let Some(edit) = change(&self.records) {
                let read =
                    config::Read::Parsed(std::mem::take(&mut self.records).into_iter().collect());
                let Some(records) = config::rmw(read, edit) else {
                    anyhow::bail!("the compiled core refused the in-memory connections");
                };
                self.records = records.into_iter().collect();
            }
            return Ok(());
        }
        let lock = crate::platform::lock_dir::LockDir::acquire(
            &self.path,
            std::time::Duration::from_secs(10),
        )
        .map_err(|error| anyhow::anyhow!("connection store lock: {error}"))?;
        let (records, broken) = match read_records(&self.path) {
            DiskRead::Missing => (None, None),
            DiskRead::Parsed(records) => (Some(records), None),
            DiskRead::Broken(reason) => (None, Some(reason)),
        };
        let edit = change(records.as_ref().unwrap_or(&HashMap::new()));
        let written = edit.map(|edit| {
            let read = match (records, &broken) {
                (_, Some(_)) => config::Read::Broken,
                (Some(records), None) => config::Read::Parsed(records.into_iter().collect()),
                (None, None) => config::Read::Missing,
            };
            config::rmw(read, edit)
        });
        match (written, broken) {
            (Some(Some(records)), _) => {
                let records: HashMap<String, McpConnectionRecord> = records.into_iter().collect();
                write_records(&self.path, &records)?;
                drop(lock);
                self.records = records;
                self.load_error = None;
                Ok(())
            }
            (Some(None) | None, Some(reason)) => {
                drop(lock);
                self.records = HashMap::new();
                self.load_error = Some(reason.clone());
                anyhow::bail!("{reason}");
            }
            (None, None) => Ok(()),
            (Some(None), None) => {
                anyhow::bail!("the compiled core refused a readable connections file")
            }
        }
    }
}

/// Read the file's records. Only a file that does not exist is
/// [`DiskRead::Missing`]. A file that cannot be read, is not JSON, has the
/// wrong shape, has a version other than [`FILE_VERSION`], or holds a
/// record that is not valid is [`DiskRead::Broken`].
fn read_records(path: &Path) -> DiskRead {
    let content = match std::fs::read_to_string(path) {
        Ok(content) => content,
        Err(error) if error.kind() == std::io::ErrorKind::NotFound => return DiskRead::Missing,
        Err(error) => {
            return DiskRead::Broken(format!("cannot read {}: {error}", path.display()));
        }
    };
    let file = match serde_json::from_str::<ConnectionsFile>(&content) {
        Ok(file) => file,
        Err(error) => {
            return DiskRead::Broken(format!("cannot parse {}: {error}", path.display()));
        }
    };
    if file.version != FILE_VERSION {
        return DiskRead::Broken(format!(
            "{} has version {}; this build reads only version {FILE_VERSION}",
            path.display(),
            file.version
        ));
    }
    for (id, record) in &file.connections {
        if *id != record.connection_id || !record_valid(record) {
            return DiskRead::Broken(format!(
                "{} holds a connection record that is not valid: {id}",
                path.display()
            ));
        }
    }
    DiskRead::Parsed(file.connections)
}

/// Write the file atomically (temp + rename, mode 0600).
fn write_records(
    path: &Path,
    records: &HashMap<String, McpConnectionRecord>,
) -> Result<(), anyhow::Error> {
    let ordered: std::collections::BTreeMap<&String, &McpConnectionRecord> =
        records.iter().collect();
    let doc = serde_json::json!({
        "version": FILE_VERSION,
        "connections": ordered,
    });
    atomic_write_with(
        path,
        &serde_json::to_string_pretty(&doc)?,
        AtomicWriteOptions { fsync: true },
    )?;
    Ok(())
}

/// A fresh pending record for one connection (verification fills the rest).
pub fn new_pending_record(
    connection_id: &str,
    service_id: &str,
    label: &str,
    endpoint: &str,
) -> McpConnectionRecord {
    let now = now_ms();
    McpConnectionRecord {
        connection_id: connection_id.to_string(),
        service_id: service_id.to_string(),
        endpoint: endpoint.to_string(),
        label: label.to_string(),
        status: McpConnectionStatus::Pending,
        created_at: now,
        updated_at: now,
        verified_at: None,
        tool_count: None,
        last_error: None,
        attempt_id: None,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Per-call-site served-path oracle: the registry write goes through the
    /// real `write_records` writer and takes exactly one fsync branch (the
    /// registry holds connection state that is not refetchable), landing
    /// the exact serialized document bytes.
    #[test]
    fn registry_write_takes_exactly_one_fsync() {
        let dir = tempfile::tempdir().unwrap();
        let path = dir.path().join("connections.json");
        let record = McpConnectionRecord {
            connection_id: "c1".to_string(),
            service_id: "acme".to_string(),
            endpoint: "https://acme.example/mcp".to_string(),
            label: "Acme".to_string(),
            status: McpConnectionStatus::Connected,
            created_at: 1,
            updated_at: 1,
            verified_at: Some(2),
            tool_count: Some(3),
            last_error: None,
            attempt_id: None,
        };
        let mut records = HashMap::new();
        records.insert(record.connection_id.clone(), record);
        let doc = serde_json::json!({
            "version": FILE_VERSION,
            "connections": records.iter().collect::<std::collections::BTreeMap<&String, &McpConnectionRecord>>(),
        });
        let expected = serde_json::to_string_pretty(&doc).unwrap();
        let before = crate::settings::storage::opt_in_fsync_calls();
        write_records(&path, &records).unwrap();
        assert_eq!(
            crate::settings::storage::opt_in_fsync_calls(),
            before + 1,
            "the registry write must flush the temp file before the rename"
        );
        assert_eq!(std::fs::read_to_string(&path).unwrap(), expected);
    }

    fn record(connection_id: &str) -> McpConnectionRecord {
        McpConnectionRecord {
            connection_id: connection_id.to_string(),
            service_id: "acme".to_string(),
            endpoint: "https://acme.example/mcp".to_string(),
            label: "Acme".to_string(),
            status: McpConnectionStatus::Connected,
            created_at: 1,
            updated_at: 1,
            verified_at: None,
            tool_count: None,
            last_error: None,
            attempt_id: None,
        }
    }

    /// A file of another version (a newer build wrote it) is refused: the
    /// read-only open reports it, and `remove` fails and writes nothing.
    #[test]
    fn another_version_is_refused_and_never_rewritten() {
        let dir = tempfile::tempdir().unwrap();
        let path = dir.path().join("mcp-connections.json");
        let content = serde_json::to_string_pretty(&serde_json::json!({
            "version": 2,
            "connections": { "a": record("a"), "b": record("b") },
        }))
        .unwrap();
        std::fs::write(&path, &content).unwrap();
        let reason = format!(
            "{} has version 2; this build reads only version 1",
            path.display()
        );

        let mut store = McpConnectionStore::open(&path);
        assert_eq!(
            (store.records(), store.load_error()),
            (Vec::new(), Some(reason.as_str()))
        );
        let error = store.remove("a").unwrap_err().to_string();
        assert_eq!(error, reason);
        assert_eq!(std::fs::read_to_string(&path).unwrap(), content);
    }

    /// A file that is not JSON is refused: `upsert` fails and writes
    /// nothing.
    #[test]
    fn a_corrupt_file_is_refused_and_never_rewritten() {
        let dir = tempfile::tempdir().unwrap();
        let path = dir.path().join("mcp-connections.json");
        let content = "{\"version\": 1, \"connections\": {";
        std::fs::write(&path, content).unwrap();

        let mut store = McpConnectionStore::open(&path);
        assert!(store.load_error().is_some());
        assert!(store.upsert(&record("c")).is_err());
        assert_eq!(std::fs::read_to_string(&path).unwrap(), content);
    }

    /// A good file: `remove` changes only its own record.
    #[test]
    fn remove_keeps_every_other_record() {
        let dir = tempfile::tempdir().unwrap();
        let path = dir.path().join("mcp-connections.json");
        let mut store = McpConnectionStore::open(&path);
        store.upsert(&record("a")).unwrap();
        store.upsert(&record("b")).unwrap();

        let mut other = McpConnectionStore::open(&path);
        other.remove("a").unwrap();
        store.load();
        assert_eq!(
            (store.records(), store.load_error()),
            (vec![record("b")], None)
        );
    }
}
