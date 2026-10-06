//! The shared JSONL diagnostic log (TS `getLogger` entries in
//! `<agentDir>/logs/agent.jsonl`): one JSON object per line with the
//! reserved `ts`/`level`/`component`/`msg`/`pid` keys, rotated to `.old`
//! past the TS cap. Writes are best-effort: logging never fails the
//! operation being logged.

use std::path::{Path, PathBuf};

use serde_json::{json, Map, Value};

use crate::session::manager::format_iso;

/// TS `AGENT_LOG_MAX_BYTES` (`logging.ts`): the log rotates at 20 MiB.
const AGENT_LOG_MAX_BYTES: u64 = 20 * 1024 * 1024;

/// An entry's severity (TS `Logger.info`/`Logger.warn`).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AgentLogLevel {
    Info,
    Warn,
}

impl AgentLogLevel {
    fn wire_name(self) -> &'static str {
        match self {
            AgentLogLevel::Info => "info",
            AgentLogLevel::Warn => "warn",
        }
    }
}

/// One component's handle on the shared log (TS `getLogger(component)`).
#[derive(Debug, Clone)]
pub struct AgentLog {
    path: PathBuf,
    max_bytes: u64,
    component: &'static str,
}

impl AgentLog {
    /// The log at `<agentDir>/logs/agent.jsonl` with the TS rotation cap.
    #[must_use]
    pub fn new(agent_dir: &Path, component: &'static str) -> Self {
        Self {
            path: agent_dir.join("logs").join("agent.jsonl"),
            max_bytes: AGENT_LOG_MAX_BYTES,
            component,
        }
    }

    /// The log at an explicit path (tests).
    #[cfg(test)]
    pub(crate) fn at(path: impl Into<PathBuf>, component: &'static str) -> Self {
        Self {
            path: path.into(),
            max_bytes: AGENT_LOG_MAX_BYTES,
            component,
        }
    }

    /// Append one entry: caller fields first, then the reserved keys and
    /// the sink's `pid` context, so an entry is never misclassified. `ts`
    /// is the ISO-8601 UTC timestamp (TS `new Date().toISOString()`).
    pub fn log(&self, level: AgentLogLevel, msg: &str, fields: Map<String, Value>) {
        let now = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap_or_default();
        let mut entry = fields;
        entry.insert("ts".to_string(), json!(format_iso(now.as_millis() as i64)));
        entry.insert("level".to_string(), json!(level.wire_name()));
        entry.insert("component".to_string(), json!(self.component));
        entry.insert("msg".to_string(), json!(msg));
        entry.insert("pid".to_string(), json!(std::process::id()));
        self.append_rotating_log(&format!("{}\n", Value::Object(entry)));
    }

    /// TS `appendRotatingLog`: create the directory, rotate to `.old` past
    /// the cap, append the line. A failure is traced, never raised: a
    /// read-only or missing log dir must not break the logged operation.
    fn append_rotating_log(&self, line: &str) {
        use std::io::Write;
        let append = || -> std::io::Result<()> {
            std::fs::create_dir_all(self.path.parent().unwrap_or_else(|| Path::new(".")))?;
            // TS keeps appending when the rotate fails (the rename is the
            // only fallible half of its try/catch).
            if let Err(error) = self.rotate_if_needed() {
                tracing::debug!(path = %self.path.display(), %error, "agent log rotation failed");
            }
            let mut file = std::fs::OpenOptions::new()
                .create(true)
                .append(true)
                .open(&self.path)?;
            file.write_all(line.as_bytes())?;
            file.flush()
        };
        if let Err(error) = append() {
            tracing::debug!(path = %self.path.display(), %error, "agent log append failed");
        }
    }

    fn rotate_if_needed(&self) -> std::io::Result<()> {
        let size = match std::fs::metadata(&self.path) {
            Ok(meta) => meta.len(),
            Err(err) if err.kind() == std::io::ErrorKind::NotFound => return Ok(()),
            Err(err) => return Err(err),
        };
        if size <= self.max_bytes {
            return Ok(());
        }
        // The rename replaces any prior `.old`.
        std::fs::rename(&self.path, self.path.with_extension("jsonl.old"))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn entries_carry_the_reserved_keys_after_the_caller_fields() {
        let dir = tempfile::tempdir().expect("temp dir");
        let path = dir.path().join("logs").join("agent.jsonl");
        let log = AgentLog::at(&path, "coding-agent.test");
        let mut fields = Map::new();
        fields.insert("level".to_string(), json!("spoofed"));
        fields.insert("path".to_string(), json!("/x.json"));
        log.log(AgentLogLevel::Warn, "theme failed", fields);
        let raw = std::fs::read_to_string(&path).expect("log written");
        let mut entry: Value = serde_json::from_str(raw.trim()).expect("one JSON line");
        let object = entry.as_object_mut().expect("object entry");
        assert!(object.remove("ts").is_some_and(|ts| ts.is_string()));
        assert_eq!(
            entry,
            json!({
                "level": "warn",
                "component": "coding-agent.test",
                "msg": "theme failed",
                "pid": std::process::id(),
                "path": "/x.json",
            })
        );
    }
}
