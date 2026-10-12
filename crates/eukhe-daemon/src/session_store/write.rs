//! The unit-test fixture builder: an in-memory legacy session (header plus
//! an appended entry chain) and the plain full-file write that seeds the
//! legacy JSONL files the read-only readers, scans, and import consume.
//! Production never writes legacy session files.

use super::{
    fs, read::session_header_line, Context, HashMap, Map, PathBuf, Result, SessionEntry,
    SessionFile, SessionHeader, Value, Write,
};

const CURRENT_SESSION_VERSION: u32 = 3;

fn new_entry_id(used: &HashMap<String, usize>) -> String {
    loop {
        let id = uuid::Uuid::new_v4().simple().to_string()[..8].to_string();
        if !used.contains_key(&id) {
            return id;
        }
    }
}

impl SessionFile {
    /// A fresh in-memory session with a new v7 id and no path.
    pub fn create(cwd: &str, parent_session: Option<&str>, rlm_depth: u32) -> Self {
        let header = SessionHeader {
            version: Some(CURRENT_SESSION_VERSION),
            id: uuid::Uuid::now_v7().to_string(),
            timestamp: crate::util::now_iso(),
            cwd: cwd.to_string(),
            parent_session: parent_session.map(str::to_string),
            rlm_depth: Some(u64::from(rlm_depth)),
            git: None,
            rest: Map::default(),
        };
        SessionFile {
            path: PathBuf::new(),
            header,
            entries: Vec::new(),
            by_id: HashMap::new(),
            leaf_id: None,
            window: None,
            anthropic_warning_shown: false,
        }
    }

    pub fn append_entry(&mut self, type_: &str, fields: Value) -> String {
        let id = if self.window.is_some() {
            uuid::Uuid::new_v4().to_string()
        } else {
            new_entry_id(&self.by_id)
        };
        let entry = SessionEntry {
            type_: type_.to_string(),
            id: id.clone(),
            parent_id: self.leaf_id.clone(),
            timestamp: crate::util::now_iso(),
            fields,
        };
        self.push_index(entry);
        id
    }

    pub fn append_message(&mut self, message: &Value) -> String {
        self.append_entry("message", serde_json::json!({ "message": message }))
    }

    pub fn append_session_state(&mut self, status: &str) -> String {
        self.append_entry(
            "session_state",
            serde_json::json!({ "state": { "status": status } }),
        )
    }

    pub fn append_session_info(&mut self, name: &str) -> String {
        self.append_entry("session_info", serde_json::json!({ "name": name.trim() }))
    }

    pub fn append_model_change(&mut self, provider: &str, model_id: &str) -> String {
        self.append_entry(
            "model_change",
            serde_json::json!({ "provider": provider, "modelId": model_id }),
        )
    }

    pub fn append_thinking_level_change(&mut self, level: &str) -> String {
        self.append_entry(
            "thinking_level_change",
            serde_json::json!({ "thinkingLevel": level }),
        )
    }

    /// Write the fixture file (header + every entry) at `path`, creating
    /// the parent directory.
    ///
    /// # Errors
    ///
    /// Returns an error when the store only holds a window, the path is
    /// empty, or the directory or file write fails.
    pub fn rewrite(&self) -> Result<()> {
        anyhow::ensure!(
            self.window.is_none(),
            "full history required before writing a fixture session"
        );
        anyhow::ensure!(
            !self.path.as_os_str().is_empty(),
            "fixture session has no path"
        );
        if let Some(parent) = self.path.parent() {
            fs::create_dir_all(parent)
                .with_context(|| format!("create session dir {}", parent.display()))?;
        }
        let mut body = Vec::new();
        write_line(&mut body, &session_header_line(&self.header))?;
        for entry in &self.entries {
            write_line(&mut body, entry)?;
        }
        fs::write(&self.path, body).with_context(|| format!("write {}", self.path.display()))
    }

    /// Point the fixture at a concrete file path, preserving entries.
    pub fn set_path(&mut self, path: PathBuf) {
        self.path = path;
    }
}

fn write_line<T: serde::Serialize>(writer: &mut impl Write, value: &T) -> Result<()> {
    let mut line = serde_json::to_string(value)?;
    line.push('\n');
    writer.write_all(line.as_bytes())?;
    Ok(())
}
