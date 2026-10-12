//! The lifecycle concern (moved with its concern): the constructors and
//! the load/new/adopt arm. Loading a legacy session file is read-only: a
//! migration or an RLM-depth repair rewrites only the in-memory header.

use super::{
    create_session_id, format_iso_now, is_valid_rlm_depth, load_entries_from_file,
    migrate_to_current_version, resolve_session_rlm_depth, root_rlm_depth_from_env, FileEntry,
    HashMap, NewSessionOptions, Path, PathBuf, SessionHeader, SessionManager,
    CURRENT_SESSION_VERSION,
};

impl SessionManager {
    fn new_with(cwd: PathBuf, session_dir: PathBuf) -> Self {
        let mut manager = Self {
            session_id: String::new(),
            session_file: None,
            session_dir,
            cwd,
            session_dir_backed: false,
            append_ownership: super::window::AppendOwnership::Unleased,
            file_entries: Vec::new(),
            window: None,
            by_id: HashMap::new(),
            labels_by_id: HashMap::new(),
            label_timestamps_by_id: HashMap::new(),
            leaf_id: None,
        };
        manager.new_session(&NewSessionOptions::default());
        manager
    }

    /// Create an in-memory manager rooted at `cwd`.
    #[must_use]
    pub fn in_memory(cwd: &Path) -> Self {
        Self::new_with(cwd.to_path_buf(), cwd.to_path_buf())
    }

    /// Create an in-memory manager pinned to a session's own directory:
    /// the daemon worker owns the durable session and mirrors the entries,
    /// but the session's identity (its directory, the local harness
    /// state's home) stays the session's own.
    #[must_use]
    pub fn in_memory_in_session_dir(cwd: &Path, session_dir: &Path) -> Self {
        let mut manager = Self::new_with(cwd.to_path_buf(), session_dir.to_path_buf());
        manager.session_dir_backed = true;
        manager
    }

    /// Whether the manager carries a session directory of its own: a
    /// fresh in-memory manager holds only the cwd fallback, while the
    /// daemon's mirrored engine session does. Session-owned artifacts (the
    /// local harness state) need it.
    #[must_use]
    pub fn has_session_dir(&self) -> bool {
        self.session_dir_backed
    }

    /// Open only the compacted active window off the async executor. Use
    /// `active_context` until `ensure_full_history` completes before accessing
    /// historical entries, navigation, or exporting.
    ///
    /// # Errors
    ///
    /// Returns an error when the windowed session store cannot be opened.
    #[cfg(test)]
    pub async fn open_windowed(
        cwd: &Path,
        session_dir: &Path,
        session_file: &Path,
    ) -> anyhow::Result<Self> {
        let cwd = cwd.to_owned();
        let session_dir = session_dir.to_owned();
        let path = session_file.to_owned();
        tokio::task::spawn_blocking(move || {
            let mut manager = Self::in_memory_in_session_dir(&cwd, &session_dir);
            let Some(window) = super::window::WindowedSessionStore::open(&path)? else {
                manager.set_session_file(path, None);
                return Ok(manager);
            };
            manager.session_id = match window.entries().first() {
                Some(FileEntry::Header { header }) => header.id.clone(),
                _ => unreachable!("window validates header"),
            };
            manager.session_file = Some(path);
            manager.adopt_window(window);
            Ok(manager)
        })
        .await?
    }

    /// Adopt a verified read-only window: the walk's parsed trees move in
    /// (no `to_vec` clone), and the raw JSONL lines drop here — the file
    /// itself is the raw copy, and a second resident typed copy plus the
    /// raw lines measured ~29.5MiB of wire-equivalent duplication on the
    /// 10MiB canonical fixture (worker-rss census, 2026-09-26). The window
    /// stays attached for its snapshot/settings/metadata state;
    /// `active_context` walks `file_entries` with the window's settings
    /// overlay, so the served context is unchanged.
    pub fn adopt_window(&mut self, mut window: super::window::WindowedSessionStore) {
        let (entries, _raw_entries) = window.take_retained();
        self.file_entries = entries;
        self.build_index();
        self.leaf_id = Some(window.leaf_id().to_owned());
        self.window = Some(window);
    }

    /// Whether this manager may serve its retained rows as the historical
    /// snapshot. Only a caller holding this session's runtime lease may
    /// raise it (no other writer can extend the file), and every other
    /// manager keeps the unleased default that re-reads the file.
    pub fn set_append_ownership(&mut self, ownership: super::window::AppendOwnership) {
        self.append_ownership = ownership;
    }

    /// Load a legacy session file into memory (read-only). An empty or
    /// headerless file starts a fresh in-memory session at that path; a
    /// missing file does the same. Version migration and the forked
    /// header's RLM-depth resolution apply to the in-memory entries only.
    pub fn set_session_file(
        &mut self,
        session_file: PathBuf,
        preloaded_entries: Option<Vec<FileEntry>>,
    ) {
        self.window = None;
        let mut entries =
            preloaded_entries.unwrap_or_else(|| load_entries_from_file(&session_file));
        if entries.is_empty() {
            self.new_session(&NewSessionOptions::default());
            self.session_file = Some(session_file);
            return;
        }
        let header_id = entries.iter().find_map(|entry| match entry {
            FileEntry::Header { header } => Some(header.id.clone()),
            _ => None,
        });
        self.session_id = header_id.unwrap_or_else(create_session_id);
        migrate_to_current_version(&mut entries);
        if let Some(FileEntry::Header { header }) = entries.first_mut() {
            if header.parent_session.is_some() && !is_valid_rlm_depth(header.rlm_depth) {
                header.rlm_depth = Some(resolve_session_rlm_depth(header, &session_file));
            }
        }
        self.file_entries = entries;
        self.build_index();
        self.session_file = Some(session_file);
    }

    /// Start a new in-memory session: a fresh header (the requested id, or
    /// a minted one) and an empty entry chain.
    pub fn new_session(&mut self, options: &NewSessionOptions) {
        self.session_id = options.id.clone().unwrap_or_else(create_session_id);
        let rlm_depth = match options.rlm_depth {
            Some(depth) => Some(depth),
            None => options
                .parent_session
                .as_deref()
                .map(|_| 0)
                .or(Some(root_rlm_depth_from_env())),
        };
        let header = FileEntry::Header {
            header: SessionHeader {
                id: self.session_id.clone(),
                version: Some(CURRENT_SESSION_VERSION),
                timestamp: format_iso_now(),
                cwd: self.cwd.display().to_string(),
                parent_session: options.parent_session.clone(),
                rlm_depth,
                git: None,
                rest: eukhe_types::JsonMap::new(),
            },
        };
        self.file_entries = vec![header];
        self.window = None;
        self.by_id.clear();
        self.labels_by_id.clear();
        self.label_timestamps_by_id.clear();
        self.leaf_id = None;
    }

    /// Adopt a durable branch as this session's entries (TS
    /// `createBranchedSession`'s in-memory case, and the engine's
    /// post-navigation context rebuild): keeps the header, replaces every
    /// entry with the given chain, and re-indexes so the leaf is the last
    /// adopted entry.
    pub fn adopt_entries(&mut self, entries: Vec<FileEntry>) {
        // The caller supplies the complete selected branch after explicit navigation.
        self.window = None;
        let header = self
            .file_entries
            .iter()
            .position(|entry| matches!(entry, FileEntry::Header { .. }));
        match header {
            Some(index) => {
                self.file_entries.truncate(index + 1);
                self.file_entries.extend(entries);
            }
            None => {
                self.file_entries = entries;
            }
        }
        self.build_index();
    }
}
