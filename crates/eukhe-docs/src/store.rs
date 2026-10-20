//! Session-scoped snapshots, clipboard registers, and no-op loop state.

use std::{
    collections::{BTreeSet, HashMap},
    hash::{DefaultHasher, Hash, Hasher},
    path::{Path, PathBuf},
    sync::{Arc, LazyLock},
};

use parking_lot::Mutex;
use regex::Regex;
use twox_hash::XxHash32;

/// Retained path count before LRU eviction.
pub const DEFAULT_MAX_PATHS: usize = 256;
/// Full-file versions retained per path.
pub const DEFAULT_MAX_VERSIONS_PER_PATH: usize = 4;
/// Global ceiling on retained snapshot text, measured in UTF-16 code units.
pub const DEFAULT_MAX_TOTAL_BYTES: usize = 64 * 1024 * 1024;
/// The one size limit of the documents tools: a larger file gets no tag
/// (so `edit` cannot change it) and grep searches only its first this many
/// bytes. Every message that names the limit formats it from here.
pub const MAX_SNAPSHOT_FILE_BYTES: u64 = 4 * 1024 * 1024;
/// Consecutive identical no-ops before the guard escalates.
pub const NOOP_HARD_LIMIT: u32 = 3;

/// One full-file version observed at a point in time.
#[derive(Debug, Clone)]
pub struct Snapshot {
    /// Canonical path this version belongs to.
    pub path: PathBuf,
    /// Full LF-normalized, BOM-stripped text.
    pub text: Arc<str>,
    /// Four-character content tag.
    pub hash: String,
    /// Lines displayed from this version, when provenance was recorded.
    pub seen_lines: Option<BTreeSet<u32>>,
}

/// Clipboard registers threaded through one patch application.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct Clipboard {
    /// Latest anonymous cut.
    pub lines: Option<Vec<String>>,
    /// Named registers, retained between batches.
    pub named: Option<HashMap<String, Vec<String>>>,
    /// Anonymous cuts not yet consumed.
    pub pending_anon_cuts: Option<Vec<String>>,
}

impl Clipboard {
    /// Start a batch with named registers only.
    #[must_use]
    pub fn start_batch(source: &Self) -> Self {
        Self {
            named: source.named.clone(),
            ..Self::default()
        }
    }

    /// Make a transactional deep copy.
    #[must_use]
    pub fn fork(&self) -> Self {
        self.clone()
    }

    /// Merge named registers from a completed transaction.
    pub fn commit_from(&mut self, fork: &Self) {
        let Some(named) = &fork.named else { return };
        self.named
            .get_or_insert_with(HashMap::new)
            .extend(named.clone());
    }
}

/// Compute the four-hex uppercase hashline content tag.
#[must_use]
pub fn file_hash(text: &str) -> String {
    let mut normalized = String::with_capacity(text.len());
    for segment in text.split_inclusive('\n') {
        let (line, newline) = segment
            .strip_suffix('\n')
            .map_or((segment, ""), |line| (line, "\n"));
        normalized.push_str(line.trim_end_matches([' ', '\t', '\r']));
        normalized.push_str(newline);
    }
    format!(
        "{:04X}",
        XxHash32::oneshot(0, normalized.as_bytes()) & 0xffff
    )
}

/// Compute a process-local 64-bit key for raw patch input.
#[must_use]
pub fn payload_hash(text: &str) -> u64 {
    let mut hasher = DefaultHasher::new();
    text.hash(&mut hasher);
    hasher.finish()
}

static SEEN_PREFIX: LazyLock<Regex> =
    LazyLock::new(|| Regex::new(r"^[ *]?(\d+)(?:-(\d+))?:").expect("valid hashline prefix regex"));

/// Parse displayed boundary line numbers from a hashline-formatted body.
#[must_use]
pub fn seen_lines_from_body(body: &str) -> Vec<u32> {
    let mut seen = Vec::new();
    for row in body.split('\n') {
        let Some(captures) = SEEN_PREFIX.captures(row) else {
            continue;
        };
        if let Ok(line) = captures[1].parse() {
            seen.push(line);
        }
        if let Some(end) = captures
            .get(2)
            .and_then(|value| value.as_str().parse().ok())
        {
            seen.push(end);
        }
    }
    seen
}

struct PathHistory {
    versions: Vec<Snapshot>,
    /// Digests of the raw bytes the session saw of this path, newest
    /// first: what `write` may replace.
    seen_bytes: Vec<u64>,
    touched: u64,
}

impl PathHistory {
    fn new(touched: u64) -> Self {
        Self {
            versions: Vec::new(),
            seen_bytes: Vec::new(),
            touched,
        }
    }
}

/// Raw-byte digests kept per path: the versions `write` may replace.
const SEEN_BYTES_PER_PATH: usize = 8;

fn bytes_digest(bytes: &[u8]) -> u64 {
    twox_hash::XxHash64::oneshot(0, bytes)
}

struct StoreState {
    histories: HashMap<PathBuf, PathHistory>,
    clipboard: Clipboard,
    noop: HashMap<PathBuf, (u64, u32)>,
    clock: u64,
    max_paths: usize,
    max_versions: usize,
    max_total_units: usize,
}

impl Default for StoreState {
    fn default() -> Self {
        Self {
            histories: HashMap::new(),
            clipboard: Clipboard::default(),
            noop: HashMap::new(),
            clock: 0,
            max_paths: DEFAULT_MAX_PATHS,
            max_versions: DEFAULT_MAX_VERSIONS_PER_PATH,
            max_total_units: DEFAULT_MAX_TOTAL_BYTES,
        }
    }
}

/// Thread-safe state shared for the lifetime of an edit session.
#[derive(Default, Clone)]
pub struct EditStore {
    inner: Arc<Mutex<StoreState>>,
}

impl EditStore {
    /// Construct a store with production retention limits.
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// Construct a store with explicit limits.
    #[must_use]
    pub fn with_limits(max_paths: usize, max_versions: usize, max_total_units: usize) -> Self {
        let state = StoreState {
            max_paths,
            max_versions,
            max_total_units,
            ..StoreState::default()
        };
        Self {
            inner: Arc::new(Mutex::new(state)),
        }
    }

    /// Record normalized text under a canonical path and return its tag.
    #[allow(
        clippy::must_use_candidate,
        reason = "callers record for the side effect and read the tag only when they render it"
    )]
    pub fn record(&self, path: &Path, text: &str, seen_lines: Option<&[u32]>) -> String {
        let hash = file_hash(text);
        let mut state = self.inner.lock();
        state.clock = state.clock.wrapping_add(1);
        let touched = state.clock;
        let max_versions = state.max_versions;
        let history = state
            .histories
            .entry(path.to_owned())
            .or_insert_with(|| PathHistory::new(touched));
        history.touched = touched;
        if let Some(index) = history
            .versions
            .iter()
            .position(|version| version.hash == hash && &*version.text == text)
        {
            let mut snapshot = history.versions.remove(index);
            merge_seen(&mut snapshot, seen_lines);
            history.versions.insert(0, snapshot);
        } else if max_versions > 0 {
            let mut snapshot = Snapshot {
                path: path.to_owned(),
                text: Arc::from(text),
                hash: hash.clone(),
                seen_lines: None,
            };
            merge_seen(&mut snapshot, seen_lines);
            history.versions.insert(0, snapshot);
            history.versions.truncate(max_versions);
        }
        evict(&mut state);
        hash
    }

    /// Record that the session saw `bytes`, the raw content of the file at
    /// canonical `path` (a read, a search, or its own write): `write` may
    /// replace that version.
    pub fn saw_bytes(&self, path: &Path, bytes: &[u8]) {
        let digest = bytes_digest(bytes);
        let mut state = self.inner.lock();
        state.clock = state.clock.wrapping_add(1);
        let touched = state.clock;
        let history = state
            .histories
            .entry(path.to_owned())
            .or_insert_with(|| PathHistory::new(touched));
        history.touched = touched;
        history.seen_bytes.retain(|seen| *seen != digest);
        history.seen_bytes.insert(0, digest);
        history.seen_bytes.truncate(SEEN_BYTES_PER_PATH);
        evict(&mut state);
    }

    /// Whether the session saw `bytes` as the content of `path` (see
    /// [`EditStore::saw_bytes`]).
    #[must_use]
    pub fn has_seen_bytes(&self, path: &Path, bytes: &[u8]) -> bool {
        let digest = bytes_digest(bytes);
        let mut state = self.inner.lock();
        touch(&mut state, path);
        state
            .histories
            .get(path)
            .is_some_and(|history| history.seen_bytes.contains(&digest))
    }

    /// Union displayed lines into the most recent version matching a tag.
    pub fn record_seen_lines(&self, path: &Path, hash: &str, lines: &[u32]) {
        let mut state = self.inner.lock();
        touch(&mut state, path);
        if let Some(version) = state
            .histories
            .get_mut(path)
            .and_then(|h| h.versions.iter_mut().find(|v| v.hash == hash))
        {
            merge_seen(version, Some(lines));
        }
    }

    /// Return the current version and refresh path recency.
    #[must_use]
    pub fn head(&self, path: &Path) -> Option<Snapshot> {
        let mut state = self.inner.lock();
        touch(&mut state, path);
        state.histories.get(path)?.versions.first().cloned()
    }

    /// Return the most recent version matching a tag and refresh path recency.
    #[must_use]
    pub fn by_hash(&self, path: &Path, hash: &str) -> Option<Snapshot> {
        let mut state = self.inner.lock();
        touch(&mut state, path);
        state
            .histories
            .get(path)?
            .versions
            .iter()
            .find(|v| v.hash == hash)
            .cloned()
    }

    /// Return the version with exactly equal text and refresh path recency.
    #[must_use]
    pub fn by_content(&self, path: &Path, text: &str) -> Option<Snapshot> {
        let mut state = self.inner.lock();
        touch(&mut state, path);
        state
            .histories
            .get(path)?
            .versions
            .iter()
            .find(|v| &*v.text == text)
            .cloned()
    }

    /// Return every retained version matching a tag.
    #[must_use]
    pub fn find_by_hash(&self, hash: &str) -> Vec<Snapshot> {
        let state = self.inner.lock();
        state
            .histories
            .values()
            .flat_map(|h| h.versions.iter())
            .filter(|v| v.hash == hash)
            .cloned()
            .collect()
    }

    /// Remove one path's history.
    pub fn invalidate(&self, path: &Path) {
        self.inner.lock().histories.remove(path);
    }

    /// Move source history and provenance to a destination path.
    pub fn relocate(&self, from: &Path, to: &Path) {
        let mut state = self.inner.lock();
        state.clock = state.clock.wrapping_add(1);
        let touched = state.clock;
        let max_versions = state.max_versions;
        let Some(mut source) = state.histories.remove(from) else {
            return;
        };
        for version in &mut source.versions {
            to.clone_into(&mut version.path);
        }
        let mut merged = source.versions;
        if let Some(destination) = state.histories.remove(to) {
            merged.extend(destination.versions);
        }
        let mut hashes = BTreeSet::new();
        merged.retain(|version| hashes.insert(version.hash.clone()));
        merged.truncate(max_versions);
        let mut history = PathHistory::new(touched);
        history.versions = merged;
        state.histories.insert(to.to_owned(), history);
        evict(&mut state);
    }

    /// Remove all snapshots, clipboard state, and no-op counters.
    pub fn clear(&self) {
        *self.inner.lock() = StoreState::default();
    }

    /// Start a clipboard batch with persisted named registers.
    #[must_use]
    pub fn start_clipboard_batch(&self) -> Clipboard {
        Clipboard::start_batch(&self.inner.lock().clipboard)
    }

    /// Publish named registers from a batch fork.
    pub fn commit_clipboard(&self, fork: &Clipboard) {
        self.inner.lock().clipboard.commit_from(fork);
    }

    /// Record an identical no-op and return its consecutive count and escalation
    /// state.
    #[must_use]
    pub fn record_noop(&self, path: &Path, payload: u64) -> (u32, bool) {
        let mut state = self.inner.lock();
        let count = state
            .noop
            .get(path)
            .filter(|(hash, _)| *hash == payload)
            .map_or(1, |(_, count)| count + 1);
        state.noop.insert(path.to_owned(), (payload, count));
        (count, count >= NOOP_HARD_LIMIT)
    }

    /// Clear one path's no-op counter.
    pub fn reset_noop(&self, path: &Path) {
        self.inner.lock().noop.remove(path);
    }
}

fn merge_seen(snapshot: &mut Snapshot, lines: Option<&[u32]>) {
    let Some(lines) = lines else { return };
    snapshot
        .seen_lines
        .get_or_insert_with(BTreeSet::new)
        .extend(lines.iter().copied());
}

fn touch(state: &mut StoreState, path: &Path) {
    if state.histories.contains_key(path) {
        state.clock = state.clock.wrapping_add(1);
        state
            .histories
            .get_mut(path)
            .expect("checked above")
            .touched = state.clock;
    }
}

fn retained_units(state: &StoreState) -> usize {
    state
        .histories
        .values()
        .map(|history| {
            1 + history
                .versions
                .iter()
                .map(|v| v.text.encode_utf16().count())
                .sum::<usize>()
        })
        .sum()
}

fn evict(state: &mut StoreState) {
    while state.histories.len() > state.max_paths || retained_units(state) > state.max_total_units {
        let Some(oldest) = state
            .histories
            .iter()
            .min_by_key(|(_, history)| history.touched)
            .map(|(path, _)| path.clone())
        else {
            break;
        };
        state.histories.remove(&oldest);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn file_hash_matches_typescript() {
        assert_eq!(file_hash("a \n b\t\r\nc"), "80BA");
        assert_eq!(file_hash("hello\n"), "5BF9");
        assert_eq!(file_hash(""), "5D05");
    }

    #[test]
    fn snapshots_deduplicate_promote_and_union_seen_lines() {
        let store = EditStore::new();
        let path = Path::new("a.ts");
        let first = store.record(path, "one", Some(&[1]));
        store.record(path, "two", Some(&[2]));
        assert_eq!(&*store.head(path).unwrap().text, "two");
        assert_eq!(store.record(path, "one", Some(&[3])), first);
        let head = store.head(path).unwrap();
        assert_eq!(&*head.text, "one");
        assert_eq!(head.seen_lines.unwrap(), BTreeSet::from([1, 3]));
    }

    #[test]
    fn version_and_lru_limits_are_enforced() {
        let store = EditStore::with_limits(2, 2, usize::MAX);
        for text in ["one", "two", "three"] {
            store.record(Path::new("a"), text, None);
        }
        assert!(store.by_content(Path::new("a"), "one").is_none());
        store.record(Path::new("b"), "b", None);
        assert!(store.head(Path::new("a")).is_some());
        store.record(Path::new("c"), "c", None);
        assert!(store.head(Path::new("b")).is_none());
        assert!(store.head(Path::new("a")).is_some());
    }

    #[test]
    fn total_limit_counts_utf16_units() {
        let store = EditStore::with_limits(10, 4, 4);
        store.record(Path::new("old"), "😀", None); // history cost: 1 + 2 units
        store.record(Path::new("new"), "ab", None); // total 6, evicts old
        assert!(store.head(Path::new("old")).is_none());
    }

    #[test]
    fn relocation_merges_and_rewrites_paths() {
        let store = EditStore::new();
        let shared = store.record(Path::new("from"), "same", Some(&[1]));
        store.record(Path::new("to"), "older", None);
        store.relocate(Path::new("from"), Path::new("to"));
        assert!(store.head(Path::new("from")).is_none());
        assert_eq!(
            store.by_hash(Path::new("to"), &shared).unwrap().path,
            Path::new("to")
        );
    }

    #[test]
    fn parses_seen_line_boundaries_only() {
        assert_eq!(
            seen_lines_from_body("1:x\n*20-30:{ … }\n nope\n 7:y"),
            vec![1, 20, 30, 7]
        );
    }

    #[test]
    fn clipboard_batch_fork_and_commit_preserve_named_only() {
        let store = EditStore::new();
        let initial = Clipboard {
            named: Some(HashMap::from([("a".into(), vec!["one".into()])])),
            lines: Some(vec!["anonymous".into()]),
            ..Default::default()
        };
        store.commit_clipboard(&initial);
        let mut batch = store.start_clipboard_batch();
        assert!(batch.lines.is_none());
        let mut fork = batch.fork();
        fork.named
            .as_mut()
            .unwrap()
            .insert("b".into(), vec!["two".into()]);
        store.commit_clipboard(&fork);
        batch = store.start_clipboard_batch();
        assert_eq!(batch.named.unwrap().len(), 2);
    }

    #[test]
    fn noop_counter_resets_for_new_payload_and_commit() {
        let store = EditStore::new();
        let path = Path::new("a");
        let hash = payload_hash("edit");
        assert_eq!(store.record_noop(path, hash), (1, false));
        assert_eq!(store.record_noop(path, hash), (2, false));
        assert_eq!(store.record_noop(path, hash), (3, true));
        assert_eq!(
            store.record_noop(path, payload_hash("different")),
            (1, false)
        );
        store.reset_noop(path);
        assert_eq!(store.record_noop(path, hash), (1, false));
    }
}
