//! The id mint (moved with its concern): the session id minters and the
//! session file path.

use super::{HashMap, Path, PathBuf};

pub(super) fn generate_id(existing: &HashMap<String, usize>) -> String {
    for _ in 0..100 {
        let id = uuid::Uuid::new_v4().simple().to_string()[..8].to_string();
        if !existing.contains_key(&id) {
            return id;
        }
    }
    uuid::Uuid::new_v4().to_string()
}

pub(super) fn create_session_id() -> String {
    create_uuid_v7()
}

/// `UUIDv7` (timestamp-ordered, like the TS `createSessionId`).
fn create_uuid_v7() -> String {
    uuid::Uuid::now_v7().to_string()
}

#[must_use]
pub fn get_session_file_path(session_dir: &Path, session_id: &str) -> PathBuf {
    session_dir.join(format!("{session_id}.jsonl"))
}
