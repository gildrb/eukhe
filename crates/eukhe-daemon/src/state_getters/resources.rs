//! The session's loaded resources on the wire (moved with their concern):
//! the `get_commands` entries (TS `createAgentConnectionCommands`) and the
//! `get_resource_snapshot` block (TS `createAgentConnectionResourceSnapshot`),
//! with the artifact references (TS `createArtifactReference`) the snapshot
//! rows carry.

use std::fmt::Write as _;
use std::path::Path;

use eukhe_core::resources::LoadedResources;
use serde_json::{json, Value};
use sha2::{Digest, Sha256};

/// The connection commands: prompt templates, then skills (the TS order).
pub(crate) fn connection_commands(resources: &LoadedResources) -> Vec<Value> {
    let mut commands = Vec::with_capacity(resources.prompts.len() + resources.skills.len());
    for template in &resources.prompts {
        let mut entry = json!({
            "name": template.name,
            "source": "prompt",
            "sourceInfo": template.source_info,
        });
        if let Some(hint) = &template.argument_hint {
            entry["argumentHint"] = json!(hint);
        }
        if !template.description.is_empty() {
            entry["description"] = json!(template.description);
        }
        commands.push(entry);
    }
    for skill in &resources.skills {
        let mut entry = json!({
            "name": format!("skill:{}", skill.name),
            "source": "skill",
            "sourceInfo": skill.source_info,
        });
        if !skill.description.is_empty() {
            entry["description"] = json!(skill.description);
        }
        commands.push(entry);
    }
    commands
}

/// The resource snapshot: context files, skills, and prompt templates with
/// their artifact references (no themes on this port).
pub(crate) fn resource_snapshot(
    resources: &LoadedResources,
    session_id: &str,
    cwd: &Path,
) -> Value {
    let cwd = cwd.display().to_string();
    let skills: Vec<Value> = resources
        .skills
        .iter()
        .map(|skill| {
            let file_path = skill.file_path.display().to_string();
            let mut entry = json!({
                "name": skill.name,
                "filePath": file_path,
                "sourceInfo": skill.source_info,
            });
            if !skill.description.is_empty() {
                entry["description"] = json!(skill.description);
            }
            if let Some(artifact) = artifact_reference(session_id, &cwd, "skill", &file_path) {
                entry["artifact"] = artifact;
            }
            entry
        })
        .collect();
    let prompts: Vec<Value> = resources
        .prompts
        .iter()
        .map(|template| {
            let mut entry = json!({
                "name": template.name,
                "filePath": template.file_path,
                "sourceInfo": template.source_info,
            });
            if !template.description.is_empty() {
                entry["description"] = json!(template.description);
            }
            if let Some(hint) = &template.argument_hint {
                entry["argumentHint"] = json!(hint);
            }
            if let Some(artifact) =
                artifact_reference(session_id, &cwd, "prompt", &template.file_path)
            {
                entry["artifact"] = artifact;
            }
            entry
        })
        .collect();
    let context_files: Vec<Value> = resources
        .agents_files
        .iter()
        .map(|file| {
            let path = file.path.display().to_string();
            let mut entry = json!({ "path": path });
            if let Some(artifact) = artifact_reference(session_id, &cwd, "context_file", &path) {
                entry["artifact"] = artifact;
            }
            entry
        })
        .collect();
    json!({
        "contextFiles": context_files,
        "skills": skills,
        "prompts": prompts,
        "themes": [],
        "diagnostics": {
            "skills": resources.skill_diagnostics,
            "prompts": [],
            "themes": [],
        },
    })
}

/// One artifact reference (TS `createArtifactReference` in
/// modes/agent-connection/snapshot.ts): the sha256-derived id, the owning
/// session, the artifact type, and the logical path (cwd-relative when the
/// file lives under the cwd, else the basename).
fn artifact_reference(
    session_id: &str,
    cwd: &str,
    artifact_type: &str,
    file_path: &str,
) -> Option<Value> {
    if file_path.is_empty() {
        return None;
    }
    let digest = Sha256::new()
        .chain_update(format!("{session_id}\0{artifact_type}\0{file_path}"))
        .finalize();
    // The first 16 hex characters of the digest (8 bytes).
    let mut id = String::with_capacity(16);
    for byte in digest.iter().take(8) {
        // Writing into a String cannot fail.
        let _ = write!(id, "{byte:02x}");
    }
    let logical = logical_artifact_path(cwd, file_path);
    let mut reference = json!({
        "id": format!("artifact_{id}"),
        "sessionId": session_id,
        "type": artifact_type,
        "logicalPath": logical,
    });
    if let Ok(relative) = Path::new(file_path).strip_prefix(cwd) {
        if logical.chars().next().is_some_and(|c| c != '.' && c != '/') {
            reference["relativePath"] = json!(relative.to_string_lossy().replace('\\', "/"));
        }
    }
    Some(reference)
}

/// TS `createArtifactPathInfo`: synthetic paths (`<...>`) stay as-is; a
/// path under the cwd keeps its cwd-relative form; anything else degrades
/// to the basename.
fn logical_artifact_path(cwd: &str, file_path: &str) -> String {
    if file_path.starts_with('<') && file_path.ends_with('>') {
        return file_path.to_string();
    }
    if let Ok(relative) = Path::new(file_path).strip_prefix(cwd) {
        let relative = relative.to_string_lossy().replace('\\', "/");
        if !relative.is_empty() && !relative.starts_with("..") && !relative.starts_with('/') {
            return relative;
        }
    }
    Path::new(file_path).file_name().map_or_else(
        || "artifact".to_string(),
        |name| name.to_string_lossy().into_owned(),
    )
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The artifact reference: a stable 16-hex id over (session, type,
    /// path), the cwd-relative logical path for a file under the cwd, and
    /// the basename otherwise.
    #[test]
    fn artifact_references_follow_the_ts_shape() {
        let reference = artifact_reference("s1", "/work", "skill", "/work/skills/a/SKILL.md")
            .expect("a reference");
        let id = reference["id"].as_str().expect("id");
        assert_eq!(id.len(), "artifact_".len() + 16);
        assert!(id.starts_with("artifact_"));
        assert_eq!(reference["logicalPath"], "skills/a/SKILL.md");
        assert_eq!(reference["relativePath"], "skills/a/SKILL.md");
        assert_eq!(
            artifact_reference("s1", "/work", "skill", "/work/skills/a/SKILL.md"),
            Some(reference),
            "the id is deterministic"
        );
        let outside =
            artifact_reference("s1", "/work", "prompt", "/home/u/p.md").expect("a reference");
        assert_eq!(outside["logicalPath"], "p.md");
        assert!(outside.get("relativePath").is_none());
        assert_eq!(artifact_reference("s1", "/work", "prompt", ""), None);
        assert_eq!(logical_artifact_path("/work", "<builtin>"), "<builtin>");
    }
}
