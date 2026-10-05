//! The version-file concern (moved with its concern): the schema consts, the
//! `.bootstrap-version` read/write, and the current-version predicates the
//! flows and the readiness gates compose.

use super::{BootstrapPythonSkill, BootstrapVersion, Path};

/// Schema of `.bootstrap-version`; a mismatch rebuilds the venv. Schema 10:
/// the venv installs from the runtime's hash-locked requirements, whose
/// content is part of the runtime identity (no separate package record).
pub(super) const BOOTSTRAP_SCHEMA: u64 = 10;
const BOOTSTRAP_VERSION_FILE: &str = ".bootstrap-version";
pub(super) fn read_bootstrap_version(venv: &Path) -> Option<BootstrapVersion> {
    let raw = std::fs::read_to_string(venv.join(BOOTSTRAP_VERSION_FILE)).ok()?;
    let parsed: BootstrapVersion = serde_json::from_str(&raw).ok()?;
    (parsed.schema > 0).then_some(parsed)
}

/// Identity of one recorded skill: the install root is the package path, and
/// the editable install follows that path.
pub(super) fn bootstrap_skill_key(skill: &BootstrapPythonSkill) -> String {
    format!("{}\u{0}{}", skill.import_name, skill.package_path)
}

/// True when the recorded installs cover every current skill at the same
/// path with the same pyproject hash. Extra recorded skills from other
/// sessions are fine: the venv is a shared cache, not a per-session manifest,
/// so a session whose skill set differs must not force reinstalls.
pub(super) fn recorded_skills_cover(
    recorded: Option<&[BootstrapPythonSkill]>,
    current: &[BootstrapPythonSkill],
) -> bool {
    if current.is_empty() {
        return true;
    }
    let Some(recorded) = recorded else {
        return false;
    };
    current.iter().all(|skill| {
        recorded.iter().any(|entry| {
            bootstrap_skill_key(entry) == bootstrap_skill_key(skill)
                && entry.pyproject_path == skill.pyproject_path
                && entry.pyproject_hash == skill.pyproject_hash
        })
    })
}

pub(super) fn bootstrap_base_version_current(
    version: Option<BootstrapVersion>,
    runtime_identity: &str,
) -> bool {
    match version {
        Some(version) => {
            version.schema == BOOTSTRAP_SCHEMA
                && version.runtime.as_deref() == Some(runtime_identity)
        }
        None => false,
    }
}

pub(super) fn bootstrap_version_current(
    version: Option<&BootstrapVersion>,
    runtime_identity: &str,
    python_skills: &[BootstrapPythonSkill],
) -> bool {
    version.is_some_and(|version| {
        bootstrap_base_version_current(Some(version.clone()), runtime_identity)
            && recorded_skills_cover(version.python_skills.as_deref(), python_skills)
    })
}

pub(crate) fn write_bootstrap_version(
    venv: &Path,
    runtime_identity: &str,
    python_skills: &[BootstrapPythonSkill],
) -> anyhow::Result<()> {
    let version = BootstrapVersion {
        schema: BOOTSTRAP_SCHEMA,
        runtime: Some(runtime_identity.to_string()),
        python_skills: Some(python_skills.to_vec()),
    };
    std::fs::write(
        venv.join(BOOTSTRAP_VERSION_FILE),
        format!("{}\n", serde_json::to_string(&version)?),
    )?;
    Ok(())
}

/// The parsed `.bootstrap-version` plus its raw text (the probe-memo key
/// input), in one read.
pub(super) fn read_bootstrap_version_raw(venv: &Path) -> (Option<BootstrapVersion>, String) {
    let raw = std::fs::read_to_string(venv.join(BOOTSTRAP_VERSION_FILE)).unwrap_or_default();
    let parsed: Option<BootstrapVersion> = serde_json::from_str(&raw).ok();
    (parsed.filter(|v| v.schema > 0), raw)
}
