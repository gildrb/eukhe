//! The runtime bootstrap code injected into each kernel right after start or
//! restore: binds the `rlm`, `bash`, and MCP surfaces and pre-imports every
//! Python skill (from `core/tools/ipython.ts`'s `buildRlmBootstrapCode`).

use super::KernelPythonSkill;

/// Line the runtime bootstrap prints (once, after the skill import loop) when
/// one or more pre-imported Python skills failed to import. The host scans
/// the bootstrap cell's stdout for this marker so unavailable skills reach
/// the model instead of failing only on first call.
pub const PYTHON_SKILL_IMPORT_ERROR_REPORT_MARKER: &str = "__EUKHE_PYTHON_SKILL_IMPORT_ERRORS__";

/// Failed skill imports reported by a bootstrap cell: `(import name, import
/// error)` pairs in import order (TS `UnavailablePythonSkills =
/// Record<string, string>`; the marker's JSON preserves insertion order,
/// which the notice keeps).
pub type UnavailablePythonSkills = Vec<(String, String)>;

/// Extract the unavailable-skill report a bootstrap cell printed, or
/// `None` when it printed none: the marker must be followed by a JSON
/// object of `{import name: error}` with at least one non-empty string
/// value (TS `parseUnavailablePythonSkills`).
#[must_use]
pub fn parse_unavailable_python_skills(stdout: &str) -> Option<UnavailablePythonSkills> {
    let at = stdout.find(PYTHON_SKILL_IMPORT_ERROR_REPORT_MARKER)?;
    let raw = stdout[at + PYTHON_SKILL_IMPORT_ERROR_REPORT_MARKER.len()..].trim();
    let parsed = serde_json::from_str::<serde_json::Map<String, serde_json::Value>>(raw).ok()?;
    let errors = parsed
        .into_iter()
        .filter_map(|(name, error)| {
            let error = error.as_str()?;
            (!error.is_empty()).then(|| (name, error.to_string()))
        })
        .collect::<UnavailablePythonSkills>();
    (!errors.is_empty()).then_some(errors)
}

const RLM_BOOTSTRAP_HEADER_CODE: &str =
    "import asyncio\nimport os as _eukhe_os\n\n_eukhe_os.environ[\"NO_COLOR\"] = \"1\"";

const RLM_BOOTSTRAP_RUNTIME_CODE: &str = r#"
try:
    import rlm as _eukhe_rlm_module
    rlm = _eukhe_rlm_module.rlm
    bash = _eukhe_rlm_module.bash
    import rlm.mcp as mcp
except Exception as _eukhe_rlm_error:
    _EUKHE_RLM_IMPORT_ERROR = str(_eukhe_rlm_error)

    class _EukheMissingRlm:
        def _raise_missing(self):
            raise RuntimeError(
                "eukhe-runtime is not installed in this kernel. "
                "Remove ~/.eukhe/kernel-venv so eukhe can rebuild it, or set "
                "EUKHE_KERNEL_PYTHON to a kernel environment with eukhe-runtime installed. "
                f"Import error: {_EUKHE_RLM_IMPORT_ERROR}"
            )

        async def spawn(self, prompt, **kwargs):
            self._raise_missing()

        async def find_models(self, query="", limit=8):
            self._raise_missing()

        async def create_session(self, prompt, **kwargs):
            self._raise_missing()

        async def list_subagents(self):
            self._raise_missing()

        async def delete_subagent(self, target):
            self._raise_missing()

    rlm = _EukheMissingRlm()

    def bash(command):
        rlm._raise_missing()
"#;

/// The code the session injects right after kernel start/restore: binds the
/// `rlm`, `bash`, and MCP surfaces, imports every Python skill (wrapping
/// callable ones, replacing broken imports with a stub that raises), and —
/// when any import failed — ends by printing
/// [`PYTHON_SKILL_IMPORT_ERROR_REPORT_MARKER`] plus the errors as JSON so
/// the host can tell the model, matching the TS `buildRlmBootstrapCode`.
#[must_use]
pub fn build_rlm_bootstrap_code(python_skills: &[KernelPythonSkill]) -> String {
    let base_code = format!("{RLM_BOOTSTRAP_HEADER_CODE}\n\n{RLM_BOOTSTRAP_RUNTIME_CODE}");
    // TS: `[...new Set(pythonSkills.map(...))]` — first-seen order, so the
    // pre-import loop (and the unavailable-skills report it prints) follows
    // the session's skill discovery order.
    let mut import_names: Vec<&str> = Vec::new();
    for skill in python_skills {
        let import_name = skill.import_name.as_str();
        if !import_names.contains(&import_name) {
            import_names.push(import_name);
        }
    }
    if import_names.is_empty() {
        return base_code;
    }
    let imports_json = serde_json::to_string(&import_names).unwrap_or_else(|_| "[]".to_string());
    format!(
        r#"
{base_code}

import importlib as _eukhe_importlib
import inspect as _eukhe_inspect
import sys as _eukhe_sys
import types as _eukhe_types

class _EukheCallableSkillModule(_eukhe_types.ModuleType):
    async def __call__(self, *args, **kwargs):
        result = self.run(*args, **kwargs)
        if _eukhe_inspect.isawaitable(result):
            return await result
        return result

class _EukheUnavailableSkill:
    def __init__(self, name, error):
        self.__name__ = name
        self._eukhe_import_error = error
        self.__doc__ = f"Python skill {{name}} is unavailable: {{error}}"

    async def run(self, *args, **kwargs):
        raise RuntimeError(
            f"Python skill {{self.__name__}} is unavailable in this kernel. "
            f"Import error: {{self._eukhe_import_error}}"
        )

    async def __call__(self, *args, **kwargs):
        return await self.run()

    def __repr__(self):
        return f"<unavailable Python skill {{self.__name__!r}}: {{self._eukhe_import_error}}>"

def _eukhe_wrap_skill_module(module):
    run = getattr(module, "run", None)
    if not callable(run):
        return module
    if isinstance(module, _EukheCallableSkillModule):
        return module
    wrapped = _EukheCallableSkillModule(module.__name__)
    wrapped.__dict__.update(module.__dict__)
    try:
        wrapped.__signature__ = _eukhe_inspect.signature(run)
    except Exception:
        pass
    doc = getattr(run, "__doc__", None)
    if doc:
        wrapped.__doc__ = doc
    _eukhe_sys.modules[module.__name__] = wrapped
    return wrapped

_EUKHE_SKILL_IMPORT_ERRORS = {{}}

for _eukhe_skill_name in {imports_json}:
    try:
        globals()[_eukhe_skill_name] = _eukhe_wrap_skill_module(
            _eukhe_importlib.import_module(_eukhe_skill_name)
        )
    except Exception as _eukhe_skill_error:
        # An empty exception message would otherwise be dropped by the
        # host-side parser; fall back to the exception type name.
        _eukhe_skill_error_text = (
            str(_eukhe_skill_error) or type(_eukhe_skill_error).__name__
        )
        _EUKHE_SKILL_IMPORT_ERRORS[_eukhe_skill_name] = _eukhe_skill_error_text
        globals()[_eukhe_skill_name] = _EukheUnavailableSkill(
            _eukhe_skill_name,
            _eukhe_skill_error_text,
        )

if _EUKHE_SKILL_IMPORT_ERRORS:
    import json as _eukhe_json
    print(
        "{PYTHON_SKILL_IMPORT_ERROR_REPORT_MARKER}"
        + _eukhe_json.dumps(_EUKHE_SKILL_IMPORT_ERRORS)
    )
"#
    )
    .trim()
    .to_string()
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::path::PathBuf;

    #[test]
    fn bootstrap_code_without_skills_binds_rlm() {
        let code = build_rlm_bootstrap_code(&[]);
        assert!(code.contains("import rlm as _eukhe_rlm_module"));
        assert!(!code.contains("_EukheUnavailableSkill"));
    }

    #[test]
    fn bootstrap_code_imports_skills() {
        let skills = vec![KernelPythonSkill {
            name: "edit".into(),
            import_name: "edit".into(),
            package_path: PathBuf::from("/pkg/edit"),
            pyproject_path: PathBuf::from("/pkg/edit/pyproject.toml"),
        }];
        let code = build_rlm_bootstrap_code(&skills);
        assert!(code.contains(r#"for _eukhe_skill_name in ["edit"]"#));
        assert!(code.contains("_EukheUnavailableSkill"));
    }

    /// The TS #2381 parser table: marker+JSON, noise-prefixed marker,
    /// no marker, non-JSON payload, and the empty dict all land where the
    /// host-side report decides notice vs silence.
    #[test]
    fn parse_unavailable_python_skills_table() {
        let cases: Vec<(String, Option<UnavailablePythonSkills>)> = vec![
            (
                format!(
                    "{PYTHON_SKILL_IMPORT_ERROR_REPORT_MARKER}{{\"websearch\":\"No module named 'websearch'\"}}\n"
                ),
                Some(vec![("websearch".into(), "No module named 'websearch'".into())]),
            ),
            (
                format!("noise\n{PYTHON_SKILL_IMPORT_ERROR_REPORT_MARKER}{{\"edit\":\"boom\"}}"),
                Some(vec![("edit".into(), "boom".into())]),
            ),
            ("some unrelated kernel output".to_string(), None),
            (format!("{PYTHON_SKILL_IMPORT_ERROR_REPORT_MARKER}not json"), None),
            (format!("{PYTHON_SKILL_IMPORT_ERROR_REPORT_MARKER}{{}}"), None),
        ];
        for (stdout, expected) in cases {
            assert_eq!(
                parse_unavailable_python_skills(&stdout),
                expected,
                "{stdout}"
            );
        }
    }

    #[test]
    fn parse_unavailable_python_skills_drops_non_string_and_empty_values() {
        // Non-string values and empty messages drop (TS keeps only
        // non-empty string entries); ordering follows the marker's JSON.
        let stdout = format!(
            "{PYTHON_SKILL_IMPORT_ERROR_REPORT_MARKER}{{\"edit\":\"boom\",\"null_skill\":null,\"list_skill\":[1],\"empty_skill\":\"\",\"websearch\":\"No module named 'websearch'\"}}"
        );
        assert_eq!(
            parse_unavailable_python_skills(&stdout),
            Some(vec![
                ("edit".into(), "boom".into()),
                ("websearch".into(), "No module named 'websearch'".into()),
            ])
        );
        // A report whose every value drops stays silent.
        let stdout = format!("{PYTHON_SKILL_IMPORT_ERROR_REPORT_MARKER}{{\"empty_skill\":\"\"}}");
        assert_eq!(parse_unavailable_python_skills(&stdout), None);
    }
}
