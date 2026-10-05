//! rlm bootstrap code injected into every kernel start (TS:
//! `buildRlmBootstrapCode` and its constants in
//! `packages/coding-agent/src/core/tools/ipython.ts`). Split from the
//! ipython tool module for module-size hygiene.

const RLM_BOOTSTRAP_HEADER_CODE: &str = r#"
import asyncio
import os as _eukhe_os

_eukhe_os.environ["NO_COLOR"] = "1"
"#;

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

/// A Python skill installed into the kernel namespace.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PythonSkillRuntimeInfo {
    /// Module import name bound in the kernel namespace.
    pub import_name: String,
}

/// Bootstrap code that binds `rlm` and the Python skills into the kernel.
///
/// Port of `buildRlmBootstrapCode` from ipython.ts: imports the rlm runtime,
/// substitutes a raising stub when it is missing, and wraps each Python skill
/// module with a callable wrapper that forwards `__call__` to `run`.
///
/// # Panics
///
/// Panics if the sorted import-name list cannot be serialized as JSON,
/// which cannot fail for a list of strings.
#[must_use]
pub fn build_rlm_bootstrap_code(python_skills: &[PythonSkillRuntimeInfo]) -> String {
    let base_code = format!("{RLM_BOOTSTRAP_HEADER_CODE}\n\n{RLM_BOOTSTRAP_RUNTIME_CODE}");

    // The Python source embeds the exact JS JSON.stringify of the import names.
    let import_names: Vec<&str> = {
        let mut names: Vec<&str> = python_skills
            .iter()
            .map(|skill| skill.import_name.as_str())
            .collect();
        names.sort_unstable();
        names.dedup();
        names
    };
    if import_names.is_empty() {
        return base_code;
    }

    let import_names_json = serde_json::to_string(&import_names).expect("names serialize");

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
        return await self.run(*args, **kwargs)

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

for _eukhe_skill_name in {import_names_json}:
    try:
        globals()[_eukhe_skill_name] = _eukhe_wrap_skill_module(
            _eukhe_importlib.import_module(_eukhe_skill_name)
        )
    except Exception as _eukhe_skill_error:
        _EUKHE_SKILL_IMPORT_ERRORS[_eukhe_skill_name] = str(_eukhe_skill_error)
        globals()[_eukhe_skill_name] = _EukheUnavailableSkill(
            _eukhe_skill_name,
            str(_eukhe_skill_error),
        )
"#
    )
    .trim()
    .to_string()
}
