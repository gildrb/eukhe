# The `rlm.harness` API

The calls are synchronous: call them without `await`. `global_=True` targets the global store (every session; Python reserves `global`, so the parameter is spelled `global_`); the default is this session's store.

- `rlm.harness.create_skill(title: str, content: str, *, id: str | None = None, path: str = "general", reference: dict | None = None, arguments: dict | None = None, metadata: dict | None = None, global_: bool = False) -> HarnessEntry`: `reference`/`arguments` describe the Python callable (`reference` requires `{"type": "python"}`, a Python import, and a callable or call pattern)
- `rlm.harness.update_skill(id: str, title: str, content: str, *, path: str | None = None, reference: dict | None = None, arguments: dict | None = None, metadata: dict | None = None, global_: bool = False) -> HarnessEntry`
- `rlm.harness.delete_skill(id: str, *, global_: bool = False) -> bool`
- `rlm.harness.create_subagent(title: str, content: str, *, id: str | None = None, path: str = "general", metadata: dict | None = None, global_: bool = False) -> HarnessEntry`
- `rlm.harness.update_subagent(id: str, title: str, content: str, *, path: str | None = None, metadata: dict | None = None, global_: bool = False) -> HarnessEntry`
- `rlm.harness.delete_subagent(id: str, *, global_: bool = False) -> bool`
- `rlm.harness.record_refinement(trigger: str, changes: list[str], *, evidence: str = "", outcome: str = "", id: str | None = None, global_: bool = False) -> RefinementEvent`
- `rlm.harness.plan_refinement(observation: str, *, failing_component: str = "", next_step: str = "") -> list[str]`: a suggested diagnose -> update -> validate plan
- `rlm.harness.overview(*, max_entries_per_kind: int = 20, global_: bool = False) -> str`: overview of the stored entries
- `rlm.harness.search(query: str, kind: str | None = None, limit: int = 10, *, global_: bool = False) -> list[HarnessEntry]`: ranked term search over the entries

`HarnessEntry`:

- `id: str`
- `kind: Literal["prompt", "memory", "skill", "subagent"]`: memories and prompt notes exist only in harness-memory sessions
- `title: str`
- `content: str`
- `path: str`: category path ("general" for memories, "policy" for prompt notes)
- `scope: Literal["local", "global"]`
- `reference: dict[str, Any]`: for skills
- `arguments: dict[str, Any]`: for skills
- `metadata: dict`
- `source: Literal["agent", "refine"]`
- `created_at: str`: ISO timestamp of creation
- `updated_at: str`: ISO timestamp of latest update
- `version: int`: increments with every update, starting at 1

`RefinementEvent`:

- `id: str`
- `trigger: str`: what caused the refinement
- `changes: list[str]`: applied edits; empty if never edited
- `evidence: str`
- `outcome: str`
- `created_at: str`
