---
name: skill-creator
description: Create, review, trim or install an eukhe skill (markdown, or Python-backed and callable from the kernel). Use when the user asks for a new skill, wants a workflow, script or prompt turned into a reusable skill, asks how to write a SKILL.md or where skills live, or asks whether something should be a skill, a tool or a subagent.
---

# Skill Creator

Skills teach how; tools do; subagents give a separate context. One agent with one context runs the loop and loads skills on demand.

## 1. Decide what to build

| The need | Build | Why |
|---|---|---|
| steps, rules, judgment calls, domain know-how | a markdown skill | costs only its description until a task needs it |
| an action, live data, a fixed-shape result, a hard limit or precondition | a tool: a Python skill function (or an MCP server) that refuses with a message the model can act on | a limit in code holds; a limit in prose is a hope |
| parallel work, context bloat, conflicting tools or instructions | a subagent spec, plus a skill that says when to spawn it | divide by context; only a compact result comes back |

Default to a skill. Facts every turn needs belong in the prompt, not a skill.

## 2. Keep three levels apart

1. `name` + `description`: always in the prompt, every turn, for every skill. Make it a trigger: what it achieves and "Use when ..." with the words a request contains. At most 1024 bytes.
2. `SKILL.md` body: loads when the task matches. Procedure and judgment only (numbered steps, rules, failure handling), about 2 KB.
3. `references/`, `scripts/`, `assets/`: load only when the body links them. Signatures, field lists, long examples.

## 3. Write

1. Check the skill list: no two descriptions may trigger on the same request. Overlap: sharpen both, or extend the existing skill.
2. Pick the location (ask when unclear): project `.eukhe/skills/<name>/`, personal `~/.eukhe/skills/<name>/`, or a package's `skills/`.
3. Write `SKILL.md`; move anything the body only looks up into `references/`.
4. Add `evals/cases.jsonl`: about 10 golden cases, one JSON object per line, `{"prompt": ..., "expect_skill": ..., "expect": ...}`. Include near misses whose `expect_skill` is another skill or `null`.
5. Verify it loads (format reference). A description with an unquoted `: ` breaks the YAML and the skill does not load.

## 4. Prune

Delete what the model does right without the skill, text the system prompt or another skill already carries, and steps no eval needs. A smaller skill triggers more precisely and costs less.

Format, frontmatter and checks: [references/format.md](references/format.md). Python-backed skills: [references/python-skills.md](references/python-skills.md).
