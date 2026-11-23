# Skill format

eukhe follows the [Agent Skills standard](https://agentskills.io/specification) and extends it with Python-backed skills.

| Kind | What it is | When |
|---|---|---|
| markdown | `SKILL.md` plus optional references, scripts and assets | procedures, CLI recipes, domain knowledge |
| python | a markdown skill that also ships a Python package, pre-imported in the kernel (`await my_skill(...)`) | an action the agent calls: API wrappers, fetchers, converters, computations |

## Layout

```
my-skill/
├── SKILL.md              # required: frontmatter + body
├── references/           # optional: docs the body links, loaded only when needed
├── scripts/              # optional: helper scripts the body runs
├── assets/               # optional: templates and data files
└── evals/cases.jsonl     # optional: golden routing examples
```

Discovery stops at a directory that holds `SKILL.md`, so these subdirectories are never read as skills. Link files with paths relative to the skill directory; the agent resolves them against it, and `read skill://<name>/<path>` reads one directly.

## Frontmatter

```markdown
---
name: my-skill
description: What it achieves. Use when ...
---
```

| Field | Required | Rules |
|---|---|---|
| `name` | yes | at most 64 characters: `a-z`, `0-9`, hyphens; no leading, trailing or double hyphens; equals the directory name |
| `description` | yes | at most 1024 characters; missing, empty or invalid YAML: the skill is not loaded |
| `disable-model-invocation` | no | `true` hides it from the prompt; only `/skill:<name>` invokes it |
| `license` | no | a license name or a bundled file |
| `compatibility` | no | at most 500 characters: environment requirements |
| `metadata` | no | any key-value mapping |
| `allowed-tools` | no | space-separated pre-approved tools (experimental) |

Unknown fields are ignored. A name violation is a warning; the skill still loads. An unquoted description that contains `: ` is invalid YAML; quote it or reword it.

Good description: `Extracts text and tables from PDF files, fills PDF forms, merges PDFs. Use when working with PDF documents.` Poor: `Helps with PDFs.`

## Precedence

On a name collision the first skill found wins: explicit `--skill` paths and `skills` settings entries, then project, then global, then package, then built-in skills.

## Evals

`evals/cases.jsonl`, one object per line:

```json
{"prompt": "the user's request", "expect_skill": "my-skill", "expect": "what a correct run does"}
```

- About 10 cases: typical requests, phrasing variants, and near misses (`expect_skill` names the skill that should win instead, or `null` when none should load).
- Run them by hand after an edit: give each prompt to a fresh session and check that the expected skill loads and the run does what `expect` says.

## Verification

1. Re-read the frontmatter against the table: `name` equals the directory, the description is non-empty valid YAML.
2. `/reload` in an interactive session picks up new skills; other sessions pick them up at start. Load problems (bad name, missing description, collisions, invalid YAML) show as warnings.
3. A loaded skill is invocable as `/skill:<name>`.

Python-backed skills: also run the checks in [python-skills.md](python-skills.md).
