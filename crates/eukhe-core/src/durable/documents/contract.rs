//! One contract per documents function: its name, revision, model-facing
//! description, parameter schema, and declared dialect. The wire tools and
//! the kernel's `fs.*` requests decode through the same contract, so
//! `read(path=...)` in Python and a `read` tool call mean the same thing and
//! repair the same way (omp ADRs 0020, 0026).

use std::num::NonZeroUsize;

use eukhe_ai::typebox::{Options, TSchema, Type};
use eukhe_docs::{GlobRequest, GrepRequest};
use eukhe_durable::harness::{repair_arguments, ArgDialect, ArgumentError, Repaired};
use eukhe_types::pi_ai::{JsonObject, ToolSchema};
use serde::Deserialize;

/// Lines of context omp's grep shows around each match.
const GREP_CONTEXT_BEFORE: u32 = 1;
const GREP_CONTEXT_AFTER: u32 = 3;

/// How a relative path resolves, the same for every function.
const PATH_RULE: &str = "Relative paths resolve against the session's cwd; the same-named Python functions use `os.getcwd()`.";

const PATH_ALIASES: &[&str] = &["file_path", "filepath", "file", "filename"];

const READ_DESCRIPTION: &str = "Read a file or directory. Line ranges go in `path`, never in separate offset/limit parameters (`notes.txt:450-455`); repeat the selector on every ranged call.
Selectors: `:50`/`:50-` from line 50; `:50-200` inclusive; `:50+150` 150 lines; commas join ranges or lines (`:5-16,960-973`, `:19,59`). One non-raw range also shows 1 line before and 3 after. `:raw` verbatim without prefixes (`:2-4:raw` exactly those lines).
A file prints as a `[path#TAG]` header, then `N:TEXT` rows; `edit` copies that header verbatim. A directory lists its root; child listings cap at 12 (`… N more`): read the child.
URLs: `repo://<path>` (workspace root); `skill://<name>/<path>` (bare: its SKILL.md); `agent://<name|id>` (subagent chat); `memory://` (chat view), `memory://<id>` (message whole), `memory://<id>/<n>` (line id+n); `mcp://<server>` (resource list), `mcp://<server>/<uri>`; `ssh://<host>/<path>` (remote text file, `/~/` = remote home, `ssh.hosts` only). `..` never leaves a URL's root.";

const GREP_DESCRIPTION: &str = "Regex search, Rust syntax; case-sensitive and gitignore-respecting by default. `path`: `;`-separated files/dirs/globs or a `file:50-100` selector; default `.`. Bare glob `*.ts` matches any depth; `dir/*.ts` only direct children (`dir/**/*.ts` recurses). Literal `\\n` enables cross-line matches. `skip` pages by file.
Hits print as `[path#TAG]` then `*N:TEXT` (match) and ` N:TEXT` (context) rows: `edit` anchors under that header. A file printed without a tag must be read before an edit.";

const GLOB_DESCRIPTION: &str = "Glob files/dirs: `;`-separated patterns or paths; default `.`. `hidden` and `gitignore` default true (ignored dotfiles need `gitignore: false`). Newest first by directory; dirs end `/`; `skip` pages past the first `limit` paths.";

const WRITE_DESCRIPTION: &str = "Create or overwrite a whole file atomically; parent directories are created; BOM, line endings and mode are kept. An existing file is replaced only if you read or wrote it and it has not changed since. Prefer `edit` for existing files.";

const EXACT_STRING_HINT: &str = "edit takes a hashline patch, not old/new strings. read or grep the file, then send '[path#TAG]\\nPUT 12.=14:\\n+new line' with the header and line numbers they printed.";

/// A documents function.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum Function {
    Read,
    Write,
    Edit,
    Grep,
    Glob,
}

fn optional_boolean() -> TSchema {
    Type::optional(Type::boolean())
}

fn optional_integer(minimum: u32) -> TSchema {
    Type::optional(Type::integer_with(Options::new().set("minimum", minimum)))
}

impl Function {
    pub(super) const fn name(self) -> &'static str {
        match self {
            Self::Read => "read",
            Self::Write => "write",
            Self::Edit => "edit",
            Self::Grep => "grep",
            Self::Glob => "glob",
        }
    }

    /// The durable identity's revision (`name@rev`).
    pub(super) const fn version(self) -> &'static str {
        match self {
            Self::Read => "read@1",
            Self::Write => "write@1",
            Self::Edit => "edit@hl.1",
            Self::Grep => "grep@1",
            Self::Glob => "glob@1",
        }
    }

    /// The `fs.*` kernel request type.
    pub(super) const fn request_type(self) -> &'static str {
        match self {
            Self::Read => "fs.read",
            Self::Write => "fs.write",
            Self::Edit => "fs.edit",
            Self::Grep => "fs.grep",
            Self::Glob => "fs.glob",
        }
    }

    /// The model-facing description, ending with the path rule.
    pub(super) fn description(self) -> String {
        let body = match self {
            Self::Read => READ_DESCRIPTION,
            Self::Write => WRITE_DESCRIPTION,
            Self::Edit => eukhe_docs::HASHLINE_DESCRIPTION,
            Self::Grep => GREP_DESCRIPTION,
            Self::Glob => GLOB_DESCRIPTION,
        };
        format!("{}\n\n{PATH_RULE}", body.trim_end())
    }

    /// The parameter schema: the shared `i`, then the function's own
    /// arguments; closed.
    pub(super) fn parameters(self) -> TSchema {
        let own: Vec<(&str, TSchema)> = match self {
            Self::Read => vec![("path", Type::string())],
            Self::Write => vec![("path", Type::string()), ("content", Type::string())],
            Self::Edit => vec![("input", Type::string())],
            Self::Grep => vec![
                ("pattern", Type::string()),
                ("path", Type::optional(Type::string())),
                ("case", optional_boolean()),
                ("gitignore", optional_boolean()),
                ("skip", optional_integer(0)),
            ],
            Self::Glob => vec![
                ("path", Type::optional(Type::string())),
                ("hidden", optional_boolean()),
                ("gitignore", optional_boolean()),
                ("limit", optional_integer(1)),
                ("skip", optional_integer(0)),
            ],
        };
        crate::durable::tool_contract::parameters(1, own)
    }

    /// The names models also use for these arguments, and the keys of
    /// another dialect refused with a hint.
    pub(super) fn dialect(self) -> ArgDialect {
        let dialect = ArgDialect::default();
        match self {
            Self::Read => dialect.alias("path", PATH_ALIASES),
            Self::Write => dialect
                .alias("path", PATH_ALIASES)
                .alias("content", &["text", "contents", "data", "body"]),
            Self::Edit => dialect
                .alias("input", &["patch", "diff", "edits", "payload"])
                .refuse(
                    &[
                        "old_string",
                        "new_string",
                        "old_str",
                        "new_str",
                        "old",
                        "new",
                    ],
                    EXACT_STRING_HINT,
                ),
            Self::Grep => dialect
                .alias("pattern", &["regex", "query", "pat"])
                .alias("path", PATH_ALIASES)
                .alias("path", &["paths", "dir", "directory"])
                .alias("case", &["case_sensitive"]),
            Self::Glob => dialect
                .alias("path", PATH_ALIASES)
                .alias("path", &["pattern", "patterns", "glob", "dir", "directory"]),
        }
    }

    /// `raw` in this function's dialect, the way the Harness repairs a wire
    /// call (aliases, scalar spellings, refused and unknown keys).
    pub(super) fn repair(self, raw: JsonObject) -> Result<Repaired, ArgumentError> {
        repair_arguments(
            self.name(),
            &ToolSchema::from(self.parameters()),
            &self.dialect(),
            raw,
        )
    }
}

/// `read@1` arguments.
#[derive(Debug, Deserialize)]
pub(super) struct ReadArgs {
    pub(super) path: String,
}

/// `write@1` arguments.
#[derive(Debug, Deserialize)]
pub(super) struct WriteArgs {
    pub(super) path: String,
    pub(super) content: String,
}

/// `edit@hl.1` arguments.
#[derive(Debug, Deserialize)]
pub(super) struct EditArgs {
    pub(super) input: String,
}

/// `grep@1` arguments.
#[derive(Debug, Deserialize)]
pub(super) struct GrepArgs {
    pattern: String,
    path: Option<String>,
    case: Option<bool>,
    gitignore: Option<bool>,
    skip: Option<u64>,
}

impl GrepArgs {
    pub(super) fn into_request(self) -> GrepRequest {
        GrepRequest {
            pattern: self.pattern,
            path: self.path.unwrap_or_else(|| ".".to_owned()),
            glob: None,
            ignore_case: !self.case.unwrap_or(true),
            gitignore: self.gitignore.unwrap_or(true),
            context_before: GREP_CONTEXT_BEFORE,
            context_after: GREP_CONTEXT_AFTER,
            skip: self.skip.unwrap_or(0),
            limit: None,
        }
    }
}

/// `glob@1` arguments.
#[derive(Debug, Deserialize)]
pub(super) struct GlobArgs {
    path: Option<String>,
    hidden: Option<bool>,
    gitignore: Option<bool>,
    limit: Option<NonZeroUsize>,
    skip: Option<u64>,
}

impl GlobArgs {
    pub(super) fn into_request(self) -> GlobRequest {
        GlobRequest {
            path: self.path.unwrap_or_else(|| ".".to_owned()),
            hidden: self.hidden.unwrap_or(true),
            gitignore: self.gitignore.unwrap_or(true),
            limit: self.limit,
            skip: self.skip.unwrap_or(0),
        }
    }
}
