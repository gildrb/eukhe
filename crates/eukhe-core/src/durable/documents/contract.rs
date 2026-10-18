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
const PATH_RULE: &str = "Relative paths resolve against the session's working directory; the Python functions of the same name resolve against the REPL's current directory (`os.getcwd()`).";

const PATH_ALIASES: &[&str] = &["file_path", "filepath", "file", "filename"];

const READ_DESCRIPTION: &str = "Read a file or directory.

Put line ranges in `path`, never a separate range/offset/limit parameter: `{\"path\":\"notes.txt:450-455\"}` reads lines 450-455. Include the selector on every ranged call; repeating a bare path does not advance through the file.

Path suffixes: :50 or :50- starts at line 50; :50-200 inclusive; :50+150 counts lines; commas join ranges (:5-16,960-973) or individual lines (:19,59). A single non-raw range also shows 1 line before and 3 after (e.g. :50-80 shows 49-83). :raw verbatim without anchors/prefixes; combine :2-4:raw or :raw:2-4 for exactly those lines.

Sources:
- File: `[foo.ts#1A2B]` snapshot, then `N:TEXT` lines. Copy `[FILENAME#TAG]` for anchored edits; NEVER invent tag.
- Directory: complete root; child listings cap at 12 (`… N more`), read child.
- Internal URLs: `repo://<path>` under the workspace root; `skill://<name>/<path>` under a skill's directory (bare `skill://<name>`: its SKILL.md); `agent://<name|id>` a subagent's chat; `memory://` the chat view, `memory://<id>` message id whole, `memory://<id>/<n>` line id+n; `mcp://<server>` an MCP server's resources, `mcp://<server>/<uri>` one resource; `ssh://<host>/<path>` one remote text file (`/<path>` from the remote root, `/~/<path>` under the remote home; only hosts in the user's `ssh.hosts`). `..` never leaves a URL's root: a path above it, or a symlink out of it, is rejected.";

const GREP_DESCRIPTION: &str = "Regex: Rust syntax. `path`: `;`-separated file/dir/glob; default `.`. Default case-sensitive, gitignore respected; `skip` paginates files.
File-only selector: `src/foo.ts:50-100`. Literal `\\n`/`\\\\n` enables cross-line.
Bare glob `*.ts` matches any depth; `dir/*.ts` only `dir`'s direct children (`dir/**/*.ts` recurses).
Hits print as `[path#TAG]` groups of `*N:TEXT` (match) and ` N:TEXT` (context) rows; every printed line is an `edit` anchor.";

const GLOB_DESCRIPTION: &str = "Glob files/dirs: `;`-separated paths; default `.`.
`gitignore` and `hidden` default true; ignored dotfiles need `gitignore: false`. Newest-first by directory; dirs end `/`.";

const WRITE_DESCRIPTION: &str = "Create or overwrite a file atomically. Parent directories are created; a replaced file keeps its BOM, line endings, and mode. Prefer `edit` for changes to an existing file.";

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

fn described(description: &str) -> Options {
    Options::new().set("description", description)
}

fn optional_string(description: &str) -> TSchema {
    Type::optional(Type::string_with(described(description)))
}

fn optional_boolean(description: &str) -> TSchema {
    Type::optional(Type::boolean_with(described(description)))
}

fn optional_integer(description: &str, minimum: u32) -> TSchema {
    Type::optional(Type::integer_with(
        described(description).set("minimum", minimum),
    ))
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
            Self::Read => vec![(
                "path",
                Type::string_with(described(
                    "File or directory path; inline selectors (`:50-200`, `:raw`) are supported.",
                )),
            )],
            Self::Write => vec![
                ("path", Type::string_with(described("File path"))),
                ("content", Type::string_with(described("The whole new file text"))),
            ],
            Self::Edit => vec![(
                "input",
                Type::string_with(described("One or more [PATH#TAG] sections")),
            )],
            Self::Grep => vec![
                ("pattern", Type::string_with(described("regex pattern"))),
                (
                    "path",
                    optional_string(
                        "file, directory, glob, or \"<file>:<lines>\" selector to search; pass several as a semicolon-delimited list (\"src; tests\"). Omitted -> searches \".\"",
                    ),
                ),
                ("case", optional_boolean("case-sensitive search (default true)")),
                ("gitignore", optional_boolean("respect gitignore (default true)")),
                (
                    "skip",
                    optional_integer(
                        "files to skip before collecting results — use to paginate when the prior call hit the file limit",
                        0,
                    ),
                ),
            ],
            Self::Glob => vec![
                (
                    "path",
                    optional_string(
                        "glob, file, or directory to search — a single path or a semicolon-delimited list (\"src/**/*.ts; test/**/*.ts\"). Omitted -> searches \".\"",
                    ),
                ),
                ("hidden", optional_boolean("include hidden files (default true)")),
                ("gitignore", optional_boolean("respect gitignore (default true)")),
                ("limit", optional_integer("max results", 1)),
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
}

impl GlobArgs {
    pub(super) fn into_request(self) -> GlobRequest {
        GlobRequest {
            path: self.path.unwrap_or_else(|| ".".to_owned()),
            hidden: self.hidden.unwrap_or(true),
            gitignore: self.gitignore.unwrap_or(true),
            limit: self.limit,
        }
    }
}
