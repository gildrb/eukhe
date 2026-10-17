# Harness laws: tool surface

The shared rules (what a law secures, the adversary, H1 to H6) are in [harness.md](harness.md).

### S7. The tool surface

The tool surface is what the model can call: the tools of the roster, the
tools behind `dyn`, the internal URLs and the shell.

1. The roster is the list of tools that each request sends. The roster is
   fixed when the session opens, before its first request. After that, the
   harness rejects each change of the roster with the typed error
   `RosterFixed`: an install or uninstall of an extension that changes the
   tools the model sees, a `configure` of `tools`, `modelTools` or
   `extensions`, and an `add_tools` of a tool round. Each request sends
   the same roster, so the prompt cache stays valid.
2. A tool that comes later (the tool of an MCP server, a host tool that
   joins) does not go into the roster. The roster tool `dyn` reaches it.
   `dyn` without `name` lists the dynamic tools. `dyn` with `name` and
   `arguments` runs one. The tool `mcp/<server>/<tool>` is the tool of an
   MCP server that the user configured; the kernel's MCP client runs it.
   A host tool joins with `ToolSurface::join` and leaves with
   `ToolSurface::quit`. A tool that left is not reachable.
3. Each tool schema that the harness sends has the intent parameter `i`
   (optional, first) and a version of 1 or more: the annotation
   `title: "v<n>"` in the schema itself. Every wire API keeps it. The
   session builds every schema at open: it adds `i` when the schema does
   not have it, keeps each declared parameter in its place, and sets the
   declared version, or 1 when there is none. Building a built schema
   changes nothing. `codemode` gets `i` and `v1` in this way.
4. `report_issue` (behind `dyn`) is the AutoQA path. An agent reports a
   tool that failed or did not do what its description says, with the
   arguments `tool` and `description`. The report is stored in the session
   as a display-only row of custom type `eukhe.tool_issue`. The user sees
   the row. The model context does not get it.
5. Internal URLs. The `read` tool (and the kernel `read()`) accepts an
   internal URL `scheme://path` in place of a file path. `repo://<path>`
   reads a file or directory under the workspace root (the working
   directory of the session). `skill://<name>/<path>` reads a file under
   the directory of the skill `name`; `skill://<name>` reads its
   `SKILL.md`. `agent://<name|id>` reads the whole chat of a subagent that
   the conversation started. `memory://` reads the chat view,
   `memory://<id>` reads message `id` whole (with its images), and
   `memory://<id>/<n>` reads line `id+n`. A `repo://` or `skill://` read
   is a normal file read: it has the `[path#TAG]` header, and its lines
   are edit anchors. An unknown scheme gets the rejection `scheme`.
   `mcp://<server>` lists the resources of a server and
   `mcp://<server>/<uri>` reads one (text; a binary part is a note with
   its size and MIME type), bounded like any read. The server must be one
   of the generic MCP servers of the session. `ssh://` gets the rejection
   `scheme`: eukhe has no SSH client. `glob` rejects all schemes; `grep`
   does not find a scheme path.
6. Confinement. A URL path is a list of `/`-separated segments under the
   root of its scheme. `..` goes up one segment; `.` and an empty segment
   do not move. A path that goes above its root gets the rejection
   `escapes`. The path is not clamped to the root. A path that stays under
   its root resolves. After this lexical check, a `repo://` or `skill://`
   read resolves the real path (it follows symlinks) and requires it under
   the real path of the root. A symlink out of the root also gets the
   rejection `escapes`. This guard is against the filesystem; the model
   stays the lexical rule. A plain file path is not confined; this is the
   same as before. Absolute paths and `..` from the working directory
   still read any file. `lexical_normalize` keeps the filesystem rule
   (`/..` is `/`) and is not used for URL paths.
7. The shell and the approval gate. The `bash` tool (`bash@1`, extension
   `eukhe.shell`) is in the roster at open. It runs a script in process
   (crate `eukhe-shell`). It does not start a system shell for each
   script. A script is a list of steps. A step is one simple command.
   Steps join with `;`, a newline, `&&`, `||` and `|`. Each step can have
   redirections (`<`, `>`, `>>`, `2>&1`, `&>`). The shell expands `$NAME`,
   `${NAME}`, `$?`, a leading `~` and the patterns `*`, `?`, `[...]`. The
   shell runs the usual commands itself: `cat`, `ls`, `head`, `tail`,
   `wc`, `echo`, `pwd`, `mkdir`, `rm`, `rmdir`, `touch`, `cp` and `mv`. It
   runs `grep` on the ripgrep engine (`grep-regex`, `grep-searcher`). It
   starts all other commands, and these commands with options it does not
   know, as external processes. Each external process gets its own
   process group and the same environment as a local kernel: the
   environment of the daemon worker, with the session values on top
   (`EUKHE_CODING_AGENT_DIR`, and `EUKHE_CHAT_MEMORY` in a chat-memory
   session). One function (`kernel::manager::local_env` over
   `durable::rlm::session_env`) makes this environment for both. The
   commands of a pipeline run at the same time. OS pipes connect them, and
   the pipe buffer of the kernel limits each pipe. When a command stops,
   its input pipe closes. The command that writes to that pipe then stops
   too: an external process gets SIGPIPE, and a command of the shell stops
   with status 141. Thus `yes | head -n 3` stops. Some scripts use other
   syntax: control flow, functions, subshells, command substitution,
   here-documents or background jobs. Such a script is one `exec` step,
   and `bash -c` runs it. The tool obeys the S2 limits. The output goes
   through the `Truncation` of the call while the steps write it: the
   result keeps the output within the cap, and the `output_bounded`
   diagnostic counts each dropped byte. With the opt-out, the result keeps
   all of the output. A call blocks for the blocking budget
   (`toolBlockingBudgetMs`) at most. A script that runs longer than the
   budget becomes a job (`JobKind::Shell`) in the `JobTable` of the
   session. The call then settles `detached` with the output until that
   time and the job id. The script continues, and a gated step still asks
   the user. When the script ends, it settles its job and sends a
   `JobSettled::Shell` row (`[job-settled job:ID status:S]` and the
   bounded output) through the job-settled wake, the same as a detached
   cell. The kill of the job stops the script and kills the process group
   of each running external process; the job then settles `killed`.
8. Each step has one effect: read, write, exec or net. A table in
   `eukhe-shell` (`effect.rs`) gives the effect from the command name, the
   `git` subcommand and some options. A command that is not in the table
   has the effect exec. A read step only reads. These rules make sure of
   that:
   - A program name with `/` (`./cat`, `bin/stat`, `/usr/bin/rm`) is
     exec. The shell runs that file, whatever its name.
   - A step with an assignment (`PATH=./bin stat f`, `X=1`) is exec, and
     `export` with an operand is exec. The environment can make a reading
     command run another program (`PATH`, `LD_PRELOAD`, `LESSOPEN`,
     `GIT_*`).
   - `git`: before the subcommand, only `-C DIR` and options that set no
     configuration and no program (`--no-pager`, `-P`, the pathspec
     options, `--no-optional-locks`, `--no-replace-objects`) are allowed.
     Any other option (`-c`, `--config-env`, `--exec-path`, `--git-dir`)
     is exec. A read subcommand with `--output` is write. `git grep` with
     `-O` or `--open-files-in-pager` is exec.
   - `sed`: each script must be a known-safe form, else the step is exec.
     A safe script has only the commands `p P d D q Q = n N g G h H x { }`,
     `s` with the flags `g i I m M p` and a number, and `y`. Each command
     can have the addresses `N`, `$` or `/regex/`, and `!`. The allowed
     options are `-n -E -r -s -u -z -e -i` and their long forms. Any other
     option (`-f`) is exec. With `-i` and safe scripts, the step is write.
   - `rg` with `--pre`, `--pre-glob` or `--hostname-bin` is exec.
   - `sort` with `--compress-program` is exec; with `-o` or `--output` it
     is write.
   - `uniq` and `xxd` with two operands are write (the second operand is
     the output file).
   - `find` with `-exec`, `-execdir`, `-ok` or `-okdir` is exec; with
     `-delete`, `-fls`, `-fprint`, `-fprint0` or `-fprintf` it is write.
   - `less` with a `+` command that has `!` or `|` is exec; with `-o`,
     `-O`, `--log-file` or `--LOG-FILE` it is write.
   - `file` with `-C` or `--compile` is write.
   - `tree` is not in the table (`-o` writes a file), so it is exec.

   A long option can be an abbreviation (GNU `getopt_long`). The rules
   accept each prefix of the option name. An option letter in a group of
   short options (`-uo`) counts.

   A redirection to a file changes a read step to a write step. A step
   whose effect is in the auto set runs immediately. The auto set is the
   Local cvar `shell.autoEffects` (S4): a list of effect names, default
   `["read"]`. A name that is not an effect is a typed error when the
   value is set. The cvar is an execution gate, so an untrusted project
   cannot set it. For each other step, the host asks the user before the
   step runs. The worker sends a `shell_approval` frame to the attached
   clients. The first `answer_shell_approval` (approve or deny) is the
   answer. If no client is attached, or if all clients detach, there is no
   answer. No answer is a denial. The shell asks about the steps of a
   pipeline in order before any of them runs. A denial stops the script at
   that step. The steps before it ran, and their changes stay. The denied
   step, the other steps of its pipeline and all later steps do not run.
   The result gives the output and the exit status of each step that ran.
   It also tells how the script ended: finished, exited, or refused at
   step N (`denied` or `unanswered`). Shell state (`cd`, `export`) lasts
   for one call only. The kernel `bash()` in `ipython` is not gated. The
   reason: a cell is arbitrary Python, and Python can start any process
   without `bash()` (`subprocess`, `os.system`). A gate on `bash()` would
   thus not stop an effect; it would only seem to. Also, `bash()` gives a
   live process handle (pid, kill, tail, background notices) that an
   in-process shell cannot give. The `bash` tool is the gated surface.

Model: `bend/tools.bend`. Laws: `LAWS.bend` section (S7). Proofs:
`bend/proof_tools.bend`. Every input is free: any tools that join and
quit, any schemas, any paths, any scripts, any auto set, any answers of
the user.

| Law | Says |
| --- | --- |
| `roster_fixed` | No event changes the roster: tools that join go behind `dyn` (S7.1, S7.2). |
| `roster_sent_fixed` | Every request of a session sends the roster it started with (S7.1). |
| `dyn_reaches_joined` | A tool that joins is reachable through `dyn` (S7.2). |
| `dyn_drops_quit` | A tool that quits is not reachable through `dyn` (S7.2). |
| `schema_has_intent` | Every schema the harness sends has the intent parameter (S7.3). |
| `schema_versioned` | Every schema the harness sends has a version of at least 1 (S7.3). |
| `schema_keeps_params` | The harness keeps every parameter a tool declares (S7.3). |
| `schema_build_idempotent` | Building a built schema changes nothing (S7.3). |
| `path_rejects_escape` | A path that goes above its root is rejected, never clamped (S7.6). |
| `path_resolves_inside` | A path that stays under its root resolves (S7.6). |
| `gate_prefix` | The steps that ran are the first steps of the script, in order (S7.8). |
| `gate_needs_yes` | No more gated steps run than the user approved (S7.8). |
| `gate_deny_stops` | A denial stops the script at the denied step: the steps before it ran, it and every later step did not (S7.8). |
| `gate_finish_runs_all` | A script that finished ran every step (S7.8). |

Code: `eukhe-durable/src/harness/registry.rs` (`Registry::fix_roster`,
`RosterFixed`, `RosterChange`, the checks in `install` and `uninstall`),
`harness/harness/conversation.rs` `Conversation::configure`,
`harness/generation/round.rs` (`add_tools`);
`eukhe-core/src/durable/registry.rs` `create_eukhe_registry` (builds
every schema, then fixes the roster); `durable/tool_contract.rs`
(`parameters`, `build`); `durable/tool_surface/mod.rs` (`ToolSurface`,
the `dyn` tool, `report_issue`); `kernel/manager/mod.rs`
`mcp_tool_call` and the `mcp_call` request of the kernel's MCP lane
(`eukhe-runtime/src/rlm/repl.py`); `eukhe-docs/src/url.rs` (`Url::names`,
the one place that walks a URL path); `eukhe-core/src/durable/shell.rs`
(the `bash` tool and its approval) and the crate `eukhe-shell` (the
in-process shell, `effect.rs`, the gate).

Tie: the bridge test
`durable::tool_surface::bridge::the_rust_tool_surface_equals_the_bend_model`
drives a real registry with its roster fixed, a `ToolSurface` and
`tool_contract::build` against `bend/bridge_tools.bend` (the model `run`,
`step`, `dyn_call` and `build`): sessions with a roster, tools that join
(the registry is also asked to install them) and quit (the registry is
also asked to drop the roster), requests resolved as the Harness resolves
them, and schemas built twice. `bend/bridge_paths.bend` compares
`Url::names` with the model `resolve` and `stays`. `bend/bridge_shell.bend`
compares the gate of `eukhe-shell`
(`run::tests::the_gate_runs_as_its_model`) with the model `exec`.
Regression tests:
`harness::tests::registry::a_fixed_roster_rejects_every_change_of_the_tools_the_model_sees`,
`durable::tool_surface::tests` (an open session over two turns: every
request sends the same roster while a late tool is listed and run through
`dyn`, `report_issue` stores its row, and install and `configure` are
rejected), and the daemon test `dyn_tool_e2e` (a configured stdio MCP
server's tool is listed and called through `dyn`; the transcript holds one
tool loadout). Not modelled: the wire form of the version annotation, the
MCP listing and call through the kernel, and the row of a report. Their
tests tie them.
