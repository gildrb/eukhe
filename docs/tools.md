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
   of the generic MCP servers of the session. `ssh://<host>/<path>` reads
   one remote text file (item 9 has the rules). `glob` rejects all
   schemes; `grep` does not find a scheme path.
6. Confinement. A URL path is a list of `/`-separated segments under the
   root of its scheme. `..` goes up one segment; `.` and an empty segment
   do not move. A path that goes above its root gets the rejection
   `escapes`. The path is not clamped to the root. A path that stays under
   its root resolves. After this lexical check, a `repo://` or `skill://`
   read resolves the real path (it follows symlinks) and requires it under
   the real path of the root. A symlink out of the root also gets the
   rejection `escapes`. This guard is against the filesystem; the model
   stays the lexical rule. An `ssh://` path has one of two roots on its
   host: the remote `/`, or the remote home when the first segment is
   exactly `~`. eukhe cannot see the remote filesystem, so a remote
   symlink is not checked. A plain file path is not confined; this is the
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
9. Remote reads (`ssh://`). An `ssh://` read is new outbound traffic, so
   it is off by default:
   1. The host must be in the setting `ssh.hosts` (a list of strings;
      default empty). The setting is Global: eukhe reads it from the
      global `settings.json` only, and a project cannot set it. The host
      must agree with an entry as written (`box`, `me@box`). When the list
      is empty, each `ssh://` read gets the rejection `not_allowed`, and
      the message names `ssh.hosts`.
   2. The host is letters, digits, `.`, `-`, `_` and `@`. It must not
      start with `-`. Other hosts get the rejection `arguments`. Put
      ports, users and options in `~/.ssh/config`.
   3. `ssh://box/etc/hosts` reads `/etc/hosts`. `ssh://box/~/notes/a.md`
      reads `notes/a.md` under the remote home. `ssh://box/~/../x` and
      `ssh://box/../x` get the rejection `escapes` (item 6).
   4. eukhe runs the `ssh` program of the user with the user's
      `~/.ssh/config`: `ssh -T -o BatchMode=yes -o ConnectTimeout=<s>
      -o ClearAllForwardings=yes -- <host> "cat -- '<path>'"`. eukhe
      handles no key and no password. With `BatchMode`, a host that asks
      for a password or a passphrase fails at once. The path goes to the
      remote shell as one single-quoted word (`'` becomes `'\''`). Thus no
      character of the path is shell syntax on the remote host. The
      remote login shell must be a POSIX shell.
   5. The output cap of the call (S2) keeps the first bytes of the file.
      eukhe counts the remaining bytes, and the first line of the reply
      gives the number that the cap dropped. The blocking budget
      (`toolBlockingBudgetMs`) ends the read: `ssh` runs in its own
      process group, and eukhe kills the group at the deadline. A read
      that did not fill the cap by the deadline gets the rejection
      `timeout`. A read that filled the cap gives its bytes, and the
      first line tells that the cap dropped that number of bytes or more.
   6. The read must run in a tool call. A kernel `read()` outside a tool
      call has no output cap, so it gets the rejection `arguments`.
   7. The rejections are typed: `host` (an unknown host, a host that does
      not connect, a host key that is not known or that changed), `auth`
      (the host refused each key), `not_found`, `is_directory`,
      `permission_denied`, `binary` (not UTF-8 text, or a NUL byte),
      `timeout`, and `io` (no `ssh` on `PATH`, or another failure).
   8. The read is of one whole file, as text. It has no `[path#TAG]`
      header and no selector, and its lines are not edit anchors.

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
(`eukhe-runtime/src/rlm/repl.py`); `eukhe-docs/src/url.rs` (`walk`, the
one place that walks a URL path, under `Url::names` and `Url::remote`);
`eukhe-core/src/durable/documents/ssh.rs` (`SshRead`: the `ssh.hosts`
check, the `ssh` arguments, the bounded read and the typed errors);
`eukhe-core/src/durable/shell.rs` (the `bash` tool and its approval) and
the crate `eukhe-shell` (the in-process shell, `effect.rs`, the gate).

Tie: the bridge test
`durable::tool_surface::bridge::the_rust_tool_surface_equals_the_bend_model`
drives a real registry with its roster fixed, a `ToolSurface` and
`tool_contract::build` against `bend/bridge_tools.bend` (the model `run`,
`step`, `dyn_call` and `build`): sessions with a roster, tools that join
(the registry is also asked to install them) and quit (the registry is
also asked to drop the roster), requests resolved as the Harness resolves
them, and schemas built twice. `bend/bridge_paths.bend` compares
`Url::names` with the model `resolve` and `stays`; `Url::remote` walks
with the same `walk`. `bend/bridge_shell.bend`
compares the gate of `eukhe-shell`
(`run::tests::the_gate_runs_as_its_model`) with the model `exec`.
Regression tests:
`harness::tests::registry::a_fixed_roster_rejects_every_change_of_the_tools_the_model_sees`,
`durable::tool_surface::tests` (an open session over two turns: every
request sends the same roster while a late tool is listed and run through
`dyn`, `report_issue` stores its row, and install and `configure` are
rejected), the daemon test `dyn_tool_e2e` (a configured stdio MCP
server's tool is listed and called through `dyn`; the transcript holds one
tool loadout), `url::tests::an_ssh_url_*` (the host and path rules), and
`durable::documents::ssh::tests` (a fake `ssh` that records its arguments
and plays hosts: a path with shell syntax reads the file of that name and
runs nothing, each failure is its typed error, the output cap counts the
dropped bytes, and the budget kills `ssh`). Not modelled: the wire form of
the version annotation, the MCP listing and call through the kernel, the
row of a report, and the remote side of an `ssh://` read. Their tests tie
them.

### G1. Path policy

One path policy judges each path that an agent tool reads or writes.
The `bash` tool (S7 item 8) and the document tools (`read`, `write`,
`edit`, `grep`, `glob`, and the kernel `fs.*` requests) use the same
policy (`eukhe_types::path_policy::PathPolicy`). Thus the two cannot
judge a path differently.

1. The real path. The policy judges the real path of a path, not the
   path as written. `resolve` follows each symlink on the part of the
   path that exists. It also follows a dangling symlink: a write through
   it creates the target. `.` does not move. `..` goes up from the real
   directory, not from the written name. `..` of `/` is `/`. The part
   that does not exist stays as written. Thus a symlink gets the class of
   its target. After 40 symlinks (`MAX_LINKS`, as Linux) the path loops:
   the resolution does not follow more symlinks, and the policy does not
   trust the rest of the path.
2. The classes. Each real path has one class. When more than one class
   applies, the first class in this list is the class:
   1. Secret: the path is a secret entry, or it is under one.
   2. Protected: a protected rule covers the path, or the path is an
      ancestor of a protected or secret entry. (A move or a removal of
      the ancestor moves or removes the entry.)
   3. Inside: the path is under a workspace root.
   4. Outside: all other paths.

   A path whose symlinks loop is never Inside. It is Outside, or
   Protected or Secret when one of these applies.
3. The protected set. The settings loaders give the protected set; there
   is no separate list (`durable::path_policy::policy`):
   - the agent dir and each entry directly in it (`settings.json`,
     `config.cfg`, `subagent.cfg`, `models.json`, `auth.json`,
     `binds.cfg`): a `Dir` rule;
   - the profile dir (`agents/<agent>.cfg`): a `Tree` rule;
   - the project config dir of the session (`<cwd>/.eukhe`): a `Tree`
     rule, and each `.eukhe` directory below the workspace root: a
     `Named` rule;
   - each settings file that the session loads and reads again
     (`EukheSettings::watched`): a `Tree` rule;
   - each `.git` directory below the workspace root: a `Named` rule (its
     config and its hooks name programs that git runs);
   - each directory on `PATH`: a `Dir` rule (a file in it replaces a
     command).

   A `Named` rule looks at the part of the path below its workspace root
   (all of the path when no root holds it). The policy makes each entry
   real when it starts.
4. The secret set: `auth.json` in the agent dir, the Prime CLI config,
   the credential stores of other programs in the home dir (`.ssh`,
   `.aws`, `.azure`, `.config/gcloud`, `.config/gh`,
   `.docker/config.json`, `.kube`, `.gnupg`, `.password-store`,
   `.local/share/keyrings`, `.netrc`, `.git-credentials`, `.npmrc`,
   `.pypirc`, `.cargo/credentials`, `.cargo/credentials.toml`), and the
   files that `AWS_SHARED_CREDENTIALS_FILE`, `AWS_CONFIG_FILE` and
   `CLOUDSDK_CONFIG` name.
5. The effects of an access. A read or a list of a path is read; of a
   Secret path, read and secret. A search (a `grep` of a directory) of a
   path that is a secret or that holds a secret is read and secret. A
   write is write when Inside, write and outside when Outside, write and
   protected when Protected, and write and secret when Secret.
6. The gate of the document tools (`DocumentsGate`). A document tool
   resolves each path one time. It gives that resolution (`RealPath`: the
   real path, and whether its symlinks looped) to the gate before the
   access. The access then occurs on that real path. The gate judges the
   resolution as it is. It does not resolve the real path again: a second
   resolution can lose a loop. An access runs without a question only
   when the auto set (`shell.autoEffects`, S7 item 8) holds each of its
   effects. Outside, protected and secret are never in the auto set.
   Thus:
   - a write runs without a question only Inside, and only when the auto
     set holds write;
   - a read of a secret always asks;
   - each other access asks when the auto set does not hold all of its
     effects.

   The question goes through the approval sink of a `bash` step: the
   `shell_approval` frame, with the verb and the real path as the command
   (`write /path`), and the effects. When the user approves, the access
   runs. When the user denies, or no answer comes, the access does not
   run, and the model gets the reason. When no client can answer (the
   session has no approval sink), the gate does not ask: each access that
   must ask does not run, and the model gets an error that names the
   effects that need the approval of the user.
7. A write occurs on the real path. The writer locks the real path, then
   resolves the path again. When the real path changed (a symlink was
   made or moved), the write stops, and nothing is written. A replaced
   file keeps its mode. A created file gets the default mode: it has no
   execute bit.

Model: `bend/path_policy.bend` (alias `Pp`: `real` with `max_links`
links of fuel, `class`, `holds`, `effs`, `runs`, `asks`, the store
`run` and `guarded`). Laws: `laws/path_policy.bend` (alias `Pg`).
Proofs: `bend/proof_path_policy.bend`. Every input is free: any
symlinks (loops too), any policy, any paths, any auto set, any answers.

| Law | Says |
| --- | --- |
| `path_real_has_no_link` | Unless its symlinks looped, no prefix of the real path of a path is a symlink (G1.1). |
| `path_secret_wins` | A path whose real path is under a secret entry is Secret (G1.2). |
| `path_inside_is_safe` | A path is Inside only when its symlinks did not loop, no secret covers it, no rule protects it, it is no ancestor of an entry, and a root holds it (G1.2). |
| `path_ancestor_guarded` | An ancestor of a protected or secret entry is Protected or Secret (G1.2). |
| `gate_write_auto_only_inside` | A write runs without a yes only Inside (G1.6). |
| `gate_secret_read_needs_yes` | A read of a secret runs only on a yes (G1.6). |
| `gate_yes_runs` | The yes of the user runs each access (G1.6). |
| `gate_inside_write_runs` | With write in the auto set, a write Inside runs without a question (G1.6). |
| `config_needs_yes` | No sequence of agent writes without a yes changes a protected or secret location (G1.6, G1.7). |

Code: `eukhe-types/src/path_policy.rs` (`resolve`, `RealPath`,
`PathPolicy::class_of_resolved`, `holds_secret_of_resolved`, `PathRule`,
`MAX_LINKS`), `eukhe-core/src/durable/path_policy.rs` (`policy`,
`session_policy`, `effects`, `DocumentsGate`), `eukhe-docs/src/gate.rs`
(`AccessGate`, `Access`), `eukhe-docs/src/write.rs` (`write_file`,
`LockedWriter`), `eukhe-shell/src/run.rs` (the effects of the paths of a
step: `PathPolicy::class` and `holds_secret`). Tie:
`durable::path_policy::bridge::path_policy_and_gate_match_the_model`
with `bend/bridge_path_policy.bend`. It runs 200 scenarios from a fixed
seed. Each scenario makes a tree in a temp dir (directories, files, and
symlinks with targets from `/` and from their directory, dangling targets
and loops too) and a policy (roots, `Tree`, `Dir` and `Named` rules,
secret entries). For each query path it compares the loop bit, the real
path, the class, `holds_secret`, and, for a read, a list, a search and a
write with a random auto set and answer, whether the real `DocumentsGate`
let the access run and whether it asked. Then it writes through
`Documents::write` with answers that are never yes, and compares whether
the gate asked, the path that the question names, and the content of each
protected or secret file after the writes (`Pp.guarded` of `Pp.run`: law
`config_needs_yes`). Regression tests:
`durable::path_policy::tests::every_loader_file_is_guarded_and_a_project_file_is_inside`,
`durable::path_policy::tests::a_write_whose_links_looped_asks_even_when_its_real_path_is_inside`,
and `path_policy::tests` in `eukhe-types`. Not modelled: a change of the
filesystem between the gate and the lock (the writer checks it), and the
file modes.
