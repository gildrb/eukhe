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
   process group and this environment: the environment of the daemon
   worker, with the session values on top (`EUKHE_CODING_AGENT_DIR`, and
   `EUKHE_CHAT_MEMORY` in a chat-memory session), less each credential
   (`kernel::manager::local_env` over `durable::rlm::session_env`). A
   credential is a provider credential that the provider code reads
   (`eukhe_ai::env_api_keys::credential_env_vars`, in any case), or a name
   whose upper case contains `API_KEY`, `APIKEY`, `TOKEN`, `SECRET`,
   `PASSWORD`, `PASSWD`, `PASSPHRASE`, `CREDENTIAL`, `PRIVATE_KEY` or
   `ACCESS_KEY`. A local kernel gets the same environment, but it keeps the
   credentials that the MCP config of the user reads (a `bearerTokenEnvVar`,
   a stdio `{"env": NAME}` reference, an `mcp:*` key in `auth.json` that
   names a variable). It never keeps a provider credential. The laws (G3)
   in `laws/child_env.bend` state this. The
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
8. Each step has a set of effects: read, write, exec, net, outside,
   protected and secret. A table in `eukhe-shell` (`effect.rs`) gives the
   effects of the command from its name, the `git` subcommand and some
   options. A command that is not in the table has the effect exec. Each
   redirection adds the effects of its target: a write to a path inside
   the workspace is write, outside it write and outside, to a protected
   path (S7 G1: eukhe's own settings and credentials, a `.git` directory,
   a directory on `PATH`, an ancestor of a protected or secret entry)
   write and protected; a read of a secret (ssh keys, credential stores)
   is read and secret. The paths that a step names add effects too: a
   word that is a secret or holds one (`cat ~/.ssh/id_ed25519`,
   `grep -r KEY ~`) adds secret; for a command that writes, a word
   outside the workspace adds outside and a protected word adds
   protected. The working directory adds secret, when it holds a secret,
   only to a command that reads it because it names no path of its own:
   `ls`, `du`, `find` with no starting point, `rg` (the first operand is
   the pattern unless `-e`, `-f`, `--regexp`, `--file` or `--files`
   gives it), `grep -r`/`-R` (the same), `git ls-files`, and `git grep`
   with no pathspec after `--` (an operand before `--` may be a
   revision). An option whose value may be the next word takes it, so
   the count of paths errs low. `echo hi`, `date` or `git -C repo log`
   in the home dir has no secret effect; `ls` or `rg x` there has. Every
   other command in the table reads only what it names or its input; a
   command that is not in the table is exec. A script outside the
   grammar is one step with exec and every effect of every command it
   holds (subshells, command substitutions, pipelines inside control
   flow). A read step only reads. These rules make sure of that:
   - A program name with `/` (`./cat`, `bin/stat`, `/usr/bin/rm`) is
     exec. The shell runs that file, whatever its name.
   - A step with an assignment (`PATH=./bin stat f`, `X=1`) is exec, and
     `export` with an operand is exec. The environment can make a reading
     command run another program (`PATH`, `LD_PRELOAD`, `LESSOPEN`,
     `GIT_*`).
   - `git`: before the subcommand, only `-C DIR` and options that set no
     configuration and no program (`--no-pager`, `-P`, the pathspec
     options, `--no-optional-locks`, `--no-replace-objects`) are allowed.
     Any other option (`-c`, `--config-env`, `--exec-path`, `--git-dir`,
     `-p`) is exec. A repository's configuration can make git run a
     program: the filesystem monitor, hooks, a pager, clean filters,
     external diff and textconv drivers, signature programs, ssh commands
     and credential helpers. Thus only these subcommands are read:
     `cat-file`, `count-objects`, `describe`, `for-each-ref`, `grep`,
     `log`, `ls-files`, `ls-tree`, `merge-base`, `name-rev`, `rev-list`,
     `rev-parse`, `shortlog`, `show`, `show-ref`, `version`, `diff
     --cached`, `branch` and `symbolic-ref` that only show. `branch`,
     `symbolic-ref`, `update-ref` and `init` that change refs are write.
     The shell runs each of these with `GIT_UNTRUSTED_REPO_ARGS`
     (`eukhe-shell`, also used by eukhe's own git probes: no fsmonitor, no
     hooks, no signature check, no pager, no fetch of missing objects),
     and `diff`, `log`, `show` with `--no-ext-diff --no-textconv`. Each of
     them is exec with `--textconv`, `--ext-diff`, `--filters`, a
     signature option or format (`%G`, `signature`, a `pretty.<name>`
     alias), `describe --dirty`/`--broken`, `ls-files -m`, `grep -O`,
     `branch --edit-description`. Every other subcommand is exec:
     `status`, `diff` of the work tree, `blame` and `add` hash work-tree
     files through the clean filters, which no argument can switch off;
     `commit`, `merge`, `rebase -x`, `bisect run`, aliases run commands. A
     subcommand that talks to a remote (`clone`, `fetch`, `ls-remote`,
     `pull`, `push`, `submodule`) is net and exec. A read subcommand with
     `--output` is also write.
   - `curl` with an option that writes a file (`-o`, `-O`, `-D`, `-c`,
     `-K`, `--output`, ...) is net and write; `wget` is net and write.
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

   A step runs immediately only when each of its effects is in the auto
   set. The auto set is the Local cvar `shell.autoEffects` (S4): a list of
   effect names from read, write, exec and net, default all four
   (`["read", "write", "exec", "net"]`, law `default_auto_is_grantable`).
   Outside, protected and secret are never in it: a step with one of them
   always asks (law `never_auto_is_routed`). A user who narrows the auto
   set is asked about the steps it no longer holds. A name that is not
   one of the four is a typed error when the value is set. The cvar is an
   execution gate, so an untrusted project cannot set it. For each other
   step, the host asks the user
   before the step runs. The question shows the step exactly as it runs:
   each control or bidi character in a word is escaped (`$'…'`), and the
   prompt keeps each line whole; Enter alone answers no. The worker
   sends a `shell_approval` frame (`effects`: the names) to the attached
   clients. The first `answer_shell_approval` (approve or deny) is the
   answer. The phone gateway (`eukhe gateway`) shows no question. A
   session whose only attached clients are the gateway asks no one: it
   runs the step at once, but it refuses at once a step with the effect
   protected or secret (the gateway rule, G5). If a TUI or the dashboard
   is attached too, that client gets the question. If no client is
   attached, or if all clients detach without an answer, a subagent's
   session hands the question to its parent, up to the root (G5); a root
   has no one to ask, and there is no answer. No answer is a denial. The
   shell asks about the steps of a pipeline in order before any of them
   runs. A denial stops the script at that step. The steps before it ran,
   and their changes stay. The denied step, the other steps of its
   pipeline and all later steps do not run. The result gives the output
   and the exit status of each step that ran. It also tells how the
   script ended: finished, exited, or refused at step N (`denied`,
   `unanswered` or `gateway_refused`). The text of a refused step, of a
   cell that did not run and of a document access that did not run comes
   from one renderer (`durable/shell.rs` `RefusalText`): what failed, then
   the model's next step, as `<what failed>. <next step>.`. Denied: do not
   try it again unless the user asks for it. Unanswered: ask the user to
   attach a client, or to allow its effect in `shell.autoEffects` if that
   is write, exec or net; or use read-only steps. Gateway refused: ask the
   user to run it from the eukhe TUI or the dashboard. Shell state (`cd`,
   `export`) lasts for one call only.

   The `ipython` tool is gated too. A cell is arbitrary Python: it can
   start any process (`subprocess`, `os.system`, the kernel `bash()`).
   Thus each cell is one step with the effect `exec`. A cell runs
   immediately only when `exec` is in `shell.autoEffects`, as it is by
   default. Else the host asks the user with the same `shell_approval`
   frame: request id `<call>:cell`, step 0, the code as the command
   (control and bidi characters escaped), effects `["exec"]`. The host
   asks before it starts the kernel, starts a job or starts the blocking
   budget. If the user denies, or no client is attached, or no answer
   comes, the cell does not run and the model gets the refusal's text
   (`ipython did not run (exec): ` and the text above). The `bash()`
   calls and the host requests of a cell run inside the cell that the
   gate let run; they do not ask again.
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
with the same `walk`. `bend/bridge_shell.bend` compares the gate of
`eukhe-shell` (`run::tests::the_gate_runs_as_its_model`) with the model
`join` and `exec` (see G2).
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
   runs. When the user denies, or no answer comes, or the gateway rule
   refuses it (G5), the access does not run, and the model gets the
   refusal's text (S7 item 8), opened by the access's effects
   (`(write+outside) it needs the user's approval, …`). When no client can
   answer (the session has no approval sink), the gate does not ask: each
   access that must ask does not run, and the model gets the unanswered
   refusal's text, opened the same way.
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

### G2. Shell classification

A step's effects are a set: every effect of every part of it (S7 item
8). The gate runs a step without a question only when the whole set is
within the auto set; outside, protected and secret are never within it.
By default the auto set holds every grantable effect (read, write, exec,
net; law `default_auto_is_grantable`, G5), so only a step with outside,
protected or secret asks.
A step has secret only when one of its parts names a path that is or
holds a secret (an operand, an option value, a redirection target, the
working directory of a command that reads it because it names no path).

Model: `bend/tools.bend` part 4 (`Step{id, effs}`, `grantable`,
`within`, `join`, `Part{own, secret}`, `part.effs`, `parts.effs`,
`parts.secret`, `exec`). Laws: `laws/shell_classification.bend` (alias
`Sg`). Proofs: `bend/proof_shell.bend`.

| Law | Says |
| --- | --- |
| `step_holds_every_part` | A step made of parts has every effect of every part. |
| `secret_needs_a_secret_path` | A step has secret only when one of its parts names a path that is or holds a secret: a step whose parts name none has no secret. |
| `secret_path_gives_secret` | A part that names a path that is or holds a secret gives its step secret. |
| `auto_needs_every_effect` | A step with one effect that is not in the auto set, or that no auto set may hold, does not run without a question. |
| `auto_never_sensitive` | A step with outside, protected or secret never runs without a question, whatever the auto set holds. |
| `composed_needs_every_part` | A step made of parts runs without a question only when every effect of every part is within the auto set. |
| `auto_runs_within` | A step whose effects are within the auto set runs and uses no answer. |
| `held_needs_a_yes` | A step whose effects are not within the auto set does not run without a yes; the script stops there. |

Code: `eukhe-types/src/shell.rs` (`ShellEffect`, `ShellEffects`,
`AutoSet`), `eukhe-shell/src/effect.rs` (`classify`,
`GIT_UNTRUSTED_REPO_ARGS`, `reads_cwd`), `run.rs` (`Shell::effects`,
the parts of a script outside the grammar from `parse::parts`),
`shown.rs` (`quote`, `visible`), `eukhe-tui/src/confirm.rs`
(`ConfirmPanel::approval`). Tie: `run::tests::the_gate_runs_as_its_model`
builds steps from parts whose effects and secret paths the path classes
of a temp workspace fix (reads of a secret, writes outside and to a
protected tree, redirections, scripts outside the grammar), in the
workspace or in the dir above it, which holds a secret (`echo` and
`date` there have no secret part; `ls` and `grep -r` have one for the
working directory), runs them with random auto sets (outside, protected
and secret in them too) and answers, and compares the steps that ran
with their effects and the end with `bend/bridge_shell.bend`. Every
command and redirection kind runs in each directory. Regression tests:
`every_effect_of_a_step_must_be_allowed`,
`only_a_step_that_reads_its_working_directory_reads_a_secret_in_it`,
`effect::tests::a_command_reads_the_working_directory_only_when_it_names_no_path`,
`effect::tests::a_git_step_that_can_run_a_repository_program_is_exec`,
`a_git_step_that_is_not_exec_runs_with_the_untrusted_repository_arguments`,
`shown::tests::a_hidden_character_is_escaped_and_bash_reads_the_word_back`,
`confirm::tests::an_approval_answers_no_on_enter_and_keeps_every_line`.
Not modelled: which paths a command reads or writes (every word counts;
the working directory only by `reads_cwd`), and what an exec step does
once approved.

### G4. Every runner of code goes through the gate

A tool that runs code declares a `Runner` in its registration (`extra`):
its caps (each effect that its code can have) and how the gate covers it
(`EachStep`: `bash`; `EachCall`: `ipython`). A tool that declares no
`Runner` runs no code of its own. A `Runner` is always gated: Rust cannot
write an ungated one.

Model: `bend/runners.bend` (`registry`, the tools that a default session
installs, in install order; `cell`, the gate of one call). Laws:
`laws/runners.bend` (alias `Ru`). Proofs: `bend/proof_runners.bend`.

| Law | Says |
| --- | --- |
| `gate_covers_every_runner` | Each tool of the registry whose caps hold `exec` is gated. |
| `ipython_gated_each_call` | `ipython` has the caps `exec` and the gate covers each call. |
| `cell_runs_only_within_or_approved` | A gated call runs only when its caps are within the auto set or the user approves it. |
| `cell_within_runs_unasked` | A call whose caps are within the auto set runs, and does not ask. |
| `cell_approved_runs` | A call outside the auto set that the user approves runs. |
| `cell_no_yes_stops` | A call outside the auto set without approval (a denial, no answer, no client) does not run. |
| `cell_exec_asks` | Code that can run a program is never within an auto set without `exec`. |

Code: `eukhe-core/src/durable/runner.rs` (`Runner`, `Gate`),
`durable/rlm/tool.rs` (the `ipython` gate), `durable/shell.rs` (the
`bash` runner). Tie: `durable::runner::tests` with
`bend/bridge_runners.bend`. `the_registry_is_its_model` dumps every tool
of an opened session (name, caps, gate) and compares it with `registry`.
`the_ipython_gate_runs_as_its_model` runs one real `ipython` call for
each auto set and asker (no client, no answer, deny, approve) and
compares whether it asked and how it ended with `cell`. Regression test:
`a_cell_runs_only_within_the_auto_set_or_approved`. Not modelled: the
dynamic tools behind `dyn` (MCP tools, `remote/<name>` functions of the
kernel).

### G5. A child's question reaches its root's user; the phone never waits

A subagent session (an RLM child) runs in its own worker and has no
client of its own, so its gated steps (S7 item 8: `bash` steps, `ipython`
cells) must ask the user of its root session. A session whose question no
client answers, because none is attached or all detach without an
answer, hands it to its parent session: the daemon command
`relay_shell_approval` (the parent's persisted session id, the request,
and `agent`, the name of the subagent that asks), which the supervisor
routes to the parent's worker like a turn-long wait. The parent asks its
own clients with a `shell_approval` frame that carries `agent`, or hands
the question on to its own parent. The first session up the chain whose
clients answer gives the answer (`{"answer": "approve" | "deny" |
"unanswered" | "gateway_refused"}`); when the root has no client that
answers, the answer is `unanswered` (a denial, with the usual message to
the model). The TUI's prompt names the subagent (`Subagent <name> asks:
allow shell step N (<effects>)?`), with the characters of the name that a
terminal hides or moves escaped. A frame without `agent` is the session's
own question.

A client tells its kind when it attaches (`clientKind`: `interactive`,
the default, or `gateway`). The phone gateway attaches as `gateway`: it
shows no question, so a session must never wait for its answer. A session
whose attached clients are all gateways asks no one and answers at once
by the gateway rule: a step with the effect protected (a write of eukhe's
own config or credentials, a `.git` or `.eukhe` dir, a `PATH` dir) or
secret is refused (`gateway_refused`), and every other step runs. The
bash result, the `ipython` result and the document tools' error tell the
model that the session runs only from the phone gateway and that the user
must run the step from the TUI or the dashboard. A subagent's question
that reaches such a session gets the same answer. When a TUI or the
dashboard is attached beside the gateway, that client gets the question;
if all of them detach without an answer while the gateway stays, the
gateway rule answers.

The auto set comes first: a step within it runs, and no one is asked
(`gate`). The auto set of a session whose user sets none holds every
grantable effect: read, write, exec and net. A step with outside,
protected or secret is never within any auto set, so its question goes
the route above: a TUI or the dashboard is asked, and from the phone
alone a write outside the workspace runs by the gateway rule while a
protected write or a secret is refused.

Model: `bend/approvals.bend` (`route`, a chain of sessions from the one
that asks up to its root: no client, clients that leave, clients that
answer, the gateway alone, clients that leave while the gateway stays;
`fate`, what becomes of a step with given effects; `default_auto`;
`gate`, the auto set before the route). Laws:
`laws/approvals.bend` (alias `Ap`). Proofs: `bend/proof_approvals.bend`.

| Law | Says |
| --- | --- |
| `child_answered_by_root` | When no session below the root has clients that answer, a subagent's question reaches the root's clients, and their answer is the verdict. |
| `nearest_answer_wins` | The first session up the chain whose clients answer gives the verdict, whatever the sessions above it. |
| `unanswered_only_when_quiet` | A question is unanswered (a denial) only when no session of the whole chain has clients that answer. |
| `quiet_is_unanswered` | Then it is unanswered: no session invents an answer. |
| `gateway_never_waits` | A step of a session whose only clients are the phone gateway never waits: no client gets a frame, the question does not go up the chain, and the session's gateway rule answers at once. |
| `gateway_refuses_protected` | The gateway rule refuses a step that writes a protected path. |
| `gateway_refuses_secret` | The gateway rule refuses a step that reads or writes a secret. |
| `gateway_runs_the_rest` | The gateway rule runs every other step unasked. |
| `left_to_the_gateway` | A question the interactive clients leave unanswered while the gateway stays falls to the gateway rule, not up the chain. |
| `gateway_rules_a_subagent` | A subagent's question that reaches a session whose only clients are the gateway fares as that session's own step. |
| `default_auto_is_grantable` | The auto set of a session whose user sets none holds exactly the grantable effects: read, write, exec and net. |
| `never_auto_is_routed` | A step with outside, protected or secret never runs unasked through the auto set, in any session: its question goes its route. |
| `never_auto_asks_the_client` | In a session whose client answers (the TUI, the dashboard), such a step asks that client, and its answer decides. |
| `outside_runs_only_by_the_gateway` | From the phone alone, a write outside the workspace that is not protected and touches no secret runs, and only by the gateway rule. |
| `guarded_refused_from_the_phone` | From the phone alone, a protected write or a secret is refused at once, whatever the auto set. |

Code: `eukhe-daemon/src/shell_approval.rs` (`ShellApprovals::ask`,
`relay`), `worker.rs` (the relay over the supervisor link),
`supervisor/routing.rs` (the relay's budget), `eukhe-tui/src/session_ui/
settings.rs` (the prompt), `worker/connection.rs` (the client kind at
attach), `eukhe-gateway/src/link.rs` (the gateway attaches as
`gateway`), `eukhe-core/src/settings/cvar/table.rs` (`SHELL_AUTO_EFFECTS`,
the default auto set). Ties: `shell_approval::bridge::
the_approval_route_is_its_model` with `bend/bridge_approvals.bend` runs
every chain of up to 3 sessions with a write, a run of a program, a
protected write and a secret read, and generated longer ones, on real
`ShellApprovals`, each relaying through its parent's real handler, and
compares which sessions showed the question, whether each frame names
the subagent, and how it ended. `durable::shell::tests::
the_default_auto_set_is_its_model` reads the real auto set of a session
whose user sets none and compares, with the same model, the effects it
holds and whether the gate runs each of the 127 steps of one to seven
effects unasked. Regression tests:
`with_no_auto_set_only_the_write_outside_the_workspace_asks` (no client:
a write and a run of a program run, a write outside the workspace stops
the script unanswered),
`rlm_child_approval_e2e::a_subagent_step_runs_when_the_root_client_approves`
(a real supervisor, a root with an attached client, a subagent whose
`bash` step writes under an auto set of `read`) and
`shell_approval_e2e::a_phone_only_session_runs_steps_unasked_and_refuses_a_protected_write`
(a real supervisor and a client attached as `gateway`, under an auto set
of `read`: a write and a run of a program run unasked by the gateway
rule, a write of `.eukhe/settings.json` is refused at once with the
gateway message). Not modelled: the supervisor's routing of
the command (a parent whose worker is not resident is not asked; the
question is then unanswered), a client attaching while a question waits
above it. The dashboard shows a subagent's question without its name.

### S8. The documents tools

The documents tools are `read`, `edit`, `grep` and `glob`, and the kernel
functions `read()`, `write()`, `edit()`, `grep()` and `glob()` (crate
`eukhe-docs`). They share one edit store per session.

1. An `edit` of many files is all or nothing for conflicts. The writer
   locks every path of the call, in one order. Then it checks each file:
   its bytes must be the bytes the edit was applied to, and an `MV`
   destination must not exist. If one check fails, no file is written.
   Then the writer writes the files in order, and stops at the first
   failure. The reply tells which files landed (with their new tags) and
   which did not: "Applied to a; NOT applied to b, c". It never says that
   nothing was written when a file landed. A rename that landed but whose
   directory sync failed, and a move whose source stays, are landed writes
   with a warning.
2. A retry of a start or end insert with the old tag, after the insert
   landed, does not insert it again: the result says that the edit is
   already in the file.
3. `write()` replaces an existing file only when its bytes on disk are a
   version that this session saw: a read, a grep, or its own write or
   edit. Else it writes nothing and tells the model to read the file
   first. A new file is created. A replaced file keeps its BOM, line
   endings and mode; a warning tells when the content had other line
   endings, or when the old file was not UTF-8.
4. `MV` never replaces a file. The destination gets the bytes through a
   hard link, which fails on a name that exists.
5. A temporary file is `.eukhe-tmp-<hash of the name>-<pid>-<n>`, so a long
   name still fits. Its writer locks it. Each write of a target removes
   the temporary files of that target that no writer locks (a crash left
   them). `grep` and `glob` do not show these names.
6. A line ends at `\n`. A `\r` before `\n` is part of the CRLF ending of
   that line; a lone `\r` is text. `read`, `grep` and `edit` use this one
   line model. An edit keeps every byte outside its lines. A new or
   changed line gets the ending of the line before it (at the start of
   the file: the first ending of the file, else LF).
7. The tag of a grep result is the hash of the bytes that grep searched,
   not of a second read of the file.
8. A line is seen only when its row reached the model, after the output
   bound cut the middle of a long result. An edit anchor on a line that
   is not seen is rejected; the rejection shows the line and marks it
   seen, so the same edit applies on a retry. After an edit lands, the
   lines that were seen before and the lines that the edit wrote stay
   seen.
9. `grep` and `glob` tell each file that they skip or cut, with the
   reason and the count: binary, unreadable, searched only in part,
   excluded directories, symlinks, walk errors, the match caps. A
   continuation (`skip=N`, a line range) gives the next results.
10. One size limit (`MAX_SNAPSHOT_FILE_BYTES`, 4 MiB) applies everywhere. A
    larger file has no tag; the message tells the model to read it in
    ranges and to change it with `write()` or `bash`. A file that is not
    UTF-8 gets a message with its path and its encoding.

Models: `bend/doc_commit.bend`, `bend/doc_seen.bend`,
`bend/doc_lines.bend`, `bend/doc_tags.bend`, `bend/doc_search.bend`. Laws:
`laws/documents.bend`. Proofs: `bend/proof_documents.bend`,
`bend/proof_doc_lines.bend`.

| Law | Says |
| --- | --- |
| `edit_reports_what_landed` | The reply calls a file applied exactly when its new content is on disk (S8.1). |
| `edit_all_or_nothing_on_conflict` | When one file changed since the edit staged it, no file lands (S8.1). |
| `edit_lands_every_file` | With no changed file and no failed write, every file lands (S8.1). |
| `write_never_loses_unseen` | A write over a version the session did not see is refused and changes nothing (S8.3). |
| `write_writes_seen` | A write over no file or a seen version writes it (S8.3). |
| `move_never_overwrites` | A move to a name that exists is refused and changes nothing (S8.4). |
| `move_moves` | A move to a free name moves the content (S8.4). |
| `temp_sweep_never_held` | A sweep never removes a temporary file a live writer locks (S8.5). |
| `temp_sweep_only_own` | A sweep removes only temporary files of its target (S8.5). |
| `temp_sweep_removes_free` | A sweep removes every temporary file of its target that no writer locks (S8.5). |
| `load_persist_roundtrip` | A file loaded and written with no edit is the same bytes (S8.6). |
| `edit_keeps_untouched_bytes` | An edit keeps every byte outside its lines (S8.6). |
| `grep_line_is_read_line` | `grep` and `read` show the same line text at the same number (S8.6). |
| `tag_names_shown_text` | The tag of a result names the text that its rows come from (S8.7). |
| `edit_only_seen_lines` | An edit applies only when every anchor is a seen line (S8.8). |
| `edit_seen_applies` | An edit whose anchors are all seen applies (S8.8). |
| `reveal_then_retry` | A rejected edit applies on a straight retry (S8.8). |
| `grep_accounts_every_file` | Each walked entry is in exactly one class, and the classes add up to the walk (S8.9). |
| `grep_notes_every_gap` | A class of skipped, cut or not-searched entries has its notice exactly when it is not empty (S8.9). |
| `grep_notes_every_cut` | A shown file whose matches were cut has its own notice (S8.9). |
| `continuation_progresses` | A continuation gives a page that is not empty (S8.9). |
| `continuation_contiguous` | A page and the page of its continuation are the next part of the list: nothing left out, nothing twice (S8.9). |
| `continuation_disjoint` | A page and the page of its continuation have no item in common (S8.9). |

Code: `eukhe-docs/src/write.rs` (`LockedWriter::write_all`, `publish`,
`write_file`, the sweep), `hashline/mod.rs` (`apply_hashline`, `commit`),
`hashline/patcher.rs` and `hashline/apply.rs` (the line origins, `persist`,
the seen guard), `text.rs`, `read/mod.rs`, `grep/`, `glob.rs`, `store.rs`
(`saw_bytes`); `eukhe-core/src/durable/documents/tool.rs` (`bounded`) and
`requests.rs` (`Cut`, `Done::mark_seen`).

Tie: the bridge tests `write::bridge` (an edit of many files with injected
faults and conflicts, the write tool with writes by another program, the
move, the sweep with live locks), `hashline::bridge` (random bytes with
`\r`, `\n`, `\r\n` and a BOM through a real read and edit), `grep::bridge`
(the rows of read and grep, and a grep whose file changes between the
search and the record), `grep::bridge_accounts` and `glob::bridge`
(generated trees, every continuation followed once), and
`durable::documents::bridge` (a long read cut by the output bound, then
edits at anchors in and around the cut). Not modelled: the bytes of the
notice texts, and the line model of the rebase of a stale edit (it maps
lines through a line diff).
