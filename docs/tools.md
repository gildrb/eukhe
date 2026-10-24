# Harness laws: tool surface

Shared rules (what a law secures, the adversary, H1 to H6): [harness.md](harness.md).

### S7. The tool surface

The model can call: the roster tools, the tools behind `dyn`, the internal URLs, the shell.

1. The roster is the tool list each request sends. It is fixed when the
   session opens, before its first request. After that, the harness
   rejects each roster change with the typed error `RosterFixed`:
   - an install or uninstall of an extension that changes the tools the model sees;
   - a `configure` of `tools`, `modelTools` or `extensions`;
   - an `add_tools` of a tool round.

   Each request sends the same roster, so the prompt cache stays valid.
2. A later tool (an MCP server tool, a host tool that joins) does not go
   into the roster. The roster tool `dyn` reaches it:
   - `dyn` without `name` lists the dynamic tools;
   - `dyn` with `name` and `arguments` runs one;
   - `mcp/<server>/<tool>` is a tool of an MCP server the user configured; the kernel's MCP client runs it;
   - a host tool joins with `ToolSurface::join` and leaves with `ToolSurface::quit`. A tool that left is not reachable.
3. Each schema the harness sends has the intent parameter `i` (optional,
   first) and a version of 1 or more: the annotation `title: "v<n>"` in the
   schema. Every wire API keeps it. At open the session builds every
   schema: it adds `i` if missing, keeps each declared parameter in its
   place, and sets the declared version (1 if none). Building a built
   schema changes nothing. `codemode` gets `i` and `v1` this way.
4. `report_issue` (behind `dyn`) is the AutoQA path. An agent reports a
   tool that failed or did not do what its description says, with the
   arguments `tool` and `description`. The session stores the report as a
   display-only row of custom type `eukhe.tool_issue`. The user sees the
   row; the model context does not get it.
5. Internal URLs. The `read` tool (and the kernel `read()`) accepts
   `scheme://path` in place of a file path:

   | URL | Reads |
   | --- | --- |
   | `repo://<path>` | a file or directory under the workspace root (the session's working directory) |
   | `skill://<name>/<path>` | a file under the directory of skill `name` |
   | `skill://<name>` | its `SKILL.md` |
   | `agent://<name\|id>` | the whole chat of a subagent the conversation started |
   | `memory://` | the chat view |
   | `memory://<id>` | message `id` whole (with its images) |
   | `memory://<id>/<n>` | line `id+n` |
   | `mcp://<server>` | the resource list of a server |
   | `mcp://<server>/<uri>` | one resource (text; a binary part is a note with its size and MIME type), bounded like any read |
   | `ssh://<host>/<path>` | one remote text file (rules: item 9) |

   - A `repo://` or `skill://` read is a normal file read: `[path#TAG]` header, lines are edit anchors.
   - An `mcp://` server must be one of the session's generic MCP servers.
   - An unknown scheme gets the rejection `scheme`.
   - `glob` rejects all schemes; `grep` does not find a scheme path.
6. Confinement. A URL path is a list of `/`-separated segments under the
   root of its scheme. `..` goes up one segment; `.` and an empty segment
   do not move.
   - A path above its root gets the rejection `escapes`. It is never clamped to the root.
   - A path that stays under its root resolves.
   - After this lexical check, a `repo://` or `skill://` read resolves the real path (follows symlinks) and requires it under the real path of the root. A symlink out of the root also gets `escapes`. This guard is against the filesystem; the model stays the lexical rule.
   - An `ssh://` path has one of two roots on its host: the remote `/`, or the remote home when the first segment is exactly `~`. eukhe cannot see the remote filesystem, so it does not check a remote symlink.
   - A plain file path is not confined (unchanged): absolute paths and `..` from the working directory still read any file.
   - `lexical_normalize` keeps the filesystem rule (`/..` is `/`) and is not used for URL paths.
7. The shell and the approval gate. The `bash` tool (`bash@1`, extension
   `eukhe.shell`) is in the roster at open. It runs a script in process
   (crate `eukhe-shell`), not a system shell per script.
   - A script is a list of steps. A step is one simple command. Steps join with `;`, newline, `&&`, `||`, `|`.
   - Redirections per step: `<`, `>`, `>>`, `2>&1`, `&>`.
   - Expansions: `$NAME`, `${NAME}`, `$?`, a leading `~`, the patterns `*`, `?`, `[...]`.
   - Built in: `cat`, `ls`, `head`, `tail`, `wc`, `echo`, `pwd`, `mkdir`, `rm`, `rmdir`, `touch`, `cp`, `mv`; `grep` on the ripgrep engine (`grep-regex`, `grep-searcher`). All other commands, and these with options the shell does not know, run as external processes.
   - Each external process gets its own process group and this environment: the daemon worker's environment, plus the session values (`EUKHE_CODING_AGENT_DIR`; `EUKHE_CHAT_MEMORY` in a chat-memory session), minus each credential (`kernel::manager::local_env` over `durable::rlm::session_env`).
   - A credential is a provider credential the provider code reads (`eukhe_ai::env_api_keys::credential_env_vars`, any case), or a name whose upper case contains `API_KEY`, `APIKEY`, `TOKEN`, `SECRET`, `PASSWORD`, `PASSWD`, `PASSPHRASE`, `CREDENTIAL`, `PRIVATE_KEY` or `ACCESS_KEY`.
   - A local kernel gets the same environment, but keeps the credentials the user's MCP config reads (a `bearerTokenEnvVar`, a stdio `{"env": NAME}` reference, an `mcp:*` key in `auth.json` that names a variable). It never keeps a provider credential. Runs as the compiled model `bend/child_env.bend` (`kernel::manager::child_env` calls entry `bend/ffi_child_env.bend`). Laws (G3): `laws/child_env.bend`.
   - Pipeline commands run at the same time, joined by OS pipes; the kernel pipe buffer limits each pipe. When a command stops, its input pipe closes, and the writer to that pipe stops too: an external process gets SIGPIPE, a shell command stops with status 141. Thus `yes | head -n 3` stops.
   - A script with other syntax (control flow, functions, subshells, command substitution, here-documents, background jobs) is one `exec` step; `bash -c` runs it.
   - The tool obeys the S2 limits. Output goes through the call's `Truncation` as the steps write it: the result keeps output within the cap; the `output_bounded` diagnostic counts each dropped byte. With the opt-out, the result keeps all output.
   - A call blocks for the blocking budget (`toolBlockingBudgetMs`) at most. A longer script becomes a job (`JobKind::Shell`) in the session's `JobTable`; the call settles `detached` with the output so far and the job id. The script continues, and a gated step still asks the user. When the script ends, it settles its job and sends a `JobSettled::Shell` row (`[job-settled job:ID status:S]` and the bounded output) through the job-settled wake, as a detached cell does.
   - The job's kill stops the script and kills the process group of each running external process; the job settles `killed`.
8. Each step has a set of effects: read, write, exec, net, outside,
   protected, secret. A table in `eukhe-shell` (`effect.rs`) gives a
   command's effects from its name, the `git` subcommand and some options.
   A command not in the table is exec.
   - Each redirection adds the effects of its target: a write inside the workspace is write; outside it, write and outside; to a protected path (S7 G1: eukhe's own settings and credentials, a `.git` directory, a directory on `PATH`, an ancestor of a protected or secret entry), write and protected. A read of a secret (ssh keys, credential stores) is read and secret.
   - Paths a step names add effects: a word that is or holds a secret (`cat ~/.ssh/id_ed25519`, `grep -r KEY ~`) adds secret. For a command that writes, a word outside the workspace adds outside; a protected word adds protected.
   - The working directory adds secret (when it holds one) only to a command that reads it because it names no path of its own: `ls`, `du`, `find` with no starting point, `rg` (the first operand is the pattern unless `-e`, `-f`, `--regexp`, `--file` or `--files` gives it), `grep -r`/`-R` (the same), `git ls-files`, and `git grep` with no pathspec after `--` (an operand before `--` may be a revision). An option whose value may be the next word takes it, so the path count errs low. In the home dir, `echo hi`, `date` or `git -C repo log` has no secret effect; `ls` or `rg x` has.
   - Every other table command reads only what it names or its input.
   - A script outside the grammar is one step with exec and every effect of every command it holds (subshells, command substitutions, pipelines inside control flow).

   A read step only reads. These rules make sure of that:
   - A program name with `/` (`./cat`, `bin/stat`, `/usr/bin/rm`) is exec: the shell runs that file, whatever its name.
   - A step with an assignment (`PATH=./bin stat f`, `X=1`) is exec, and `export` with an operand is exec. The environment can make a reading command run another program (`PATH`, `LD_PRELOAD`, `LESSOPEN`, `GIT_*`).
   - `git`: before the subcommand, only `-C DIR` and options that set no configuration and no program (`--no-pager`, `-P`, the pathspec options, `--no-optional-locks`, `--no-replace-objects`) are allowed. Any other (`-c`, `--config-env`, `--exec-path`, `--git-dir`, `-p`) is exec. Repository config can make git run a program (fsmonitor, hooks, pager, clean filters, external diff and textconv drivers, signature programs, ssh commands, credential helpers), so:
     - read subcommands: `cat-file`, `count-objects`, `describe`, `for-each-ref`, `grep`, `log`, `ls-files`, `ls-tree`, `merge-base`, `name-rev`, `rev-list`, `rev-parse`, `shortlog`, `show`, `show-ref`, `version`, `diff --cached`, and `branch` and `symbolic-ref` that only show;
     - write: `branch`, `symbolic-ref`, `update-ref` and `init` that change refs;
     - the shell runs each of these with `GIT_UNTRUSTED_REPO_ARGS` (`eukhe-shell`, also used by eukhe's own git probes: no fsmonitor, no hooks, no signature check, no pager, no fetch of missing objects), and `diff`, `log`, `show` with `--no-ext-diff --no-textconv`;
     - each of them is exec with `--textconv`, `--ext-diff`, `--filters`, a signature option or format (`%G`, `signature`, a `pretty.<name>` alias), `describe --dirty`/`--broken`, `ls-files -m`, `grep -O`, `branch --edit-description`;
     - every other subcommand is exec: `status`, work-tree `diff`, `blame` and `add` hash work-tree files through the clean filters, which no argument can switch off; `commit`, `merge`, `rebase -x`, `bisect run`, aliases run commands;
     - a subcommand that talks to a remote (`clone`, `fetch`, `ls-remote`, `pull`, `push`, `submodule`) is net and exec;
     - a read subcommand with `--output` is also write.
   - `curl` with an option that writes a file (`-o`, `-O`, `-D`, `-c`, `-K`, `--output`, ...) is net and write; `wget` is net and write.
   - `sed`: each script must be a known-safe form, else exec. Safe: only the commands `p P d D q Q = n N g G h H x { }`, `s` with the flags `g i I m M p` and a number, and `y`; addresses `N`, `$`, `/regex/`, and `!`. Allowed options: `-n -E -r -s -u -z -e -i` and their long forms. Any other option (`-f`) is exec. `-i` with safe scripts is write.
   - `rg` with `--pre`, `--pre-glob` or `--hostname-bin` is exec.
   - `sort` with `--compress-program` is exec; with `-o` or `--output`, write.
   - `uniq` and `xxd` with two operands are write (the second operand is the output file).
   - `find` with `-exec`, `-execdir`, `-ok` or `-okdir` is exec; with `-delete`, `-fls`, `-fprint`, `-fprint0` or `-fprintf`, write.
   - `less` with a `+` command that has `!` or `|` is exec; with `-o`, `-O`, `--log-file` or `--LOG-FILE`, write.
   - `file` with `-C` or `--compile` is write.
   - `tree` is not in the table (`-o` writes a file), so it is exec.
   - A long option can be an abbreviation (GNU `getopt_long`): the rules accept each prefix of the option name. An option letter in a short-option group (`-uo`) counts.

   The auto set:
   - A step runs immediately only when each of its effects is in the auto set.
   - The auto set is the Local cvar `shell.autoEffects` (S4): a list of effect names from read, write, exec, net, outside, protected. Default all six (law `default_auto_is_grantable`): nothing asks but a secret.
   - Secret is never in it: a step that reads or writes a secret always asks (law `never_auto_is_routed`). A user who narrows the auto set is asked about the steps it no longer holds.
   - A name other than the six is a typed error when the value is set.
   - The cvar is an execution gate, so an untrusted project cannot set it.

   The question (every other step, before it runs):
   - It shows the step exactly as it runs: each control or bidi character in a word is escaped (`$'…'`); the prompt keeps each line whole; Enter alone answers no.
   - The worker sends a `shell_approval` frame (`effects`: the names) to the attached clients. The first `answer_shell_approval` (approve or deny) is the answer.
   - When the session stops waiting on a question (a client answered it, its step ended or was cancelled, or every interactive client detached and it went elsewhere), the worker sends `shell_approval_settled` (`requestId`): every client drops it, shown or queued. An answer to a question no longer pending is refused with error code `shell_approval_gone`; the TUI shows one muted note, no error.
   - Who answers (phone gateway, no client, parent chain): G5. No answer is a denial.
   - The shell asks about the steps of a pipeline in order before any of them runs.
   - A denial stops the script at that step. Earlier steps ran and their changes stay. The denied step, the rest of its pipeline and all later steps do not run.
   - The result gives the output and exit status of each step that ran, and how the script ended: finished, exited, or refused at step N (`denied`, `unanswered` or `gateway_refused`).
   - One renderer (`durable/shell.rs` `RefusalText`) writes the text of a refused step, of a cell that did not run and of a document access that did not run: `<what failed>. <next step>.` Next steps:
     - Denied: do not try it again unless the user asks for it.
     - Unanswered: ask the user to attach a client, or to allow its effect in `shell.autoEffects` if that is not secret; or use read-only steps.
     - Gateway refused: ask the user to run it from the eukhe TUI or the dashboard.
   - Shell state (`cd`, `export`) lasts for one call only.

   The `ipython` tool is gated too. A cell is arbitrary Python: it can
   start any process (`subprocess`, `os.system`, the kernel `bash()`).
   - Each cell is one step with the effect `exec`. It runs immediately only when `exec` is in `shell.autoEffects` (the default).
   - Else the host asks with the same `shell_approval` frame: request id `<call>:cell`, step 0, the code as the command (control and bidi characters escaped), effects `["exec"]`. It asks before it starts the kernel, a job or the blocking budget.
   - On a denial, no client, or no answer, the cell does not run; the model gets the refusal text (`ipython did not run (exec): ` and the text above).
   - The `bash()` calls and host requests of a cell the gate let run do not ask again.
9. Remote reads (`ssh://`). An `ssh://` read is new outbound traffic, so
   it is off by default:
   1. The host must be in the setting `ssh.hosts` (list of strings; default empty). The setting is Global: eukhe reads it from the global `settings.json` only; a project cannot set it. The host must match an entry as written (`box`, `me@box`). With an empty list, each `ssh://` read gets the rejection `not_allowed`, and the message names `ssh.hosts`.
   2. The host is letters, digits, `.`, `-`, `_` and `@`, not starting with `-`. Other hosts get the rejection `arguments`. Put ports, users and options in `~/.ssh/config`.
   3. Examples:
      ```
      ssh://box/etc/hosts       # reads /etc/hosts
      ssh://box/~/notes/a.md    # reads notes/a.md under the remote home
      ssh://box/~/../x          # rejection escapes (item 6)
      ssh://box/../x            # rejection escapes (item 6)
      ```
   4. eukhe runs the user's `ssh` program with the user's `~/.ssh/config`:
      ```
      ssh -T -o BatchMode=yes -o ConnectTimeout=<s> -o ClearAllForwardings=yes -- <host> "cat -- '<path>'"
      ```
      eukhe handles no key and no password. With `BatchMode`, a host that asks for a password or passphrase fails at once. The path goes to the remote shell as one single-quoted word (`'` becomes `'\''`), so no character of it is remote shell syntax. The remote login shell must be a POSIX shell.
   5. The call's output cap (S2) keeps the first bytes of the file. eukhe counts the rest; the reply's first line gives the number the cap dropped. The blocking budget (`toolBlockingBudgetMs`) ends the read: `ssh` runs in its own process group, and eukhe kills the group at the deadline. A read that did not fill the cap by the deadline gets the rejection `timeout`. A read that filled the cap gives its bytes, and the first line tells that the cap dropped that number of bytes or more.
   6. The read must run in a tool call. A kernel `read()` outside a tool call has no output cap, so it gets the rejection `arguments`.
   7. Typed rejections: `host` (unknown host, no connection, host key unknown or changed), `auth` (the host refused each key), `not_found`, `is_directory`, `permission_denied`, `binary` (not UTF-8 text, or a NUL byte), `timeout`, `io` (no `ssh` on `PATH`, or another failure).
   8. The read is of one whole file, as text: no `[path#TAG]` header, no selector, lines are not edit anchors.

Model: `bend/tools.bend`. Laws: `laws/tools.bend` (S7). Proofs:
`proof/tools/`. Every input is free: any tools that join and
quit, any schemas, any paths, any scripts, any auto set, any answers of
the user.

| Law | Says |
| --- | --- |
| `roster_fixed` | no event changes the roster; joiners go behind `dyn` (S7.1, S7.2) |
| `roster_sent_fixed` | every request sends the starting roster (S7.1) |
| `dyn_reaches_joined` | joined tool reachable via `dyn` (S7.2) |
| `dyn_drops_quit` | quit tool unreachable via `dyn` (S7.2) |
| `schema_has_intent` | every sent schema has `i` (S7.3) |
| `schema_versioned` | every sent schema has version ≥ 1 (S7.3) |
| `schema_keeps_params` | every declared parameter kept (S7.3) |
| `schema_build_idempotent` | rebuild changes nothing (S7.3) |
| `path_rejects_escape` | above root: rejected, never clamped (S7.6) |
| `path_resolves_inside` | under root: resolves (S7.6) |
| `gate_prefix` | steps that ran = first steps of the script, in order (S7.8) |
| `gate_needs_yes` | gated steps run ≤ steps approved (S7.8) |
| `gate_deny_stops` | denial: earlier steps ran; denied and later steps did not (S7.8) |
| `gate_finish_runs_all` | finished script ran every step (S7.8) |

Code: `eukhe-durable/src/harness/registry.rs` (`Registry::fix_roster`, `RosterFixed`, `RosterChange`, `install`/`uninstall` checks), `harness/harness/conversation.rs` `Conversation::configure`, `harness/generation/round.rs` (`add_tools`), `eukhe-core/src/durable/registry.rs` `create_eukhe_registry` (builds schemas, then fixes roster), `durable/tool_contract.rs` (`parameters`, `build`), `durable/tool_surface/mod.rs` (`ToolSurface`, `dyn`, `report_issue`), `kernel/manager/mod.rs` `mcp_tool_call` + `mcp_call` of the kernel MCP lane (`eukhe-runtime/src/rlm/repl.py`), `eukhe-docs/src/url.rs` (`walk`: sole URL path walker, under `Url::names`, `Url::remote`), `eukhe-core/src/durable/documents/ssh.rs` (`SshRead`: `ssh.hosts` check, `ssh` args, bounded read, typed errors), `eukhe-core/src/durable/shell.rs` (`bash` + approval), crate `eukhe-shell` (in-process shell, `effect.rs`, gate).

Ties:
- `durable::tool_surface::bridge::the_rust_tool_surface_equals_the_bend_model` vs `bridge/bridge_tools.bend` (`run`, `step`, `dyn_call`, `build`): real registry with fixed roster, `ToolSurface`, `tool_contract::build`; tools join (registry also asked to install) and quit (registry also asked to drop roster); requests resolved as the Harness does; schemas built twice.
- `Url::names` and `Url::remote` walk a path with model `resolve`, run as the compiled core (entry `bend/ffi_tools.bend`, request laws `tools_ffi_*`; a name crosses as its segment's index).
- `bridge/bridge_shell.bend`: `eukhe-shell` gate (`run::tests::the_gate_runs_as_its_model`) vs model `join`, `exec` (G2).

Tests: `harness::tests::registry::a_fixed_roster_rejects_every_change_of_the_tools_the_model_sees`; `durable::tool_surface::tests` (two turns, same roster each request; late tool listed and run via `dyn`; `report_issue` row stored; install, `configure` rejected); daemon `dyn_tool_e2e` (stdio MCP tool listed and called via `dyn`; one tool loadout in transcript); `url::tests::an_ssh_url_*` (host, path rules); `durable::documents::ssh::tests` (fake `ssh` records args, plays hosts; shell-syntax path reads that file, runs nothing; each failure typed; cap counts dropped bytes; budget kills `ssh`).

Not modelled (tests tie them): wire form of the version annotation, MCP list and call via kernel, report row, remote side of `ssh://`.

### G1. Path policy

One path policy (`eukhe_types::path_policy::PathPolicy`) judges each path
an agent tool reads or writes. The `bash` tool (S7 item 8) and the
document tools (`read`, `write`, `edit`, `grep`, `glob`, the kernel `fs.*`
requests) share it, so they cannot judge a path differently.

1. The real path. The policy judges the real path, not the written path.
   `resolve` follows each symlink on the existing part of the path,
   dangling ones too (a write through it creates the target). `.` does not
   move. `..` goes up from the real directory, not the written name. `..`
   of `/` is `/`. The part that does not exist stays as written. Thus a
   symlink gets the class of its target. After 40 symlinks (`MAX_LINKS`,
   as Linux) the path loops: resolution stops following, and the policy
   does not trust the rest of the path.
2. The classes. Each real path has one class; the first that applies wins:
   1. Secret: the path is a secret entry, or under one.
   2. Protected: a protected rule covers the path, or the path is an ancestor of a protected or secret entry (moving or removing the ancestor moves or removes the entry).
   3. Inside: the path is under a workspace root.
   4. Outside: all other paths.

   A path whose symlinks loop is never Inside: it is Outside, or Protected or Secret when one applies.
3. The protected set comes from the settings loaders; there is no separate
   list (`durable::path_policy::policy`):
   - the agent dir and each entry directly in it (`settings.json`, `config.cfg`, `subagent.cfg`, `models.json`, `auth.json`, `binds.cfg`): a `Dir` rule;
   - the profile dir (`agents/<agent>.cfg`): a `Tree` rule;
   - the session's project config dir (`<cwd>/.eukhe`): a `Tree` rule; each `.eukhe` directory below the workspace root: a `Named` rule;
   - each settings file the session loads and rereads (`EukheSettings::watched`): a `Tree` rule;
   - each `.git` directory below the workspace root: a `Named` rule (its config and hooks name programs git runs);
   - each directory on `PATH`: a `Dir` rule (a file in it replaces a command).

   A `Named` rule looks at the part of the path below its workspace root
   (the whole path when no root holds it). The policy makes each entry real
   when it starts.
4. The secret set: `auth.json` in the agent dir, the Prime CLI config, the
   credential stores of other programs in the home dir (`.ssh`, `.aws`,
   `.azure`, `.config/gcloud`, `.config/gh`, `.docker/config.json`,
   `.kube`, `.gnupg`, `.password-store`, `.local/share/keyrings`,
   `.netrc`, `.git-credentials`, `.npmrc`, `.pypirc`,
   `.cargo/credentials`, `.cargo/credentials.toml`), and the files named
   by `AWS_SHARED_CREDENTIALS_FILE`, `AWS_CONFIG_FILE` and
   `CLOUDSDK_CONFIG`.
5. Effects of an access:

   | Access | Effects |
   | --- | --- |
   | read or list | read; of a Secret path, read and secret |
   | search (`grep` of a directory) of a path that is or holds a secret | read and secret |
   | write Inside | write |
   | write Outside | write and outside |
   | write Protected | write and protected |
   | write Secret | write and secret |
6. The gate of the document tools (`DocumentsGate`). A document tool
   resolves each path once and gives that resolution (`RealPath`: the real
   path, and whether its symlinks looped) to the gate before the access.
   The access then occurs on that real path. The gate judges the
   resolution as given and does not resolve again: a second resolution can
   lose a loop. An access runs without a question only when the auto set
   (`shell.autoEffects`, S7 item 8) holds each of its effects; secret is
   never in it. Thus:
   - a write runs without a question when the auto set holds its effects, and never to a secret;
   - a read of a secret always asks;
   - each other access asks when the auto set does not hold all its effects.

   The question goes through the approval sink of a `bash` step: the
   `shell_approval` frame, with the verb and the real path as the command
   (`write /path`), and the effects.
   - Approve: the access runs.
   - Deny, no answer, or refused by the gateway rule (G5): the access does not run; the model gets the refusal text (S7 item 8), opened by the access's effects (`(write+outside) it needs the user's approval, …`).
   - No client can answer (no approval sink): the gate does not ask; each access that must ask does not run, and the model gets the unanswered refusal text, opened the same way.
7. A write occurs on the real path. The writer locks the real path, then
   resolves the path again. If the real path changed (a symlink was made
   or moved), the write stops and writes nothing. A replaced file keeps
   its mode. A created file gets the default mode, with no execute bit.

Model: `bend/path_policy.bend` (alias `Pp`: `real` with `max_links`
links of fuel, `class`, `holds`, `effs`, `runs`, `asks`, the store
`run` and `guarded`). Laws: `laws/path_policy.bend`.
Proofs: `proof/path_policy/`. Every input is free: any
symlinks (loops too), any policy, any paths, any auto set, any answers.

| Law | Says |
| --- | --- |
| `path_real_has_no_link` | no loop: no prefix of the real path is a symlink (G1.1) |
| `path_secret_wins` | real path under a secret entry: Secret (G1.2) |
| `path_inside_is_safe` | Inside only if: no loop, no secret covers it, no rule protects it, no ancestor of an entry, a root holds it (G1.2) |
| `path_ancestor_guarded` | ancestor of a protected or secret entry: Protected or Secret (G1.2) |
| `gate_write_auto_never_secret` | write without a yes: never to a secret (G1.6) |
| `gate_secret_read_needs_yes` | secret read: only on a yes (G1.6) |
| `gate_yes_runs` | a yes runs each access (G1.6) |
| `gate_inside_write_runs` | write in auto set: Inside write runs unasked (G1.6) |
| `secrets_need_yes` | no agent write sequence without a yes changes a secret (G1.6, G1.7) |

Code: `eukhe-types/src/path_policy.rs` (`resolve`, `RealPath`, `PathPolicy`, `PathRule`, `MAX_LINKS`), `eukhe-shell/src/paths.rs` (`judge`: class and holds-a-secret of a resolved path, run as compiled model `judge`, entry `bend/ffi_path_policy.bend`, request laws `path_policy_ffi_*`; each path component crosses as an id), `eukhe-core/src/durable/path_policy.rs` (`policy`, `session_policy`, `effects`, `DocumentsGate`), `eukhe-docs/src/gate.rs` (`AccessGate`, `Access`), `eukhe-docs/src/write.rs` (`write_file`, `LockedWriter`), `eukhe-shell/src/run.rs` (step path effects: one `judge_path` per path).

Tests: `durable::path_policy::tests::every_loader_file_is_guarded_and_a_project_file_is_inside`, `durable::path_policy::tests::a_write_whose_links_looped_asks_even_when_its_real_path_is_inside`, `path_policy::tests` (`eukhe-types`).

Not modelled: filesystem change between gate and lock (the writer checks it), file modes.

### G2. Shell classification

A step's effects: every effect of every part (S7 item 8); auto set rules: S7 item 8. By default only a step with outside, protected or secret asks. A step has secret only when a part names a path that is or holds a secret (an operand, an option value, a redirection target, the working directory of a command that reads it because it names no path).

Model: `bend/tools.bend` part 4 (`Step{id, effs}`, `grantable`,
`within`, `join`, `Part{own, secret}`, `part.effs`, `parts.effs`,
`parts.secret`, `exec`). Laws: `laws/tools.bend`. Proofs: `proof/tools/`.

| Law | Says |
| --- | --- |
| `step_holds_every_part` | step has every effect of every part |
| `secret_needs_a_secret_path` | secret only if a part names a path that is or holds a secret |
| `secret_path_gives_secret` | such a part gives its step secret |
| `auto_needs_every_effect` | one effect outside the auto set, or ungrantable: asks |
| `auto_never_sensitive` | secret: always asks, any auto set |
| `composed_needs_every_part` | unasked only if every effect of every part is within the auto set |
| `auto_runs_within` | within the auto set: runs, uses no answer |
| `held_needs_a_yes` | not within: runs only on a yes; else the script stops there |

Code: `eukhe-types/src/shell.rs` (`ShellEffect`, `ShellEffects`, `AutoSet`), `eukhe-shell/src/effect.rs` (`classify`, `GIT_UNTRUSTED_REPO_ARGS`, `reads_cwd`), `run.rs` (`Shell::effects`; parts of an out-of-grammar script from `parse::parts`), `shown.rs` (`quote`, `visible`), `eukhe-tui/src/confirm.rs` (`ConfirmPanel::approval`).

Tie: `run::tests::the_gate_runs_as_its_model` vs `bridge/bridge_shell.bend`: steps from parts whose effects and secret paths come from a temp workspace's path classes (secret reads, writes outside and to a protected tree, redirections, out-of-grammar scripts), run in the workspace or the dir above it, which holds a secret (there `echo`, `date`: no secret part; `ls`, `grep -r`: one for the working dir); random auto sets (outside, protected, secret included) and answers; compares steps run, their effects, the end. Every command and redirection kind runs in each dir.

Tests: `every_effect_of_a_step_must_be_allowed`, `only_a_step_that_reads_its_working_directory_reads_a_secret_in_it`, `effect::tests::a_command_reads_the_working_directory_only_when_it_names_no_path`, `effect::tests::a_git_step_that_can_run_a_repository_program_is_exec`, `a_git_step_that_is_not_exec_runs_with_the_untrusted_repository_arguments`, `shown::tests::a_hidden_character_is_escaped_and_bash_reads_the_word_back`, `confirm::tests::an_approval_answers_no_on_enter_and_keeps_every_line`.

Not modelled: which paths a command reads or writes (every word counts; working dir only via `reads_cwd`); what an approved exec step does.

### G4. Every runner of code goes through the gate

A tool that runs code declares a `Runner` in its registration (`extra`):
its caps (each effect its code can have) and how the gate covers it
(`EachStep`: `bash`; `EachCall`: `ipython`). A tool with no `Runner` runs
no code of its own. A `Runner` is always gated: Rust cannot write an
ungated one.

Model: `bend/runners.bend` (`registry`, the tools a default session
installs, in install order; `cell`, the gate of one call). Laws:
`laws/runners.bend`. Proofs: `proof/runners/`.

| Law | Says |
| --- | --- |
| `gate_covers_every_runner` | every registry tool whose caps hold `exec` is gated |
| `ipython_gated_each_call` | `ipython`: caps `exec`, gate covers each call |
| `cell_runs_only_within_or_approved` | gated call runs only if caps within the auto set or approved |
| `cell_within_runs_unasked` | caps within: runs unasked |
| `cell_approved_runs` | outside, approved: runs |
| `cell_no_yes_stops` | outside, no approval (denial, no answer, no client): does not run |
| `cell_exec_asks` | code that can run a program is never within an auto set without `exec` |

Code: `eukhe-core/src/durable/runner.rs` (`Runner`, `Gate`), `durable/rlm/tool.rs` (`ipython` gate), `durable/shell.rs` (`bash` runner).

Tie: `durable::runner::tests` vs `bridge/bridge_runners.bend`: `the_registry_is_its_model` (every tool of an opened session: name, caps, gate vs `registry`); `the_ipython_gate_runs_as_its_model` (one real `ipython` call per auto set and asker: no client, no answer, deny, approve; asked? end? vs `cell`).

Test: `a_cell_runs_only_within_the_auto_set_or_approved`.

Not modelled: dynamic tools behind `dyn` (MCP tools, kernel `remote/<name>` functions).

### G5. A child's question reaches its root's user; the phone never waits

A subagent session (an RLM child) runs in its own worker with no client of
its own, so its gated steps (S7 item 8: `bash` steps, `ipython` cells)
must ask the user of its root session.
- A session whose question no client answers (none attached, or all detach without an answer) hands it to its parent session: daemon command `relay_shell_approval` (the parent's persisted session id, the request, and `agent`, the name of the asking subagent). The supervisor routes it to the parent's worker like a turn-long wait.
- The parent asks its own clients with a `shell_approval` frame that carries `agent`, or hands the question on to its own parent.
- The first session up the chain whose clients answer gives the answer (`{"answer": "approve" | "deny" | "unanswered" | "gateway_refused"}`). When the root has no client that answers, the answer is `unanswered` (a denial, with the usual message to the model).
- The TUI prompt names the subagent (`Subagent <name> asks: allow shell step N (<effects>)?`), with the name's characters that a terminal hides or moves escaped. A frame without `agent` is the session's own question.

A client tells its kind when it attaches (`clientKind`: `interactive`, the
default, or `gateway`). The phone gateway attaches as `gateway`: it shows
no question, so a session never waits for its answer.
- A session whose attached clients are all gateways asks no one and answers at once by the gateway rule: a step with protected (a write of eukhe's own config or credentials, a `.git` or `.eukhe` dir, a `PATH` dir) or secret is refused (`gateway_refused`); every other step runs.
- The bash result, the `ipython` result and the document tools' error tell the model that the session runs only from the phone gateway and that the user must run the step from the TUI or the dashboard.
- A subagent's question that reaches such a session gets the same answer.
- When a TUI or the dashboard is attached beside the gateway, that client gets the question. If all of them detach without an answer while the gateway stays, the gateway rule answers.

The auto set comes first (`gate`; default: S7 item 8): a step within it runs unasked. Outside, protected and secret take the route above: a TUI or the dashboard is asked; from the phone alone, a write outside the workspace runs by the gateway rule, a protected write or a secret is refused.

Model: `bend/approvals.bend` (`route`, a chain of sessions from the one
that asks up to its root: no client, clients that leave, clients that
answer, the gateway alone, clients that leave while the gateway stays;
`fate`, what becomes of a step with given effects; `default_auto`;
`gate`, the auto set before the route). Laws:
`laws/approvals.bend`, `laws/tools.bend`. Proofs: `proof/approvals/`.

| Law | Says |
| --- | --- |
| `child_answered_by_root` | no session below the root answers: the root's clients get the question; their answer is the verdict |
| `nearest_answer_wins` | first answering session up the chain decides, whatever is above |
| `unanswered_only_when_quiet` | unanswered (a denial) only if no session in the chain answers |
| `quiet_is_unanswered` | then unanswered; no session invents an answer |
| `gateway_never_waits` | gateway-only session: no frame to any client, nothing up the chain, gateway rule answers at once |
| `gateway_refuses_protected` | gateway rule refuses a protected write |
| `gateway_refuses_secret` | gateway rule refuses a secret read or write |
| `gateway_runs_the_rest` | gateway rule runs every other step unasked |
| `left_to_the_gateway` | interactive clients leave it unanswered, gateway stays: gateway rule, not up the chain |
| `gateway_rules_a_subagent` | subagent question reaching a gateway-only session: fares as that session's own step |
| `default_auto_is_grantable` | no user setting: auto set = every effect but secret |
| `never_auto_is_routed` | secret never runs unasked via the auto set; the question takes its route |
| `never_auto_asks_the_client` | answering client (TUI, dashboard): it is asked; its answer decides |
| `outside_runs_only_by_the_gateway` | phone only, auto set without outside: an outside write, not protected, no secret, runs, only by the gateway rule |
| `guarded_refused_from_the_phone` | phone only: secret refused at once, any auto set |

Code: `eukhe-daemon/src/shell_approval.rs` (`ShellApprovals::ask`, `relay`), `worker.rs` (relay over the supervisor link), `worker/connection.rs` (client kind at attach), `supervisor/routing.rs` (relay budget), `eukhe-tui/src/session_ui/settings.rs` (prompt), `eukhe-gateway/src/link.rs` (attaches as `gateway`), `eukhe-core/src/settings/cvar/table.rs` (`SHELL_AUTO_EFFECTS`, default auto set).

Ties:
- `shell_approval::bridge::the_approval_route_is_its_model` vs `bridge/bridge_approvals.bend`: every chain of up to 3 sessions with a write, a program run, a protected write, a secret read, plus generated longer ones, on real `ShellApprovals` relaying through each parent's real handler; compares which sessions showed the question, whether each frame names the subagent, the end.
- `durable::shell::tests::the_default_auto_set_is_its_model`: real default auto set vs the same model: effects held; whether the gate runs each of the 127 steps of 1 to 7 effects unasked.

Tests:
- `with_no_auto_set_a_write_outside_the_workspace_runs_unasked`: no client; write, program run and outside write all run.
- `rlm_child_approval_e2e::a_subagent_step_runs_when_the_root_client_approves`: real supervisor; root with attached client; subagent `bash` write under auto set `read`.
- `shell_approval_e2e::a_phone_only_session_runs_steps_unasked_and_refuses_a_protected_write`: real supervisor, client attached as `gateway`, auto set `read`; write and program run run unasked by the gateway rule; `.eukhe/settings.json` write refused at once with the gateway message.

Not modelled: supervisor routing of the command (a parent whose worker is not resident is not asked; then unanswered); a client attaching while a question waits above it. The dashboard shows a subagent's question without its name.

### S8. The documents tools

The documents tools are `read`, `edit`, `grep`, `glob` and the kernel
functions `read()`, `write()`, `edit()`, `grep()`, `glob()` (crate
`eukhe-docs`). They share one edit store per session.

1. An `edit` of many files is all or nothing for conflicts. The writer
   locks every path of the call, in one order, then checks each file: its
   bytes must be the bytes the edit was applied to, and an `MV`
   destination must not exist. If one check fails, no file is written.
   Then it writes the files in order and stops at the first failure. The
   reply names the files that landed (with new tags) and those that did
   not: "Applied to a; NOT applied to b, c". It never says nothing was
   written when a file landed. A rename that landed but whose directory
   sync failed, and a move whose source stays, are landed writes with a
   warning.
2. A retry of a start or end insert with the old tag, after the insert
   landed, does not insert again: the result says the edit is already in
   the file.
3. `write()` replaces an existing file only when its bytes on disk are a
   version this session saw (a read, a grep, or its own write or edit).
   Else it writes nothing and tells the model to read the file first. A
   new file is created. A replaced file keeps its BOM, line endings and
   mode; a warning tells when the content had other line endings, or when
   the old file was not UTF-8.
4. `MV` never replaces a file. The destination gets the bytes through a
   hard link, which fails on a name that exists.
5. A temporary file is `.eukhe-tmp-<hash of the name>-<pid>-<n>`, so a
   long name still fits. Its writer locks it. Each write of a target
   removes that target's temporary files that no writer locks (a crash
   left them). `grep` and `glob` do not show these names.
6. A line ends at `\n`. A `\r` before `\n` is part of that line's CRLF
   ending; a lone `\r` is text. `read`, `grep` and `edit` share this line
   model. An edit keeps every byte outside its lines. A new or changed
   line gets the ending of the line before it (at file start: the file's
   first ending, else LF).
7. The tag of a grep result is the hash of the bytes grep searched, not of
   a second read of the file.
8. A line is seen only when its row reached the model, after the output
   bound cut the middle of a long result. An edit anchor on an unseen line
   is rejected; the rejection shows the line and marks it seen, so the
   same edit applies on a retry. After an edit lands, the lines seen
   before and the lines the edit wrote stay seen.
9. `grep` and `glob` report each file they skip or cut, with the reason
   and the count: binary, unreadable, searched only in part, excluded
   directories, symlinks, walk errors, the match caps. A continuation
   (`skip=N`, a line range) gives the next results.
10. One size limit (`MAX_SNAPSHOT_FILE_BYTES`, 4 MiB) applies everywhere.
    A larger file has no tag; the message tells the model to read it in
    ranges and change it with `write()` or `bash`. A non-UTF-8 file gets a
    message with its path and encoding.

Models: `bend/doc_commit.bend`, `bend/doc_seen.bend`,
`bend/doc_lines.bend`, `bend/doc_rows.bend`, `bend/doc_tags.bend`, `bend/doc_search.bend`. Laws:
`laws/doc_seen.bend`, `laws/doc_search.bend`, `laws/doc_commit.bend`, `laws/doc_tags.bend`, `laws/doc_lines.bend`, `laws/doc_rows.bend`. Proofs: `proof/doc_seen/`, `proof/doc_search/`, `proof/doc_commit/`, `proof/doc_tags/`, `proof/doc_lines/` and `proof/doc_rows/`.

Lines run as the compiled Bend core: Rust scans a file into its projection (`text.rs` `Projection`: the BOM flag, each line's length and own ending) and the core decides on it: the separators of an edit, the carry of a loaded file and what a whole-file write keeps (`bend/ffi_doc_lines.bend`), whether a read goes on and what it shows (`bend/ffi_doc_rows.bend`: lines counted, spans with context and gap markers, notices, tag).

| Law | Says |
| --- | --- |
| `edit_reports_what_landed` | reply says applied iff new content is on disk (S8.1) |
| `edit_all_or_nothing_on_conflict` | one file changed since staging: no file lands (S8.1) |
| `edit_lands_every_file` | no change, no failed write: every file lands (S8.1) |
| `write_never_loses_unseen` | over an unseen version: refused, no change (S8.3) |
| `write_writes_seen` | over no file or a seen version: written (S8.3) |
| `move_never_overwrites` | to an existing name: refused, no change (S8.4) |
| `move_moves` | to a free name: content moves (S8.4) |
| `temp_sweep_never_held` | never removes a temp file a live writer locks (S8.5) |
| `temp_sweep_only_own` | removes only its target's temp files (S8.5) |
| `temp_sweep_removes_free` | removes every unlocked temp file of its target (S8.5) |
| `load_persist_roundtrip` | load + write, no edit: same bytes (S8.6) |
| `edit_keeps_untouched_bytes` | every byte outside the edited lines kept (S8.6) |
| `edit_writes_new_lines` | an edit keeps the lines before, then exactly the new lines, then the lines after (S8.6) |
| `grep_line_is_read_line` | `grep` and `read`: same text at the same line number (S8.6) |
| `persist_weaves_carry` | edited file written line by line: each line but the last followed by its own ending, else the separator written before it (S8.6) |
| `persist_plan_refines` | separator plan over runs of lines gives, line for line, that rule's separators (S8.6) |
| `lines_entry_refines` | the plan's compiled entry reads every request back, answers the model's separators (S8.6) |
| `lines_carry_is_first` | the carry decided from a file's projection is the first ending persist starts from (S8.6) |
| `lines_write_keeps` | a whole-file write keeps the file's BOM and first ending, warns iff both texts have endings and they differ (S8.6) |
| `lines_entry_answers` | the lines entry answers every request spelled from the wire primitives with the spelled decision (S8.6) |
| `lines_entry_exact` | any input the lines entry does not refuse is the spelling of a request (S8.6) |
| `rows_lines_are_read_rows` | the lines a read numbers are, in order and length, the model's read rows (S8.6) |
| `rows_raw_lines_are_pieces` | a raw read counts every piece of the LF text (S8.6) |
| `rows_gate_refuses` | a read that is not raw refuses a non-UTF-8 file, then a binary one (S8.10) |
| `rows_view_shows` | a read shows the lines it counts, the spans with their context and gap markers, the notices and the tag of the read rule (S8.6, S8.10) |
| `rows_entry_answers` | the read entry answers every request spelled from the wire primitives with the spelled decision (S8.6) |
| `rows_entry_exact` | any input the read entry does not refuse is the spelling of a request (S8.6) |
| `tag_names_shown_text` | tag names the text its rows come from (S8.7) |
| `edit_only_seen_lines` | applies only if every anchor is seen (S8.8) |
| `edit_seen_applies` | all anchors seen: applies (S8.8) |
| `reveal_then_retry` | rejected edit with ≤ 40 anchors applies on a straight retry iff every unseen anchor is a line of ≤ 512 characters (S8.8) |
| `edit_marks_whole_reveal` | unseen anchors become seen iff the rejection showed them all whole: ≤ 40, each a line of ≤ 512 characters (S8.8) |
| `reject_names_unseen` | rejection names exactly the unseen anchors, in order (S8.8) |
| `reject_shows_lines` | rejection shows, of its first 40 unseen anchors, each that is a file line, cut to 512 characters when longer (S8.8) |
| `reject_whole_exact` | rejection says it showed its anchors whole iff it did (S8.8) |
| `reveal_bounds` | reveal cap: 40 anchors, 512 characters (S8.8) |
| `seen_entry_refines` | the guard's compiled entry reads every request back, answers the model's verdict (S8.8) |
| `grep_accounts_every_file` | each walked entry in exactly one class; classes sum to the walk (S8.9) |
| `grep_notes_every_gap` | skipped, cut or unsearched class has a notice iff not empty (S8.9) |
| `grep_notes_every_cut` | shown file with cut matches has its own notice (S8.9) |
| `continuation_progresses` | continuation page not empty (S8.9) |
| `continuation_contiguous` | continuation = next part of the list: none left out, none twice (S8.9) |
| `continuation_disjoint` | page and continuation share no item (S8.9) |
| `search_scope_answers` | scope: several files iff more than one root or a directory root; 20 matches a file and the skip asked, else 200 and no skip; page = match limit + 1 files, else 20 (S8.9) |
| `grep_walk_spec`, `grep_keeps_spec`, `fetch_reaches` | each walked file's class, cut, kept matches and fetch are the spec's (S8.9) |
| `page_is_window`, `next_is_more`, `past_is_beyond`, `grep_scope_pages`, `limit_round_robin`, `limit_cuts` | page, continuation, past-the-end notice, match limit: exactly the spec's (S8.9) |
| `search_walk_runs`, `search_*_answers`, `search_*_refuses`, `search_shut_refuses` | grep's compiled entry and walk stepper answer each request with the rule's decision; malformed input gets the error form (S8.9) |

Code: `eukhe-docs/src/write.rs` (`LockedWriter::write_all`, `publish`, `write_file`, sweep), `hashline/mod.rs` (`apply_hashline`, `commit`), `hashline/patcher.rs`, `hashline/seen.rs` (seen guard), `hashline/apply.rs` (line origins, `persist`), `text.rs` (scan, carry, write decision), `read/mod.rs`, `read/view.rs` (read gate and view), `grep/`, `glob.rs`, `store.rs` (`saw_bytes`), `eukhe-core/src/durable/documents/tool.rs` (`bounded`), `requests.rs` (`Cut`, `Done::mark_seen`).

Ties: `write::bridge` (multi-file edit with injected faults and conflicts; write tool vs writes by another program; move; sweep with live locks), `text::tests::the_scan_is_the_projection` (the scan is the projection the laws state), `grep::bridge` (read and grep show the same rows on random bytes with `\r`, `\n`, `\r\n`, BOM; file changes between search and record), `grep::decide::tests` (grep's decisions come from the compiled core), `glob::bridge` (generated trees; every continuation followed once), `durable::documents::bridge` (long read cut by the output bound; edits at anchors in and around the cut).

Not modelled: notice text bytes; line model of a stale edit's rebase (maps lines through a line diff).
