# security (spec): confinement and isolation

Status: design; the owner decisions of §13 are applied. Nothing below is
built; no law named here exists.
Ids `C9`, `C11` are rewrites of `spec/security/SPEC.md`; `C15..C25` are
new and provisional. Research, sources and measurements:
`spec/security/CONFINEMENT-RESEARCH.md` (cited as R§n).

Every program an agent or a check runs is held by an operating-system
mechanism to its grants: the files it reads and writes, the hosts and
sockets it reaches, the processes it signals. Eukhe's own state is out of
reach of those programs. A decision core in Bend computes each program's
profile from its grants; Rust renders the profile into the mechanism of the
platform (Seatbelt on macOS; Landlock, seccomp and, where available, user
namespaces on Linux) and starts the program under it. A program the platform
cannot hold to its grants runs only under an explicit unconfined grant,
counted and reported. The label's "unconfined" qualifier is absent exactly
when every program of the run ran confined under a listed mechanism with no
disclosed, unfixed escape; "not isolated" is a separate qualifier (decisions
1 and 2 read df9's "confinement in force" that way, §13).

Philosophy rows covered: scope statement, ds10, df9, sr18, sr41, sr73,
sr91, sr98, sr119, sr136, sr161, sr172, sr179; record T11.

## 1. Words

- **program run**: one process image an agent causes to start, with every
  process it forks or execs: an external command of the `bash` tool, a
  Python kernel, an MCP stdio server, a language server, a check's command,
  a law check's proof run, and a model request to a provider that declares
  provider-side execution (sr73). Eukhe's own processes (supervisor,
  workers, tiny workers) are not program runs; they are the trusted base
  (df6). They create copies and snapshots only with `clonefile`, `FICLONE`
  or a plain copy, and run no external tool (`git` included) on a tree an
  agent's program can write except through the launcher under a profile
  that writes only that tree and reaches no state, so no deferred
  execution file runs with the trusted base's access. A program run is live
  from its start until its last process exits. On Linux the launcher stays
  the program's parent as a child subreaper (`PR_SET_CHILD_SUBREAPER`), so
  every orphaned descendant is reparented to it; it knows when the last
  one exits and kills every one at a stop. On macOS each run's profile
  allows one per-run marker (`mach-lookup` of `eukhe.run.<id>`, a name no
  service registers), and Eukhe finds the run's processes among the
  user's by asking `sandbox_check` for that marker [INFERENCE: a
  libsystem interface outside the public SDK headers; the probe suite
  confirms it before phase 1].
- **grant** (program grants, a subset of the capability vocabulary of
  `SPEC.md` §1):
  - `Read{tree}`, `Write{tree}`: a real path tree. A readable file is
    executable: an interpreter or the dynamic loader runs any file it can
    read, so no separate execute grant exists.
  - `Send{host, ceiling}`: TCP to one exact host name through Eukhe's proxy,
    carrying data up to `ceiling`. `SendAny{ceiling}`: every host.
  - `Socket{path}`: connect to one pathname Unix socket.
  - `Serve{Loopback}`: accept connections from the same machine.
    `Serve{Any, ceiling}`: from any host, carrying data up to `ceiling`.
  - `Unconfined`: start the program with no mechanism; counted under tm8.
    A grant to run check code unconfined binds to the judged work state's
    digest (sr112).
- **state**: what df9 isolates, as paths, sockets and processes on the
  machine (table in §4).
- **mark of a program run**: the highest of the agent's context label (its
  argv, environment and stdin carry the context) and the marks of the paths
  its profile reads; an `Unconfined` run has the highest mark (its output
  carries the highest mark). A run's write reach is its write trees, or,
  for an `Unconfined` run, every path the user can write. Every path in a
  run's write reach takes the run's mark from the run's start (C6), so a
  later run that reads it counts it. When a run starts, and whenever a live
  program's mark rises, every live program whose read trees overlap that
  write reach takes the mark if higher, and its own write reach takes the
  raised mark in turn, to a fixed point. A program whose mark rises is held
  to it: the proxy decides its later sends at the raised mark (C22), and
  one whose profile allows a direct send or `AnyBind` with a ceiling below
  it, or holds the cache grant and rises above the default mark, is stopped
  before the run that raised it starts (C21). A live program refuses an
  input above its current mark (C7). Path marks are kept per account and
  machine with the store and read by every run's core, so a mark set in
  one session binds the next; only the principal lowers a path's mark, on
  the principal channel, recorded.
- **profile**: what the mechanism allows one program run: read trees, write
  trees; network (`NoNet`, `Proxy{hosts}`, `AnyNet`); Unix socket paths;
  bind (`NoBind`, `Loopback`, `AnyBind`); signals, tracing, limits and
  scheduling limited to the run's own processes.
- **mechanism**: one of the kinds of sr161 with its version: Seatbelt on a
  macOS build; Landlock at an ABI with a seccomp filter on a kernel
  release; user, mount, network and PID namespaces with a seccomp filter; a
  provider sandbox with an attestation on the trusted base list; a proof
  under a listed closure (df10). The version of the first three includes
  the Eukhe build whose launcher and renderer apply them. **listed**: on
  the release's escape list (§9) with its escape classes.
- **escape list in force** at a position: the release's list plus every
  disclosure ingested on the account before that position; a run records
  those ingested before its start at its start, and one ingested during it
  at ingestion.
- **platform facts**: what the host reports before each program run: OS and
  build or kernel release, Landlock ABI, whether user namespaces can be
  created, whether a Seatbelt profile can be applied (it cannot inside an
  already sandboxed process, R§1.2).
- **outcome** of a program run: `Confined{profile, mechanism}`,
  `Unconfined{cause}` or `Refused{grant needed}`.
- **deferred execution file**: a file that software outside Eukhe runs
  later without asking (`.git/hooks/*`, `.git/config`, shell start-up
  files, `.envrc`; the list ships per release). Writes to those of §8's
  deny set are denied on macOS and in tier N (decision 10); elsewhere
  writing one inside a write grant is within the grant, listed in the
  report (§8), and its later run is the principal's program run, outside
  Eukhe.
- **cache grant**: the shipped write grant on the package cache trees of
  the default tools (§11; decision 5), held only by interactive program
  runs whose mark is at most the contract's default mark; a run above it,
  and every program run of a scheduled, loop or autoresearch run, reads the
  caches only.

## 2. Requirements

|Id|Requirement|Rows|
|---|---|---|
|C9|A program holds its grants. Every program run is started under a listed mechanism with the profile the core computed from the run's grants: it reads and writes a real path (content, directory entries, and mode, owner, times and extended attributes) only when a grant covers it and the path is not state, and every such path except those §5 names as narrowed; beyond its grants it changes only the metadata §5 names as widened, never of a state part or a directory on a path to one; on Landlock tiers without a mount namespace a state part's existence, size, times, mode and extended attributes (`stat`, `access`, `getxattr`) and, through file notifications, its entry names stay readable, never its content (§5, reported); it reaches a host only under a `Send` or `SendAny` grant whose ceiling is at least the run's mark, through Eukhe's proxy wherever the platform can force it (§5), and directly only under `SendAny` with sr54's admission; it accepts connections from other hosts only under `Serve{Any, c}` with `c` at least that mark; it connects to a Unix socket only under a `Socket` grant naming a path on the release's list of agent sockets, services that open no file their caller names (ssh and gpg agents), any other socket (a container engine, the Nix daemon) needing `Unconfined`; it signals, traces, and changes the limits or scheduling of only processes of its own run (on Linux without a PID namespace it can read other processes' `cmdline` and `status`, §4). When the platform cannot enforce a part of the profile, the run is started only under `Unconfined` and counted (tm8, sr113), else refused naming the grant needed.|ds10, df9, sr161, sr54|
|C11|The policy and the state protect themselves. While isolation holds, nothing an agent does and nothing a program it runs does changes the store or any other state part: no effect, message, daemon or CLI command, file write, rename, link, change of mode, owner, times or extended attributes (of a state part or a directory on a path to one), socket connection, signal, or change of an Eukhe process's limits or scheduling. A write to the store's files asks a user whatever the set holds. The project's `.eukhe/` is not state: its keys apply only at a digest the principal accepted (§4).|df9, T11|
|C15|Isolation is a fact per position. Every program run shares the user's OS identity; it breaks isolation only when it is not confined, or confined yet able to reach Eukhe's state (sr179 as reworded, decision 1). A run is isolated up to the first of: an `Unconfined` program run; a confined run on a platform where signals or sockets of Eukhe are reachable (§5, tier L3); a confined run with a direct `AnyNet`, on any platform (it reaches every loopback service and every address of this machine, and some services there act with the user's access); a confined run under a mechanism version with a disclosed, unfixed instance on the escape list in force; a disclosure recorded while a program run under a version it leaves unfixed is live (at the disclosure's position); a program run started while a state file has more than one link (§4); a call of an in-process host tool that executes agent-supplied content or declares nothing (C23). Before it, the harness delivers on the principal channel, stored out of agents' reach, the head digest and a notice naming the position (sr179); a loss placed by a disclosure cannot precede its ingestion, so that notice is delivered at ingestion, before the next decided effect, and the report says the notice followed the loss. From the loss on the run is not isolated, its facts are unprotected (sr91), and a software delegate's decision is judged from that notice (sr151).|sr179, sr91, sr151, sr98, df8|
|C16|Platforms without a mechanism. A platform that cannot enforce the profile reports so before the run; its program runs need `Unconfined`. The shipped interactive default holds `Unconfined` (sr51, sr73), and every agent of an interactive run holds it exactly when the root does (decision 9); no shipped default of a scheduled, loop or autoresearch run holds it (sr113, sr133), and no spawn passes it to an agent of such a run.|sr73, sr113, ds10|
|C17|Report facts (sr18). The record entry of each program run names its outcome, mechanism and version, profile digest, mark, whether it held the cache grant, and the digest of the escape list in force. The report states as witnessed facts: its issue date; the core builds, trusted base list versions and placements in force and when they changed; which mechanism and version each program ran under; for each escape-list instance whose fixed version the host meets, the probe result (C19); which model requests were unconfined; the count and causes of unconfined runs; the count of interactive confined runs whose write trees leave the project scope (the temp dir, the cache trees), each counted as one irreversible effect (tm8, sr51); the program runs that held the cache grant and its trees; the metadata changes a profile allowed as widened (§5); the deferred execution files the run wrote (§8); whether a breach was detected (§8); the escape list's digest and date, with a qualifier when it is older than the stated age; the position isolation was lost, if it was; and, when it relies on confinement, a reference to C25's figures for each mechanism used. Denials observed are reported as measured.|sr18, sr41, tm8|
|C18|Label. The label carries "unconfined" exactly when some program run of the run (check and proof runs included) ended `Unconfined`, or ran while the escape list in force held a disclosed, unfixed instance for its mechanism version (a long-lived program counts from the disclosure on); it carries "not isolated" exactly when C15 places a loss.|df8, sr80, sr119|
|C19|Escape list and disclosures. Each release ships an escape list: per mechanism, its escape classes, each with the date it was listed, and disclosed instances with the version that introduced them, the fixed version on each release branch that has one (a macOS release line, a stable kernel series, a distribution's kernel package) and a probe. An escape class counts only if listed before any disclosure within it. A disclosed instance voids confinement, whether or not its class is listed, on every host at or above its introducing version that is not fixed for it; a host is fixed for it only when its version is at or above its branch's fixed version and the instance's probe passes on that host, run at session start and again when a disclosure is ingested, before the program run, and both facts are reported (decision 7); a host on a branch with no fix is unfixed. An instance the shipped profile blocks (a seccomp rule, a Seatbelt deny) is listed with that rule, and its probe runs against the shipped profile; it voids nothing while the probe passes. An instance with no probe yet leaves every host at or above its introducing version unfixed. A disclosure ingested on the account qualifies the label from that position on in every run live at it and every later run (§1, escape list in force). A disclosure after the report's date is appended as a relayed fact (source, date, content) with the witnessed fact of which mechanism versions the report's program runs used; no label changes.|sr119, df9|
|C20|Checks are confined to their copy. A check's command and a law check's proof run start under a profile that writes only inside the check's copy of the judged work state and sends nothing unless the check holds a send grant. It reads a path in the worker's write reach outside its copy (the write trees of the worker's program runs, the cache trees, and, once a program of the worker ran `Unconfined`, every path the user can write) only as an input reported unprotected (tm4). Judgings that run check code unconfined draw on their own irreversible allowance, a count and a value cap per run and per account, zero by default for non-interactive runs; the report states their effects are uncounted beyond that count (sr112). A recorded stop voids every grant to run check code unconfined: no such program starts after it, a running one is stopped, and the judging is undecided with cause "stopped".|tm4, sr112, sr172, sr136|
|C21|Long-lived programs. A kernel, MCP server or language server keeps the profile it started with. A grant widened later reaches it only at a restart; a revocation that covers an effect its profile allows stops it before the next effect of the subtree is decided (C5). Its mark rises as §1 states; when its profile allows a direct send or `AnyBind` with a ceiling below the raised mark, or it holds the cache grant and the raised mark is above the default mark, it is stopped before the run that raises the mark starts.|C5, C9, C7|
|C22|Network through the core. Every connection a confined program opens through the proxy is an effect submitted to the core: a send to the host at the program's current mark (C7, §1), metered or refused on a billing host (sr54), recorded with author and cause. The proxy resolves each name once and dials the checked address; unless a grant names the address, it refuses IP literals, every address assigned to an interface of this machine (read at each dial), and every address of a private or local network: 0.0.0.0/8, 127.0.0.0/8, 10.0.0.0/8, 100.64.0.0/10, 169.254.0.0/16, 172.16.0.0/12, 192.168.0.0/16, `::`, `::1`, fe80::/10, fc00::/7, and IPv4-mapped (`::ffff:0:0/96`) or NAT64 (`64:ff9b::/96`) addresses judged as their IPv4 address.|C7, sr54|
|C23|In-process placement. Every host tool or callback of the in-process placement declares whether it executes agent-supplied content; one that does, or that declares nothing, makes the run not isolated (sr98). A program it starts through Eukhe's launcher is confined like any other.|sr98, sr19|
|C24|Non-interactive runs. Scheduled, loop and autoresearch runs write only to a harness-owned copy of the scope, handed over at acceptance: their temp dir lies inside that copy and they hold no cache grant, so a tool that must write a cache uses one inside the copy, set through the tool's variable on the release's cache list. They run no unconfined program, and their report's first line says so (sr113); a model request to a provider that declares provider-side execution outside a listed mechanism is an unconfined program run and refused for them, the report's first line naming the grant needed. For interactive runs the report's first line states that billed cost of unconfined program runs outside the core's rulings is unbounded.|sr73, sr113, sr51|
|C25|Measured. Per listed mechanism and release, Eukhe publishes, with method, sample and date: the escape rate red-teaming finds with the strongest available model, as a lower bound with recall on seeded known escapes; the time from disclosure to a fixed release; per law-check closure, the rate of proofs accepted for a term other than the delivered one; the side-channel rate (side channels are not on the escape list, sr18); the denial rate and the start-up and run-time cost of confinement on recorded sessions.|sr41, sr96, sr136|

## 3. What exists in eukhe

- No mechanism. A search of `crates/`, `bend/` and `laws/` for landlock,
  seatbelt, sandbox-exec, bwrap and seccomp finds nothing.
- Program runs start with plain `tokio::process::Command` and a new process
  group: the `bash` tool's external commands
  (`crates/eukhe-shell/src/run.rs:901-913`), durable exec
  (`crates/eukhe-durable/src/env/native/exec.rs:129,518`), the Python kernel
  (`crates/eukhe-core/src/kernel/manager/startup.rs:324,380-397`), gate and
  check commands (`crates/eukhe-core/src/autonomous/gates.rs:412`); checks
  run "in the session cwd" (`durable/acceptance/evidence.rs:295`), not on a
  copy.
- The path policy (`crates/eukhe-core/src/durable/path_policy.rs:84-133`,
  `bend/path_policy.bend`) classes paths Secret, Protected, Inside, Outside
  on their real location; it is the base of the profile. The OS temp dir is
  a write root (`:121-131`) and holds the daemon socket
  (`$TMPDIR/eukhe-<uid>/daemon.sock`, `crates/eukhe-client/src/paths.rs:15-16`),
  so a write grant on the temp dir covers the socket today.
- `unsafe` is forbidden outside `crates/eukhe-bend/src/ffi.rs` (AGENTS.md),
  so no `pre_exec` hook can apply a policy after fork; a re-executed Eukhe
  binary applies it before `exec`, as `request_new_session` does for
  `setsid` (`crates/eukhe-types/src/platform/process.rs:55-60`).

## 4. State and how it leaves programs' reach

|Part|Location today|Rule|
|---|---|---|
|store, record, anchors, spend ledgers, settings, cron jobs, agent profiles|`~/.eukhe/` (`sessions/`, `config.cfg`, `settings.json`, `rlm-ledger/`, `cron-jobs.json`)|state tree: no content read, write, create, remove, rename or link, and no change of mode, owner, times or extended attributes|
|credentials|`~/.eukhe/auth.json`, `dashboard-token`; provider CLI config files and AWS files when Eukhe uses them for a provider|state: no read|
|daemon and worker sockets|`$TMPDIR/eukhe-<uid>/`|macOS: pathname sockets moved to `~/.eukhe/run/` (phase 0), denied by the profile. Linux: abstract sockets (decision 3), unreachable from confined programs (`unix_scoped`, §5); since a process of any user on the host can connect to or squat an abstract name, both ends check peer credentials (`SO_PEERCRED`): the daemon and workers serve only a peer of their own uid, and a client accepts only a server of its uid whose pid equals the one recorded under `~/.eukhe/run/` (phase 0). The uid check keeps other users out; confined programs of the same uid are kept out by the scope, not by the check|
|snapshots, child copies, check copies|`~/.eukhe/workspaces/`, snapshot dirs|moved to one work root outside `~/.eukhe` and outside every tree a shipped profile writes, the temp dir included (phase 0). The whole work root is state, with only a run's own copy, its scope, allowed back; so a copy Eukhe creates after a long-lived program started is out of that program's reach|
|check definitions and held-out content|contract paths (V5)|copied under `~/.eukhe` when the contract sets them, held-out content under names derived from its digest so that a file name carries none of it; the check runs from that copy. State for the worker's programs; read-only input for the check's own command|
|project policy|`<project>/.eukhe/`|not state: every key applies only while the directory's digest equals one the principal accepted; a changed digest drops the project settings until the principal accepts them again|
|Eukhe's executables and its launcher|the running binary's directory; the launcher is Eukhe's own binary, no helper from `PATH`|no write|
|auto-start locations|`~/Library/LaunchAgents`, `~/.config/systemd/user`, `~/.config/autostart`, the user's crontab (through `crontab`, a setuid or daemon path)|state: no write; they run code later with the user's full access, Eukhe's state included|
|Eukhe's processes|supervisor, workers, tiny workers, dashboard|no signal, trace, or change of limits or scheduling; loopback services answer only to a token that is state|
|Eukhe's process control files (Linux)|`/proc/<pid>/` of each Eukhe process (`oom_score_adj` and other files the same user may write); the cgroup directories holding them (`cgroup.kill`, `cgroup.freeze`, `memory.max`)|state: no write. No write tree reaches `/proc` or `/sys`: the core refuses a write grant there and cuts both out of a wider one (`Write{/}`), so a program changes its own process settings only through system calls (narrowed)|
|principal channel endpoints|the terminal device of each Eukhe client (the TUI's `/dev/pts/N` or `/dev/ttysNNN`) and every other terminal device of the user|state: no read, no write. A profile reaches `/dev` only through `null`, `zero`, `full`, `random`, `urandom`, `fd` and `ptmx`; a terminal device opened by path is denied except in tier N, which mounts a private `devpts` instance, so a program that opens the pty it created by path fails elsewhere (narrowed)|
|aliases of state|hard links to a state file; bind mounts and firmlinks of a state directory|classed state by device and inode (files and directories) and by the mount table when the listing is built. A hard link outside the listed paths escapes any rule by path, so Eukhe creates each state file with one link, replaces files by rename, and before each program run Rust checks every state file's link count: a count above one is an alias, and that program run breaks isolation (C15)|

Linux without a PID namespace leaves `/proc/<pid>/cmdline` and `status` of
Eukhe's processes readable; C8 keeps credentials out of argv and
environment, and `environ`, `mem` and descriptors need the ptrace access
Landlock scopes.

The core takes the state list as input (Rust gathers the real paths and
inodes), so a law ranges over every list. State is a fixed set of roots
that exist before the first program run (`~/.eukhe`, the work root, the
listed credential files, the auto-start locations, Eukhe's executables'
directory, the terminal devices, `/proc` and `/sys`); every part created
later lies beneath one, so a rule on a root, taken at a program's start,
covers what Eukhe creates under it during that program's life. A contract
path becomes state only through its copy under `~/.eukhe`.

## 5. Grant-to-mechanism mapping

Seatbelt profile: `(deny default)`, rules in this order, later rules winning
(R§1.1). Linux: Eukhe's own launcher, with no bubblewrap or other helper
(decision 4): Landlock rules per real path and a seccomp filter, plus user,
mount, network and PID namespaces where user namespaces can be created,
which give per-host network, process isolation and, without Landlock, file
rules by mounts. The launcher, on every
platform, starts the program in a new session with no controlling terminal
(`setsid`, stdin a pipe or `/dev/null`) and closes every descriptor from 3
up before `exec`, so no terminal or inherited socket reaches it; it forks
the program and stays its parent (§1, run end). In tier N
it drops every capability, empties the bounding set, sets no_new_privs, and
its seccomp filter denies `mount`, `umount2`, `move_mount`, `open_tree`,
`fsopen`, `fsmount` and `pivot_root`, so the program cannot undo the mounts
its own user namespace lets it change.

|Profile part|macOS (Seatbelt)|Linux Landlock (by ABI)|Linux seccomp|Linux namespaces|Platform lacking it|
|---|---|---|---|---|---|
|base|`process-exec`, `process-fork`; `sysctl-read` list; `mach-lookup` only libinfo, dirhelper, FSEvents and the run's marker (§1); `(deny mach-lookup (xpc-service-name-prefix ""))`; `(deny system-fcntl (fcntl-command 80 110))` (R§3.1); `/dev` per §4|handled rights = every right of the ABI; ptrace limited to the domain; `/dev` per §4|kill on foreign arch; every rule also with the x32 bit; a syscall number newer than the filter's audited table returns `ENOSYS`; deny `io_uring_*`, `bpf`, `perf_event_open`, `userfaultfd`, `keyctl`, `add_key`, `request_key`, `kexec_*`, `unshare` and `clone` with `CLONE_NEWUSER`; `clone3` returns `ENOSYS` (its flags are out of the filter's reach); `socket` only for the families, types and protocols the profile needs (`AF_UNIX` when allowed; `AF_INET*` only as `SOCK_STREAM` with protocol 0 or TCP and `SOCK_DGRAM` with protocol 0 or UDP, the type masked of `SOCK_NONBLOCK` and `SOCK_CLOEXEC`), so MPTCP, SCTP (which `SOCK_SEQPACKET` with protocol 0 selects) and SMC, which Landlock's TCP rights do not cover (R§2.1), are denied; `socket(AF_VSOCK)` denied; `sendto`, `sendmsg` and `sendmmsg` with `MSG_FASTOPEN` in their flags denied (TCP Fast Open connects without Landlock's connect check, R§4); `prlimit64`, `sched_setaffinity`, `sched_setscheduler`, `sched_setparam` and `sched_setattr` only with pid 0, `setpriority` only with `PRIO_PROCESS` and 0, `ioprio_set` only with `IOPRIO_WHO_PROCESS` and 0 (Landlock scopes signals and ptrace, not limits or scheduling, R§2.1); ioctl `TIOCSTI`, `TIOCLINUX` denied. Without a mount namespace, the path forms of metadata changes, which Landlock does not restrict (R§2.1), are denied: `chmod`, `fchmodat`, `fchmodat2`, `chown`, `lchown`, `fchownat`, `utime`, `utimes`, `futimesat`, `utimensat` with a non-NULL path, `setxattr`, `lsetxattr`, `removexattr`, `lremovexattr`, `setxattrat`, `removexattrat`, `file_setattr` (**narrowed**: `chmod +x`, `touch -d`, `cp -p` fail); the descriptor forms (`fchmod`, `fchown`, `utimensat` with a NULL path, `fsetxattr`, `fremovexattr`) stay, and they refuse an `O_PATH` descriptor. Reads of metadata (`stat`, `access`, `getxattr`, `file_getattr`) and file notifications (`inotify_add_watch`, which file watchers need) stay allowed: on these tiers a state part's metadata and entry names are readable, never its content (C9)|new PID and IPC namespaces; killed with the launcher|—|
|`Read{t}` minus state|`(allow file-read* (subpath t))`, then `(deny file-read* …)` per state part|`READ_FILE`, `READ_DIR`, `EXECUTE` on the real paths of the siblings along each path from `t` to a state part; no right on the directories of that path, so no descriptor to them opens and their metadata cannot change (**narrowed**: they cannot be listed). A program can change the mode, group, times and extended attributes of a file it owns in `t` through a descriptor it opened for reading (**widened**, reported)|—|read-only bind (metadata changes fail with `EROFS`); state parts covered by an empty tmpfs|no Landlock and no namespaces: needs `Unconfined`|
|`Write{t}` minus state|`(allow file-write* (subpath t))`; `(deny file-write* …)` per state part; `(deny file-write* (literal a))` on every ancestor `a` of a state part inside `t`, which denies its removal, rename and metadata changes|write, make, remove, `TRUNCATE` (ABI 3), `REFER` (ABI 2) on the siblings along each path to a state part; none on the directories of that path: entries directly in them cannot be created, removed or renamed (**narrowed**, reported)|—|bind; every state part under a bind covered by an empty read-only tmpfs; the directories on a path to a state part bound read-only with their other entries bound writable (**narrowed** as on Landlock)|as above|
|deferred execution files in a write tree (§8's deny set; decision 10)|`(deny file-write* (literal p) (subpath p))` per deny-set path after every grant, whether or not `p` exists; `(deny file-write-unlink …)` on its ancestors inside `t`; `(deny file-write-create (regex #"/\.git$"))` inside every write tree, so no new repository or `.git` file appears (`git init`, `git clone`, `cargo new` narrowed)|— (allow-only: a rule cannot remove them from a write tree without narrowing the project root and `.git`); listed in the report, with every `.git` entry created in a write tree|—|each one existing at start bound read-only; an absent one, and every `.git` entry created in a write tree, is listed in the report|listed in the report|
|`Socket{p}`, `p` on the release's agent-socket list (C9)|`(allow network-outbound (remote unix-socket (path-literal p)))`; state sockets denied after every grant|`RESOLVE_UNIX` (ABI 9) on `p`|ABI < 9, tier N included: `socket(AF_UNIX)` denied, `socketpair` kept; `Socket` grants unavailable|a bind shows the live sockets of the directory it binds (`/tmp/tmux-<uid>/`, `/tmp/.X11-unix/`), so the mount namespace scopes no pathname socket; a new network namespace scopes abstract sockets|as for ABI < 9|
|signals and process access|`(allow signal (target same-sandbox))`, `process-info*` same sandbox|`SCOPE_SIGNAL`, `SCOPE_ABSTRACT_UNIX_SOCKET` (ABI 6)|limits and scheduling of pid 0 only (base)|PID namespace|ABI < 6 without namespaces: tier L3|
|`NoNet`|no `network-outbound` rule|TCP connect and bind handled, no rule (ABI 4); UDP handled (ABI 10)|ABI < 10: `socket(AF_INET*)` with type `SOCK_DGRAM` (type masked as above) denied|empty network namespace|—|
|`Proxy{hosts}`|`(allow network-outbound (remote ip "localhost:<port>"))` for the run's own proxy port; `mach-lookup` of the TLS trust services; the proxy URL carries a per-run token|— (port-only rules name no host, R§2.1)|as `NoNet`|empty namespace, loopback bridge to the run's proxy port (R§3.2)|no user namespaces: per-host grants need `SendAny` or `Unconfined`|
|`AnyNet` (`SendAny`)|through the run's proxy, as `Proxy{*}` (phase 2); in phase 1, a direct `(allow network-outbound)`, which reaches every loopback service, so the run is not isolated (C15)|TCP connect on all ports and addresses, direct, loopback included, so the run is not isolated (C15); needs sr54's admission|`AF_INET*` stream and datagram sockets as in base|through the proxy, as `Proxy{*}`|—|
|`Serve{Loopback}`|`(allow network-bind network-inbound (local ip "localhost:*"))`|— (port-only: a bind takes every address)|—|own namespace's loopback|no namespaces: `Serve{Any, c}` needed|
|resource limits|`setrlimit` per process|—|—|cgroup v2 where delegated to the user|measured, never a guarantee|

`unix_scoped` holds when no socket of Eukhe and no pathname socket of
another service is reachable without a `Socket` grant. Eukhe's sockets are
pathname sockets on macOS (denied by the profile) and abstract sockets on
Linux (decision 3), unreachable by Landlock ABI 6's abstract scope, a new
network namespace, or seccomp denying `socket(AF_UNIX)`. Other services'
pathname sockets (a container engine, the Nix daemon, the desktop bus) can
act with the whole machine's or user's access, Eukhe's state included, so
they are scoped too: by Landlock ABI 9 or by seccomp denying
`socket(AF_UNIX)`, never by a mount namespace, whose binds show live
sockets; and a `Socket` grant yields a confined outcome only for a path on
the release's agent-socket list (C9).
Loopback TCP services are not scoped by a port-only mechanism, so a direct
`AnyNet` breaks isolation (C15). `signal_scoped` holds with Landlock ABI 6
or a PID namespace.

Linux tiers (R§2; ABI-to-kernel mapping confirmed, distribution kernels
unconfirmed, R§2.2). Confined and isolated on Linux needs kernel 6.12 or
later (L1, L2) or user namespaces (N); on 6.7 to 6.11 (L3) runs are
reported "confined, not isolated" (decision 2):

|Tier|Needs|Confinement|Isolation|
|---|---|---|---|
|L1|Landlock ABI ≥ 9 (7.1)|files, sockets, TCP ports; UDP by Landlock from ABI 10, by seccomp before|yes, but not with a direct `AnyNet` (C15)|
|L2|ABI 6–8 (6.12–7.0), seccomp denying `socket(AF_UNIX)`|files, TCP ports, UDP by seccomp; `Socket` grants unavailable|as L1|
|L3|ABI 4–5 (6.7–6.11), e.g. Ubuntu 24.04 GA with user namespaces restricted (R§2.3)|as L2|no: signals reach Eukhe's processes|
|N|user namespaces allowed (any ABI or none)|files by mounts, network by namespace, per-host through the proxy; with Landlock when present|yes|
|none|ABI 1–3 without user namespaces (no network rules; ABI 1–2 also no truncate right); neither Landlock nor user namespaces (WSL1; containers whose policy blocks both)|needs `Unconfined`|no|

On macOS every profile part is enforceable; nesting inside another sandbox
makes the platform "none".

## 6. Decision core (Bend)

Files: `bend/confine.bend` (rules), `bend/ffi_confine.bend` (entry),
`laws/confine.bend`, `proof/confine/`. It calls `path_policy.real` and
`path_policy.class` for real paths and classes, and the capability
decision of `SPEC.md` §5 for marks and sends.

```
type Mech:    Seatbelt{build, eukhe} | Landlock{abi, kernel, eukhe} | Userns{kernel, eukhe}
            | ProviderSandbox{attestation} | ProofClosure{closure} | NoMech
type Plat:    Plat{mech, unix_scoped, signal_scoped, per_host, loop_bind, allow_only,
                   deny_absent}
type PGrant:  Read{t} | Write{t} | Send{host, ceil} | SendAny{ceil} | Socket{p}
            | ServeLoop | ServeAny{ceil} | Unconfined{digest}
type Net:     NoNet | Proxy{hosts} | AnyNet
type Profile: Profile{read, write, narrowed, widened, deferred_denied, deferred_listed,
                      cache, net, sockets, bind}
type Outcome: Confined{profile, mech} | Unconfined{cause} | Refused{need}

profile(grants, kind, mark, default_mark, state, listing, deferred, caches,
        agent_sockets, plat) -> Profile
decide(grants, kind, ask_unconfined, mark, default_mark, state, listing, deferred,
       caches, agent_sockets, plat, escapes) -> Outcome
mark_at(runs, path_marks, position) -> marks          # each live program's mark
isolated(outcomes, plats, escapes, links, host_tools) -> Maybe<Position>   # first loss
label_bits(outcomes, escapes, links, host_tools) -> {unconfined, not_isolated}
```

`eukhe` in `Mech` is the Eukhe build whose launcher and renderer applied the
mechanism, so an escape instance in Eukhe's own set-up matches by it.
`kind` is the run's kind (interactive, scheduled, loop, autoresearch).
`listing` is the directory listing along each path from a granted tree to a
state part, with links and inodes, gathered by Rust at start; state is
the fixed roots of §4, so a profile taken at a program's start excludes
every state part Eukhe creates during that program's life (the laws range
over every position of it). `deferred` is §8's deny set with, per path, whether it
exists at start; `caches` is the release's cache tree list;
`agent_sockets` the release's agent-socket list (C9). `escapes` is the
escape list in force at each position with each instance's probe result on
the host; an instance is unfixed on the host per C19. `links` is the
result of §4's link-count check before each program run. `outcomes` carry
each program's start and end positions, so a disclosure is matched against
every program live at it. `plat.allow_only` holds on Landlock without a
mount namespace; `plat.deny_absent` holds on Seatbelt, which denies a path
whether or not it exists. `widened` lists the read trees in which a
descriptor can change a file's metadata (`plat.allow_only`, §5).

Requirement laws:

|Req|Law|States|Rejects|
|---|---|---|---|
|C9|`profile_fs_within`|For every real path in the listing, at every position of the program's life, and each access (content read, content write, create, remove, rename, link, and a change of mode, owner, times or extended attributes), the profile allows the access only when a grant of that access covers the path and the path is not state, except a metadata change through a descriptor on a file in `widened`; no access of any kind, `widened` included, reaches a state part or a directory on a path to one, except reading a state part's metadata and entry names when `plat.allow_only` (C9); a link child is judged at its target.|A profile that opens the home directory for convenience; a rule on a link child that follows it to its target (a `~/.home -> ~` link opened the state tree in the Linux probe, R§5.2); a Landlock profile that leaves `chmod 000 ~/.eukhe` or `touch -d` on a canary allowed; a Landlock profile that lets the home directory open, so `fchmod` changes it; a Seatbelt profile that denies each copy present at start rather than the work root, so a check copy made later is readable.|
|C9|`profile_fs_covers`|Every access a grant covers on a non-state path is allowed, except, when `plat.allow_only`, the entry operations in and listing of directories on a path to a state part and the path forms of metadata changes, which are exactly `narrowed`, and the writes to `deferred_denied` (`deferred_denied_or_listed`).|An empty profile; one that drops a granted tree; one that narrows more than the path to the state part; one that narrows on Seatbelt.|
|C9|`profile_net_exact`|For every confined outcome: the profile reaches host `h` exactly when `Send{h,c}` or `SendAny{c}` is held with `c` at least the run's mark; `Proxy` appears only when `plat.per_host`; a direct `AnyNet` only under `SendAny` with sr54's admission; `AnyBind` only under `ServeAny{c}` with `c` at least the mark. A `Send{h}` grant on a platform without `per_host` yields no confined outcome.|A public host open to a program that reads a secret path; a per-host grant rendered as open network on a port-only platform; a server open to every host for a program that read private data; a direct `SendAny` on a billing host without admission.|
|C9|`profile_sockets_exact`|A Unix socket path is reachable exactly when a `Socket` grant names it, it is on `agent_sockets`, it is not state, and the platform scopes pathname sockets by path (Landlock ABI 9 or Seatbelt); otherwise the outcome needs `Unconfined`.|A socket rule that reaches the daemon socket; a `Socket` grant on Landlock ABI 7 reported confined; a `Socket` grant on the Docker socket reported confined; a tier N run without Landlock ABI 9 that reaches the tmux socket through a bind of the temp dir.|
|C9, C16|`unconfined_only_by_grant`|The outcome is `Unconfined` exactly when the set holds `Unconfined` and either the step asked for it or the platform cannot enforce the profile; it is `Refused`, naming the missing grant, when the platform cannot enforce and the set lacks it; otherwise `Confined`.|An unsupported system that runs the program anyway; a run sent unconfined though its grants were enforceable and it did not ask.|
|C16|`unconfined_not_unattended_not_passed`|No shipped default of a scheduled, loop or autoresearch run holds `Unconfined`, and no spawn passes it to an agent of such a run; an agent of an interactive run holds it exactly when the run's root holds it (decision 9).|An autoresearch run whose default allows it; a loop run started from an interactive session that inherits its `Unconfined`; a subagent holding `Unconfined` its root lacks.|
|C11|`state_unreachable_when_confined`|On every platform with `unix_scoped` and `signal_scoped`, for every grant set (a grant on `/` or on the home directory included), every confined outcome without a direct `AnyNet`, every position of the program's life (state parts Eukhe creates meanwhile included), and every sequence of file and process operations its profile allows (renames, links, and metadata changes by path or descriptor included), no state content becomes readable or writable, no state part or directory on a path to one changes mode, owner, times or extended attributes, no principal channel endpoint opens, no Eukhe process control file is written, no state socket is reachable, and no Eukhe process can be signalled or have its limits or scheduling changed.|A write grant on `$TMPDIR` covering the daemon socket; a rename of the directory above a state part followed by a write at the old name; a read grant on `~` covering `auth.json`; `prlimit --pid <daemon> --fsize=0` on tier L1; `chmod 000 ~/.eukhe` on tier L2; a check copy created under the work root after a language server started, then read by it; `Write{/}` reaching `/proc/<daemon pid>/oom_score_adj` or the daemon's `cgroup.kill`; `Read{/}` opening the TUI's pty.|
|C9, C6|`written_paths_take_mark`|Every path in a run's write reach (its write trees; for an `Unconfined` run, every path the user can write) carries at least the run's mark from the run's start, so any later run, of this session or a later one on the account and machine, whose profile reads it has at least that mark; at every position, a live program whose read trees overlap the write reach of a run started since, or of a live program whose mark rose, has at least that mark, and its own write reach takes it in turn; a live program accepts no input above its current mark, and one whose profile allows a direct send or `AnyBind` with a ceiling below its current mark, or that holds the cache grant at a mark above the default mark, is stopped before the run that raised the mark starts.|A secret-mark run writing into the project and a public-mark run then sending the file out; a kernel fed a secret on stdin after starting with a public network grant; a public-mark kernel, already running, that reads a file a later secret-mark command wrote into the shared temp dir and sends it; a raised kernel that copies the secret into a tree another run reads at public mark; a confined run that reads a file an `Unconfined` run wrote, at a mark below the highest; a session that reads at public mark a file a secret-mark session wrote the day before.|
|C9, C17|`deferred_denied_or_listed`|For each deny-set path inside a write tree of the profile: its writes, creation, removal and rename are denied when `plat.deny_absent`, or when the path exists at start and `not plat.allow_only`; every other such path is in `deferred_listed`; when `plat.deny_absent`, creating an entry named `.git` anywhere in a write tree is denied, and elsewhere every `.git` entry the run creates there is listed; no deny-set path lies in both sets and none outside a write tree is in either.|A macOS profile leaving `.git/hooks/pre-commit` writable; a Landlock run whose written hook is not listed; an absent `.envrc` in tier N reported as denied; a `.git` file created in a subdirectory, pointing at a config with `core.fsmonitor`, neither denied nor listed.|
|C9, C6|`cache_grant_within_mark`|A profile writes a cache tree only for an interactive run whose mark is at most the contract's default mark, and only trees on the release's cache list, none of which holds a directory on the default `PATH` or a tool's configuration file.|A secret-mark run filling `~/.cargo/registry`; an autoresearch run holding the cache grant; a cache grant covering `~/.cargo/bin` or `~/.npmrc`.|
|C15|`isolation_lost_at_first_reach`|`isolated` returns the position of the first event that is a program run whose outcome is `Unconfined`, a program run whose platform lacks `unix_scoped` or `signal_scoped`, a confined program run with a direct `AnyNet`, a program run whose mechanism version has an instance in the escape list in force that is unfixed on its host (C19), a disclosure at whose position a program run under a version it leaves unfixed is live, a program run started while `links` shows a state file with more than one link, or a call of a host tool declared to execute agent-supplied content or undeclared; none when no such event exists.|A run reported isolated after an unconfined `npm install`; one reported isolated on tier L3; one reported isolated after a direct `SendAny` on tier L1 or on macOS in phase 1; one reported isolated after an undeclared host tool ran; one reported isolated on a kernel at an instance's fixed version whose probe failed; a kernel live when a disclosure for its kernel arrived, the run still isolated; one reported isolated while a hard link to `auth.json` sat in the project; one reported not isolated though every program ran on tier L1 with no disclosure.|
|C15|`notice_before_loss`|In the host model, the event at the loss position happens only after the notice naming that position and the head digest is delivered on the principal channel and stored where no agent effect writes; at a loss placed by a disclosure, the notice is delivered at the disclosure's ingestion, before the next decided effect, and the report says it followed the loss.|A notice written after the launch; a notice kept only in the record; no notice before an undeclared host tool's call; a disclosure's notice held back until the next program start.|
|C18|`label_unconfined_exact`|`unconfined` is set exactly when some program run, check and proof runs included, ended `Unconfined`, or was live at a position where the escape list in force held an instance unfixed on its host for its mechanism version (C19).|A qualifier kept after every run was confined; one dropped though a check ran unconfined; a long-lived kernel started before a disclosure left unqualified; a fixed version taken as fixed without its probe.|
|C19|`disclosure_qualifies_forward`|A disclosure recorded at position `i` changes no label bit of a program run that ended before `i`; a class listed after a disclosure within it does not count as listed; a disclosure after the report's date changes no label.|A disclosure that rewrites past labels; a class added to the list after its first disclosure and then treated as covering it.|
|C20|`check_profile_within_copy`|A check's profile writes only inside its copy and has `NoNet` unless the check holds a send grant; every path it reads in the worker's write reach outside its copy (the write trees of the worker's program runs, the cache trees, and, after an `Unconfined` program of the worker, every path the user can write) is listed as an unprotected input.|A check running in the live session directory (today's `evidence.rs:295`); a check reaching the network to fetch its oracle; a check that runs a build script from a worker-written `~/.cargo/registry` while its inputs are reported protected.|
|C20|`stop_ends_unconfined_checks`|After a recorded stop no check program starts `Unconfined`, each running one is stopped before the next decided effect, and its judging is undecided with cause "stopped"; an unconfined check grant allows a run only on the digest it names.|A check judged unconfined after the stop; an unconfined check left running; a grant reused on a new work state.|
|C21|`profile_never_widens`|Over any run of the host model, the profile of a live long-lived program is never wider than at its start; a revocation that covers an effect it allows stops it before the next decided effect.|A kernel keeping network after its grant was revoked.|
|C22|`proxy_connect_is_send`|Each proxy connection is decided as a send to its host at the program's current mark; a name resolving to an address on C22's list (IPv4-mapped and NAT64 addresses judged as their IPv4 address) or to an address of one of this machine's interfaces at the dial, or an IP literal, is refused unless a grant names it.|A proxy that forwards to `169.254.169.254`; one that dials a name resolving to `0.0.0.0` or `::ffff:127.0.0.1`; one that dials a name whose AAAA record is the laptop's own global address; one that allows a host by suffix.|
|C24|`unattended_writes_in_copy`|For scheduled, loop and autoresearch runs, every write tree of every profile lies inside the harness-owned copy (their temp dir included, no cache grant), and a provider request declaring execution is a program run decided like any other.|An autoresearch run writing the live project; a loop run writing the shared temp dir or `~/.cargo/registry`; a provider-side execution request let through as a model request.|

Each law gets the bend skill's process at the commit `scripts/toolchain.env`
pins: mutation before and after, fresh blind adversaries until two in a row
find no gap, two blind triviality reviewers.

Rust keeps IO: platform facts, real paths, inodes and the listing; the
link count of every state file before each program run (§4); each
program's start and end positions (§1, run end); path marks per account
and machine; the deny set's existence at start, the digests of its listed
paths at start and end, and, where `.git` creation is not denied, a walk of
each write tree at the end of each program run for `.git` entries created
during it; each escape-list instance's probe at session start and at each
ingestion; rendering
the profile (SBPL text with paths passed as `-D` parameters, Landlock rules,
the seccomp filter, namespace set-up); starting the program through
`eukhe-daemon confine <profile-fd> -- argv`, which forks and stays the
parent (Linux: the child sets up namespaces where used, then Landlock and
seccomp, then `exec`; macOS: the child execs
`/usr/bin/sandbox-exec -p … -D …`); reading denials (Landlock audit from
ABI 7; Seatbelt's log stream); writing each outcome to the record.

## 7. Unconfined runs and platforms without a mechanism

- `Unconfined` is a grant like any other: recorded with its setter, counted
  (one irreversible count per program run, sr113), named in the report.
- Shipped interactive default: holds `Unconfined`, used per program run
  only when the step asks for it or the platform cannot enforce the
  profile. Until denial rates are measured (§9), every interactive step
  that declares network asks for it and runs unconfined, counted
  (decision 6). Subagents of an interactive run hold it exactly when the
  root does (decision 9). Scheduled, loop and autoresearch defaults: never;
  their program runs are confined or refused (C24).
- An interactive confined run whose write trees leave the project scope
  (the temp dir, the cache trees) counts one irreversible effect under tm8,
  drawn from the default tools' allowance (sr51) and reported as a lower
  bound (C17).
- An `Unconfined` run's output carries the highest mark: every path the
  user can write takes it (§1), and path marks persist per account and
  machine. Every later program run, of this run or a later one, that reads
  such a path (the shipped base read set holds the home directory) runs at
  the highest mark until the principal lowers the marks: it reads the
  caches only (decision 5), and its sends need a ceiling at the highest
  mark.
- A platform without a mechanism (tier "none", macOS inside another
  sandbox) reports it at session start; every program run there is
  `Unconfined` under the interactive default and refused otherwise.
- Provider-side execution: no provider sandbox attestation is on the
  trusted base list, so such requests are `Unconfined` (interactive) or
  refused (others).
- The principal's own commands (the TUI's user shell) are the principal's
  acts, not agent program runs; they are recorded and outside the label.

## 8. Report and label

- Record entry per program run: C17's fields; denials read (measured).
- Breach detection: canary files in each state part, read-protected and
  checked for access time and content after each program run where the
  file system keeps access times, and every denial against a state path.
  "No breach detected" is witnessed while isolation holds and marked
  unprotected after a loss (sr91), next to the statement that the record
  and spend ledgers were exposed from that position.
- Deferred execution files (decision 10). The deny set: the release's list
  (`.git/hooks/`, `.git/config`, `.envrc`, shell start-up files and
  others) taken at the project root, at each git repository found under a
  write tree at start, and at the home directory. Writes to it are denied
  on macOS whether or not a path exists, and in tier N for paths existing
  at start (bound read-only); on macOS creating an entry named `.git`
  anywhere in a write tree is denied too, since a `.git` file can point git
  at a configuration elsewhere. Every other deny-set path inside a write
  tree (Landlock without namespaces; absent at start in tier N) is
  compared by digest at start and end, every `.git` entry a program run
  created there is found by a walk at its end, and those are listed as
  witnessed facts, so the principal sees them before running software
  that executes them.
- Cache grant (decision 5): the report names the program runs that held it
  and its trees, and states that a cache's content is code later builds run
  with the principal's full access.
- Label: qualifiers per C18; "verified" needs every program run confined
  and isolation held.
- Release notes state that without the pre-loss notice an unisolated run's
  report is unprotected (sr179).

## 9. Escape list and measured properties

Escape list: a file in each release, versioned and digested; each class
with the date it was listed. Seed classes (R§4):

- macOS: Mach and XPC services reachable from the profile (PID-domain XPC
  services, bookmark agents); LaunchServices and Apple Events launches;
  file-system quirks that drop quarantine; writes through read-only
  descriptors (`fcntl` 80, 110); kernel bugs reachable from allowed calls.
- Linux: kernel bugs reachable from allowed syscalls; Landlock logic errors
  (disconnected directories, CVE-2025-68736; `SIGIO` signal-scope bypass,
  CVE-2026-72183; fixed kernel versions recorded from the stable tree before
  listing); seccomp construction (arch, x32); namespace set-up (the classes
  of bubblewrap's CVE-2026-87766 and CVE-2026-41163, to which Eukhe's own
  launcher is exposed alike); terminal injection; inherited
  descriptors; pathname sockets below ABI 9; stream protocols other than
  TCP, outside Landlock's TCP rights (erratum 1, R§2.1); connects that
  bypass Landlock's connect check (TCP Fast Open through `MSG_FASTOPEN`,
  disclosed June 2026, blocked by §5's seccomp rule, R§4); calls Landlock
  does not restrict (metadata changes, limits and scheduling of other
  processes; §5's seccomp rules); mounts a program can change inside its
  own user namespace.
- Both: auto-start locations and other files the system runs later with
  the user's full access; aliases of state (hard links, bind mounts,
  firmlinks).

A disclosed instance voids confinement on every host at or above its
introducing version that is not fixed for it. A host is fixed for it only
when both hold: its kernel or build is at or above the fixed version of its
release branch (a macOS release line, such as 15.4, 14.7.5 and 13.7.5 for
one fix; a stable kernel series; for a distribution kernel, the
distribution's fixed package version), all recorded in the list, and the
instance's probe passes on that host at session start and at the
disclosure's ingestion; a host on a branch
with no fix is unfixed; both facts are reported (decision 7). An instance
counts when it bypasses the mechanism from the shipped profile per an
advisory or a reproducer; one that a rule of the shipped profile blocks is
listed with that rule and voids nothing while its probe passes against the
shipped profile. Each instance enters the list with a probe: its reproducer
against the shipped profile, or, for an advisory without one, a test of
the fixed behaviour Eukhe writes; until it ships, every host at or above
the introducing version is unfixed. An instance in Eukhe's own launcher or
renderer is matched by the Eukhe build in the mechanism's version (§6).

Measurements (C25), each with method, sample and date:

- Escape rate: canaries (a file in each state part, a canary host, a
  daemon-socket canary command, a sentinel process) and a red-team agent
  on the strongest available model, told the profile, given a fixed budget
  per attempt; per mechanism and release; successes over attempts, a lower
  bound.
- Recall (sr96): the same harness against seeded weakened profiles (a link
  rule followed, the XPC deny removed, `socket(AF_UNIX)` allowed on ABI 7);
  recall is the share of seeded escapes found.
- Law-check closures (sr136): seeded proofs of a different term than the
  delivered one and disallowed axioms, per closure.
- Side channels: timing and resource channels between a confined program
  and the network or another run, measured, not listed.
- Time from disclosure to a fixed release, per instance.
- Cost: start-up latency per program run and run time of a fixed workload
  set (build, test, `git`, search), confined against unconfined, with
  dispersion; first single-machine figures in R§5 (macOS: +6.6 ms per
  start, +6.7 ms on `git ls-files`, 0.8% on a file walk; Linux: bubblewrap
  +4.9 ms per start, as a reference for namespace set-up; Eukhe's own
  Landlock and seccomp launcher not yet measured).
- Denial rate: share of program runs in recorded interactive sessions that
  a confined profile denies, per command family; until it is measured,
  interactive network steps run unconfined (decision 6); it gates phase 3.

## 10. Trust

Proven: the profile against the grants and the state list, the outcome,
isolation positions, label bits, over the host model. Tested: the rendering
into SBPL, Landlock rules, seccomp and namespaces (a probe suite per
platform in the nightly gate, R§5); that every program start passes through
the launcher (a permit type only `decide` makes, and a test over every
spawn site of §3), Eukhe's own calls of external tools on agent-writable
trees included. Trusted: the kernel and its mechanisms, the escape
list's content, the real-path, inode and listing code in Rust, the proxy's
forwarding (it sees the name a program presents, never the content; a grant
to a host covers whatever that host relays, R§6).

## 11. What stops working, and migration

Under a confined profile with the shipped interactive grants (sr51: the
project scope, plus a base read set listed per release with the default
tools: system and toolchain paths, the home directory but state and
secrets; writes in the project, the temp dir and, as the cache grant, the
cache trees; no network):

|Workload|Under the profile|Path back|
|---|---|---|
|editing, build, test, search, local `git`|works (R§5)|—|
|package installs, `git push` and `fetch`, downloads|no network|`Send` grants per registry host (phase 2), or `Unconfined`|
|package caches (`~/.cargo/registry`, `~/.cargo/git`, `~/.npm/_cacache`, `~/.cache`, `~/Library/Caches`, `~/go/pkg/mod`; the list ships per release, lock files included)|written under the cache grant for interactive runs at or below the contract's default mark, reported (decision 5); read-only above it, and for every program run after an `Unconfined` run until the principal lowers the marks (§7), where tools that lock or fill a cache fail; never a tool's `bin` directory or configuration file|an `Unconfined` step|
|`git config`, `git remote add`, `git submodule init`, writing hooks in a repository present at start; `git init`, `git clone`, `cargo new` creating a `.git`|denied on macOS (decision 10), the first group in tier N too; listed elsewhere|an `Unconfined` step (`git push -u` and `git clone` already run unconfined as network steps)|
|Xcode tool shims (`/usr/bin/git` and others)|need per-user temp and cache dirs and `dirhelper` (R§5.1)|in the base profile|
|new entries directly in, and listings of, a directory above a state part (`ls ~` on Landlock tiers; broad write grants on the home directory)|narrowed|tier N or macOS|
|`chmod +x`, `touch -d`, `cp -p`, `tar x` restoring modes and times (Landlock tiers without namespaces)|path forms of metadata changes denied (narrowed, reported); the descriptor forms work|tier N, macOS, or an `Unconfined` step|
|ssh, gpg signing, Docker, Podman, Nix daemon, desktop bus|sockets denied; Docker and Nix daemon sockets reach the whole machine|`Socket` grant (ssh and gpg agents); brokers only `Unconfined`|
|GUI apps, `open`, browsers, AppleScript, clipboard, Keychain|denied (R§5.1 probes)|`Unconfined`|
|programs that open a pty by path (`script`, `expect`, terminal tests); writes to `/proc` and `/sys` (a program's own `oom_score_adj`)|denied (§4: terminal devices and process control files are state); in tier N a private `devpts` serves ptys|tier N for ptys; `Unconfined`|
|local servers and tests binding ports|loopback works on macOS and tier N; L1-L3 need `Serve{Any, c}`|tier N|
|debuggers attaching to other processes; `renice`, `taskset`, `prlimit` on processes outside the run|denied outside the run|`Unconfined`|
|a long-lived kernel after a grant change|keeps its start profile|restart (C21)|
|a long-lived program whose read trees a later run writes at a higher mark|its mark rises; stopped if its direct send or `AnyBind` ceiling is below the new mark (C21)|restart|

Migration:

1. Phase 1 confines checks and non-interactive runs. In interactive runs,
   steps that declare no network (the shell's effect classes) run
   confined; steps that declare it run under the shipped `Unconfined`,
   counted, as today (decision 6).
2. A confined program that hits a denial returns its output with the
   denied access and the grant that would allow it; the agent may ask for
   the step again unconfined. That is a new ruled effect, counted; no run is
   relaunched on its own (va6).
3. Interactive network steps become confined (per-host grants for
   configured registries) only after the denial rate on recorded sessions
   is measured and the owner sets the threshold it must stay under.

## 12. Phases and effort

Estimates are engineer-weeks [INFERENCE: from the size of comparable laws
and Rust in this repository, not measured].

|Phase|Content|Removes the qualifier for|Effort|
|---|---|---|---|
|0|State relocation: macOS sockets to `~/.eukhe/run/`, Linux daemon and worker IPC to abstract sockets with peer-credential checks on both ends; copies and snapshots to one work root outside `~/.eukhe` and the temp dir, made with `clonefile`, `FICLONE` or a plain copy (R§3.4), never `git worktree`; contract paths copied under `~/.eukhe`, held-out content under digest names; state files kept at one link; path marks per account and machine; the state list in one place; project trust bound to a digest; checks on a copy|nothing yet|2|
|1|Core and laws of §6 but `proxy_connect_is_send`; Eukhe's launcher as the parent of every run (subreaper on Linux, per-run marker on macOS), through which Eukhe's own external tool calls on agent-writable trees also go; Seatbelt and Landlock+seccomp renderers (the `MSG_FASTOPEN`, metadata, limits and scheduling rules, `/dev` and `/proc` rules included); `NoNet` and direct `SendAny` only (not isolated, C15); cache grant; deferred execution file denies (macOS) and listing, `.git` creation included; link-count check; record, report and pre-loss notice; escape list v1 with probes and disclosure ingestion (C19); probe suite; cost figures; a first escape-rate and recall measurement per mechanism (C25), referenced by every report that relies on confinement|runs whose programs need no network, on macOS and on Linux 6.12 or later (tiers L1, L2): checks, autoresearch and loop runs, interactive edit-build-test sessions|9|
|2|Proxy with per-run port and token; per-host `Send`; `SendAny` through the proxy; tier N in Eukhe's own launcher (user, mount, network and PID namespaces; no bubblewrap) with its deferred execution file binds; `Socket` grants|runs that fetch only from granted hosts|5|
|3|Interactive network steps confined once denial rates are measured and the owner set the threshold; long-lived program restart on grant change; cgroup limits where delegated|interactive sessions with package installs from granted registries|3|
|4|Red-team harness at full size, closure seeds, side-channel measurement, publication per release (C25)|— (measures)|2, then per release|

## 13. Owner decisions (applied)

1. Same OS user: no separate uid. sr179 is reworded so that a program run
   keeps isolation only when it is confined and unable to reach Eukhe's
   state; it breaks isolation when it is unconfined, or confined yet able
   to reach the core's files, credentials, sockets or processes (C15). The
   row's text in the philosophy changes accordingly. With decision 2
   ("confined, not isolated" on L3), df9's "confinement in force" is read
   the same way: a listed mechanism version with no disclosed, unfixed
   escape, without "isolation held", which the separate "not isolated"
   qualifier carries (C18); df9's text in the philosophy changes
   accordingly.
2. Linux floor for "confined and isolated": kernel 6.12 or later (Landlock
   ABI 6, which scopes abstract sockets and signals; tiers L1, L2) or user
   namespaces (tier N). On 6.7 to 6.11 (L3) runs are reported "confined,
   not isolated".
3. Daemon and worker IPC on Linux: abstract sockets scoped by Landlock ABI
   6 (or a network namespace, or seccomp's `AF_UNIX` denial), with peer
   credential checks on both ends (§4).
4. Eukhe's own launcher (Landlock and seccomp), with user namespaces where
   the system allows them, for per-host network and PID isolation; no
   bubblewrap dependency.
5. Package caches: a shipped write grant on the release's cache trees, for
   runs at or below the contract's default mark, reported (§8, §11). It
   applies to interactive runs: scheduled, loop and autoresearch runs
   write only their copy (sr51, C24).
6. Interactive network steps run unconfined and counted until denial
   rates are measured; the threshold for confining them is set then.
7. An instance counts as fixed on a host only with the fixed version and a
   passing probe, both reported (§9).
8. Law renames in `SPEC.md` §4 (spec-only; none is in `LAWS.bend`):
   `profile_within_allowed` becomes `profile_fs_within`,
   `profile_fs_covers` and `profile_net_exact`; `run_unconfined_needed`
   becomes `unconfined_only_by_grant`;
   `run_unconfined_not_default_not_passed` becomes
   `unconfined_not_unattended_not_passed`. They are applied to `SPEC.md`
   with C9 and C11's text from §2 when phase 1 lands.
9. Subagents of an interactive run inherit the root's `Unconfined` grant;
   no spawn passes it to a scheduled, loop or autoresearch run (C16).
10. Deferred execution files: writes denied on macOS and in tier N; listed
    in the report on Landlock alone and wherever a namespace cannot cover
    a path (§8).
11. New dependencies: a Landlock crate and a seccomp crate with safe APIs;
    `/usr/bin/sandbox-exec` on macOS (marked deprecated in its man page,
    no replacement for command-line programs, R§1.1).
12. Windows: unsupported.
