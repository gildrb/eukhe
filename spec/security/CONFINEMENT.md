# security (spec): confinement and isolation

Status: design draft. Nothing below is built; no law named here exists.
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
disclosed, unfixed escape; "not isolated" is a separate qualifier.

Philosophy rows covered: scope statement, ds10, df9, sr18, sr41, sr73,
sr91, sr98, sr119, sr136, sr161, sr172, sr179; record T11.

## 1. Words

- **program run**: one process image an agent causes to start, with every
  process it forks or execs: an external command of the `bash` tool, a
  Python kernel, an MCP stdio server, a language server, a check's command,
  a law check's proof run, and a model request to a provider that declares
  provider-side execution (sr73). Eukhe's own processes (supervisor,
  workers, tiny workers) are not program runs; they are the trusted base
  (df6).
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
  its profile reads. Every path in a run's write trees takes the run's mark
  from the run's start (C6), so a later run that reads it counts it. A
  long-lived program's mark is fixed at start; an input above it is refused
  (C7).
- **profile**: what the mechanism allows one program run: read trees, write
  trees; network (`NoNet`, `Proxy{hosts}`, `AnyNet`); Unix socket paths;
  bind (`NoBind`, `Loopback`, `AnyBind`); signals and process access
  limited to the run's own processes.
- **mechanism**: one of the kinds of sr161 with its version: Seatbelt on a
  macOS build; Landlock at an ABI with a seccomp filter on a kernel
  release; user, mount, network and PID namespaces with a seccomp filter; a
  provider sandbox with an attestation on the trusted base list; a proof
  under a listed closure (df10). **listed**: on the release's escape list
  (§9) with its escape classes.
- **escape list in force** at a position: the release's list plus every
  disclosure recorded in the run up to that position.
- **platform facts**: what the host reports before each program run: OS and
  build or kernel release, Landlock ABI, whether user namespaces can be
  created, whether a Seatbelt profile can be applied (it cannot inside an
  already sandboxed process, R§1.2).
- **outcome** of a program run: `Confined{profile, mechanism}`,
  `Unconfined{cause}` or `Refused{grant needed}`.
- **deferred execution file**: a file that software outside Eukhe runs
  later without asking (`.git/hooks/*`, `.git/config`, shell start-up
  files, `.envrc`). Writing one inside a write grant is within the grant;
  its later run is the principal's program run, outside Eukhe (§8).

## 2. Requirements

|Id|Requirement|Rows|
|---|---|---|
|C9|A program holds its grants. Every program run is started under a listed mechanism with the profile the core computed from the run's grants: it reads and writes a real path only when a grant covers it and the path is not state, and every such path except those §5 names as narrowed; it reaches a host only under a `Send` or `SendAny` grant whose ceiling is at least the run's mark, through Eukhe's proxy wherever the platform can force it (§5), and directly only under `SendAny` with sr54's admission; it accepts connections from other hosts only under `Serve{Any, c}` with `c` at least that mark; it connects to a Unix socket only under a `Socket` grant; it signals, traces and inspects only processes of its own run. When the platform cannot enforce a part of the profile, the run is started only under `Unconfined` and counted (tm8, sr113), else refused naming the grant needed.|ds10, df9, sr161, sr54|
|C11|The policy and the state protect themselves. While isolation holds, nothing an agent does and nothing a program it runs does changes the store or any other state part: no effect, message, daemon or CLI command, file write, rename, link, socket connection or signal. A write to the store's files asks a user whatever the set holds. The project's `.eukhe/` is not state: its keys apply only at a digest the principal accepted (§4).|df9, T11|
|C15|Isolation is a fact per position. A run is isolated up to the first of: an `Unconfined` program run; a confined run on a platform where signals or sockets of Eukhe are reachable (§5, tier L3); a confined run under a mechanism version with a disclosed, unfixed instance on the escape list in force; a call of an in-process host tool that executes agent-supplied content or declares nothing (C23). Before it, the harness delivers on the principal channel, stored out of agents' reach, the head digest and a notice naming the position (sr179); from it on the run is not isolated, its facts are unprotected (sr91), and a software delegate's decision is judged from that notice (sr151).|sr179, sr91, sr151, sr98, df8|
|C16|Platforms without a mechanism. A platform that cannot enforce the profile reports so before the run; its program runs need `Unconfined`. The shipped interactive default holds `Unconfined` (sr51, sr73); no shipped default of a scheduled, loop or autoresearch run holds it (sr113, sr133); no spawn passes it (the current law; decision 9).|sr73, sr113, ds10|
|C17|Report facts (sr18). The record entry of each program run names its outcome, mechanism and version, profile digest, mark, and the digest of the escape list in force. The report states as witnessed facts: its issue date; the core builds, trusted base list versions and placements in force and when they changed; which mechanism and version each program ran under; which model requests were unconfined; the count and causes of unconfined runs; whether a breach was detected (§8); the escape list's digest and date, with a qualifier when it is older than the stated age; the position isolation was lost, if it was; and, when it relies on confinement, a reference to C25's figures for each mechanism used. Denials observed are reported as measured.|sr18, sr41|
|C18|Label. The label carries "unconfined" exactly when some program run of the run (check and proof runs included) ended `Unconfined`, or ran while the escape list in force held a disclosed, unfixed instance for its mechanism version (a long-lived program counts from the disclosure on); it carries "not isolated" exactly when C15 places a loss.|df8, sr80, sr119|
|C19|Escape list and disclosures. Each release ships an escape list: per mechanism, its escape classes, each with the date it was listed, and disclosed instances with affected and fixed versions. An escape class counts only if listed before any disclosure within it; a disclosed, unfixed instance voids confinement for its versions whether or not its class is listed. A disclosure recorded during the run qualifies the label from that position on. A disclosure after the report's date is appended as a relayed fact (source, date, content) with the witnessed fact of which mechanism versions the report's program runs used; no label changes.|sr119, df9|
|C20|Checks are confined to their copy. A check's command and a law check's proof run start under a profile that writes only inside the check's copy of the judged work state, reads nothing else the worker can write, and sends nothing unless the check holds a send grant. Judgings that run check code unconfined draw on their own irreversible allowance, a count and a value cap per run and per account, zero by default for non-interactive runs; the report states their effects are uncounted beyond that count (sr112). A recorded stop voids every grant to run check code unconfined: no such program starts after it, a running one is stopped, and the judging is undecided with cause "stopped".|tm4, sr112, sr172, sr136|
|C21|Long-lived programs. A kernel, MCP server or language server keeps the profile it started with. A grant widened later reaches it only at a restart; a revocation that covers an effect its profile allows stops it before the next effect of the subtree is decided (C5).|C5, C9|
|C22|Network through the core. Every connection a confined program opens through the proxy is an effect submitted to the core: a send to the host at the run's mark (C7), metered or refused on a billing host (sr54), recorded with author and cause. The proxy resolves each name once and dials the checked address; it refuses loopback, link-local and private ranges and IP literals unless a grant names them.|C7, sr54|
|C23|In-process placement. Every host tool or callback of the in-process placement declares whether it executes agent-supplied content; one that does, or that declares nothing, makes the run not isolated (sr98). A program it starts through Eukhe's launcher is confined like any other.|sr98, sr19|
|C24|Non-interactive runs. Scheduled, loop and autoresearch runs write only to a harness-owned copy of the scope, handed over at acceptance; they run no unconfined program, and their report's first line says so (sr113); a model request to a provider that declares provider-side execution outside a listed mechanism is an unconfined program run and refused for them, the report's first line naming the grant needed. For interactive runs the report's first line states that billed cost of unconfined program runs outside the core's rulings is unbounded.|sr73, sr113|
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
|store, record, anchors, spend ledgers, settings, cron jobs, agent profiles|`~/.eukhe/` (`sessions/`, `config.cfg`, `settings.json`, `rlm-ledger/`, `cron-jobs.json`)|state tree: no content read, write, create, remove, rename or link|
|credentials|`~/.eukhe/auth.json`, `dashboard-token`; provider CLI config files and AWS files when Eukhe uses them for a provider|state: no read|
|daemon and worker sockets|`$TMPDIR/eukhe-<uid>/`|moved to `~/.eukhe/run/` (phase 0); no connect (§5)|
|snapshots, child copies, check copies|`~/.eukhe/workspaces/`, snapshot dirs|moved to a work root outside `~/.eukhe` (phase 0); a run's own copy is its scope, every other copy is state|
|check definitions and held-out content|contract paths (V5)|state for the worker's programs; read-only input for the check's own command|
|project policy|`<project>/.eukhe/`|not state: every key applies only while the directory's digest equals one the principal accepted; a changed digest drops the project settings until the principal accepts them again|
|Eukhe's executables and launcher helpers (bubblewrap when used)|the running binary's directory; helpers by absolute path and digest, never from `PATH`|no write|
|auto-start locations|`~/Library/LaunchAgents`, `~/.config/systemd/user`, `~/.config/autostart`, the user's crontab (through `crontab`, a setuid or daemon path)|state: no write; they run code later with the user's full access, Eukhe's state included|
|Eukhe's processes|supervisor, workers, tiny workers, dashboard|no signal or trace; loopback services answer only to a token that is state|
|aliases of state|hard links to a state file; bind mounts and firmlinks of a state directory|classed state by device and inode (files and directories) and by the mount table when the listing is built|

Linux without a PID namespace leaves `/proc/<pid>/cmdline` and `status` of
Eukhe's processes readable; C8 keeps credentials out of argv and
environment, and `environ`, `mem` and descriptors need the ptrace access
Landlock scopes.

The core takes the state list as input (Rust gathers the real paths and
inodes), so a law ranges over every list.

## 5. Grant-to-mechanism mapping

Seatbelt profile: `(deny default)`, rules in this order, later rules winning
(R§1.1). Linux: Landlock rules per real path, a seccomp filter, and
namespaces where user namespaces can be created. The launcher, on every
platform, starts the program in a new session with no controlling terminal
(`setsid`, stdin a pipe or `/dev/null`) and closes every descriptor from 3
up before `exec`, so no terminal or inherited socket reaches it. In tier N
it drops every capability, empties the bounding set, sets no_new_privs, and
its seccomp filter denies `mount`, `umount2`, `move_mount`, `open_tree`,
`fsopen`, `fsmount` and `pivot_root`, so the program cannot undo the mounts
its own user namespace lets it change.

|Profile part|macOS (Seatbelt)|Linux Landlock (by ABI)|Linux seccomp|Linux namespaces|Platform lacking it|
|---|---|---|---|---|---|
|base|`process-exec`, `process-fork`; `sysctl-read` list; `mach-lookup` only libinfo, dirhelper, FSEvents; `(deny mach-lookup (xpc-service-name-prefix ""))`; `(deny system-fcntl (fcntl-command 80 110))` (R§3.1)|handled rights = every right of the ABI; ptrace limited to the domain|kill on foreign arch; every rule also with the x32 bit; deny `io_uring_*`, `bpf`, `perf_event_open`, `userfaultfd`, `keyctl`, `add_key`, `request_key`, `kexec_*`, `unshare` and `clone` with `CLONE_NEWUSER`; `clone3` returns `ENOSYS` (its flags are out of the filter's reach); `socket` only for the families and protocols the profile needs (`AF_UNIX` when allowed; `AF_INET*` with protocol 0, TCP or UDP), so MPTCP, SCTP and SMC, which Landlock's TCP rights do not cover (R§2.1), are denied; `socket(AF_VSOCK)` denied; ioctl `TIOCSTI`, `TIOCLINUX` denied|new PID and IPC namespaces; killed with the launcher|—|
|`Read{t}` minus state|`(allow file-read* (subpath t))`, then `(deny file-read* …)` per state part|`READ_FILE`, `READ_DIR`, `EXECUTE` on the real paths of the siblings along each path from `t` to a state part; `READ_DIR` alone on the directories of that path (state names listable, content not)|—|read-only bind; state parts covered by an empty tmpfs|no Landlock and no namespaces: needs `Unconfined`|
|`Write{t}` minus state|`(allow file-write* (subpath t))`; `(deny file-write* …)` per state part; `(deny file-write-unlink …)` on every ancestor of a state part inside `t`|write, make, remove, `TRUNCATE` (ABI 3), `REFER` (ABI 2) on the siblings along each path to a state part; none on the directories of that path: entries directly in them cannot be created, removed or renamed (**narrowed**, reported)|—|bind; every state part under a bind covered by an empty read-only tmpfs|as above|
|`Socket{p}`|`(allow network-outbound (remote unix-socket (path-literal p)))`; state sockets denied after every grant|`RESOLVE_UNIX` (ABI 9) on `p`|ABI < 9 without a mount namespace: `socket(AF_UNIX)` denied, `socketpair` kept; `Socket` grants unavailable|state sockets not mounted; a new network namespace for abstract sockets|as for ABI < 9|
|signals and process access|`(allow signal (target same-sandbox))`, `process-info*` same sandbox|`SCOPE_SIGNAL`, `SCOPE_ABSTRACT_UNIX_SOCKET` (ABI 6)|—|PID namespace|ABI < 6 without namespaces: tier L3|
|`NoNet`|no `network-outbound` rule|TCP connect and bind handled, no rule (ABI 4); UDP handled (ABI 10)|ABI < 10: `socket(AF_INET*)` with type `SOCK_DGRAM` (type masked of `SOCK_NONBLOCK`, `SOCK_CLOEXEC`) denied; ABI < 4: `socket(AF_INET*)` denied|empty network namespace|—|
|`Proxy{hosts}`|`(allow network-outbound (remote ip "localhost:<port>"))` for the run's own proxy port; `mach-lookup` of the TLS trust services; the proxy URL carries a per-run token|— (port-only rules name no host, R§2.1)|as `NoNet`|empty namespace, loopback bridge to the run's proxy port (R§3.2)|no user namespaces: per-host grants need `SendAny` or `Unconfined`|
|`AnyNet` (`SendAny`)|through the run's proxy, as `Proxy{*}`|TCP connect on all ports, direct; needs sr54's admission|`AF_INET*` with protocol 0, TCP or UDP|through the proxy, as `Proxy{*}`|—|
|`Serve{Loopback}`|`(allow network-bind network-inbound (local ip "localhost:*"))`|— (port-only: a bind takes every address)|—|own namespace's loopback|no namespaces: `Serve{Any, c}` needed|
|resource limits|`setrlimit` per process|—|—|cgroup v2 where delegated to the user|measured, never a guarantee|

`unix_scoped` holds when no socket of Eukhe is reachable: pathname sockets
by Landlock ABI 9, by seccomp denying `socket(AF_UNIX)`, or by a mount
namespace; abstract sockets by Landlock ABI 6 or a new network namespace.
`signal_scoped` holds with Landlock ABI 6 or a PID namespace.

Linux tiers (R§2; ABI-to-kernel mapping confirmed, distribution kernels
unconfirmed, R§2.2):

|Tier|Needs|Confinement|Isolation|
|---|---|---|---|
|L1|Landlock ABI ≥ 9 (7.1)|files, sockets, TCP ports; UDP by Landlock from ABI 10, by seccomp before|yes|
|L2|ABI 6–8 (6.12–7.0), seccomp denying `socket(AF_UNIX)`|files, TCP ports, UDP by seccomp; `Socket` grants unavailable|yes|
|L3|ABI 4–5 (6.7–6.11), e.g. Ubuntu 24.04 GA with user namespaces restricted (R§2.3)|as L2|no: signals reach Eukhe's processes|
|N|user namespaces allowed (any ABI or none)|files by mounts, network by namespace, per-host through the proxy; with Landlock when present|yes|
|none|ABI 1–3 without user namespaces (no truncate or network rules); neither Landlock nor user namespaces (WSL1; containers whose policy blocks both)|needs `Unconfined`|no|

On macOS every profile part is enforceable; nesting inside another sandbox
makes the platform "none".

## 6. Decision core (Bend)

Files: `bend/confine.bend` (rules), `bend/ffi_confine.bend` (entry),
`laws/confine.bend`, `proof/confine/`. It calls `path_policy.real` and
`path_policy.class` for real paths and classes, and the capability
decision of `SPEC.md` §5 for marks and sends.

```
type Mech:    Seatbelt{build} | Landlock{abi, kernel} | Userns{kernel}
            | ProviderSandbox{attestation} | ProofClosure{closure} | NoMech
type Plat:    Plat{mech, unix_scoped, signal_scoped, per_host, loop_bind, allow_only}
type PGrant:  Read{t} | Write{t} | Send{host, ceil} | SendAny{ceil} | Socket{p}
            | ServeLoop | ServeAny{ceil} | Unconfined{digest}
type Net:     NoNet | Proxy{hosts} | AnyNet
type Profile: Profile{read, write, narrowed, net, sockets, bind}
type Outcome: Confined{profile, mech} | Unconfined{cause} | Refused{need}

profile(grants, state, listing, plat) -> Profile
decide(grants, ask_unconfined, mark, state, listing, plat, escapes) -> Outcome
isolated(outcomes, plats, escapes, host_tools) -> Maybe<Position>   # first loss
label_bits(outcomes, escapes, host_tools) -> {unconfined, not_isolated}
```

`listing` is the directory listing along each path from a granted tree to a
state part, with links and inodes, gathered by Rust at start. `escapes` is
the escape list in force at each position.

Requirement laws:

|Req|Law|States|Rejects|
|---|---|---|---|
|C9|`profile_fs_within`|For every real path in the listing and each access (content read, content write, create, remove, rename, link), the profile allows the access only when a grant of that access covers the path and the path is not state; a link child is judged at its target.|A profile that opens the home directory for convenience; a rule on a link child that follows it to its target (a `~/.home -> ~` link opened the state tree in the Linux probe, R§5.2); a hard link to `auth.json` inside the project left readable.|
|C9|`profile_fs_covers`|Every access a grant covers on a non-state path is allowed, except the entry operations in directories on a path to a state part when `plat.allow_only`, and those are exactly `narrowed`.|An empty profile; one that drops a granted tree; one that narrows more than the path to the state part; one that narrows on Seatbelt.|
|C9|`profile_net_exact`|For every confined outcome: the profile reaches host `h` exactly when `Send{h,c}` or `SendAny{c}` is held with `c` at least the run's mark; `Proxy` appears only when `plat.per_host`; a direct `AnyNet` only under `SendAny` with sr54's admission; `AnyBind` only under `ServeAny{c}` with `c` at least the mark. A `Send{h}` grant on a platform without `per_host` yields no confined outcome.|A public host open to a program that reads a secret path; a per-host grant rendered as open network on a port-only platform; a server open to every host for a program that read private data; a direct `SendAny` on a billing host without admission.|
|C9|`profile_sockets_exact`|A Unix socket path is reachable exactly when a `Socket` grant names it, it is not state, and the platform scopes pathname sockets by path (Landlock ABI 9, Seatbelt, or a mount namespace); otherwise the outcome needs `Unconfined`.|A socket rule that reaches the daemon socket; a `Socket` grant on Landlock ABI 7 reported confined.|
|C9, C16|`unconfined_only_by_grant`|The outcome is `Unconfined` exactly when the set holds `Unconfined` and either the step asked for it or the platform cannot enforce the profile; it is `Refused`, naming the missing grant, when the platform cannot enforce and the set lacks it; otherwise `Confined`.|An unsupported system that runs the program anyway; a run sent unconfined though its grants were enforceable and it did not ask.|
|C16|`unconfined_not_unattended_not_passed`|No shipped default of a scheduled, loop or autoresearch run holds `Unconfined`, and no spawn passes it.|A child inheriting the parent's unconfined shell; an autoresearch run whose default allows it.|
|C11|`state_unreachable_when_confined`|On every platform with `unix_scoped` and `signal_scoped`, for every grant set (a grant on `/` or on the home directory included), every confined outcome, and every sequence of file operations its profile allows (renames and links included), no state content becomes readable or writable, no state socket is reachable, and no Eukhe process can be signalled.|A write grant on `$TMPDIR` covering the daemon socket; a rename of the directory above a state part followed by a write at the old name; a read grant on `~` covering `auth.json`.|
|C9, C6|`written_paths_take_mark`|Every path in a confined run's write trees carries at least the run's mark from the run's start, so any later run whose profile reads it has at least that mark; a long-lived program accepts no input above the mark it started with.|A secret-mark run writing into the project and a public-mark run then sending the file out; a kernel fed a secret on stdin after starting with a public network grant.|
|C15|`isolation_lost_at_first_reach`|`isolated` returns the position of the first event that is a program run whose outcome is `Unconfined`, a program run whose platform lacks `unix_scoped` or `signal_scoped`, a program run whose mechanism version has a disclosed, unfixed instance in the escape list in force, or a call of a host tool declared to execute agent-supplied content or undeclared; none when no such event exists.|A run reported isolated after an unconfined `npm install`; one reported isolated on tier L3; one reported isolated after an undeclared host tool ran; one reported not isolated though every program ran on tier L1 with no disclosure.|
|C15|`notice_before_loss`|In the host model, the event at the loss position happens only after the notice naming that position and the head digest is delivered on the principal channel and stored where no agent effect writes.|A notice written after the launch; a notice kept only in the record; no notice before an undeclared host tool's call.|
|C18|`label_unconfined_exact`|`unconfined` is set exactly when some program run, check and proof runs included, ended `Unconfined`, or was live at a position where the escape list in force held a disclosed, unfixed instance for its mechanism version.|A qualifier kept after every run was confined; one dropped though a check ran unconfined; a long-lived kernel started before a disclosure left unqualified.|
|C19|`disclosure_qualifies_forward`|A disclosure recorded at position `i` changes no label bit of a program run that ended before `i`; a class listed after a disclosure within it does not count as listed; a disclosure after the report's date changes no label.|A disclosure that rewrites past labels; a class added to the list after its first disclosure and then treated as covering it.|
|C20|`check_profile_within_copy`|A check's profile writes only inside its copy, reads no path the worker can write other than the copy, and has `NoNet` unless the check holds a send grant.|A check running in the live session directory (today's `evidence.rs:295`); a check reaching the network to fetch its oracle.|
|C20|`stop_ends_unconfined_checks`|After a recorded stop no check program starts `Unconfined`, each running one is stopped before the next decided effect, and its judging is undecided with cause "stopped"; an unconfined check grant allows a run only on the digest it names.|A check judged unconfined after the stop; an unconfined check left running; a grant reused on a new work state.|
|C21|`profile_never_widens`|Over any run of the host model, the profile of a live long-lived program is never wider than at its start; a revocation that covers an effect it allows stops it before the next decided effect.|A kernel keeping network after its grant was revoked.|
|C22|`proxy_connect_is_send`|Each proxy connection is decided as a send to its host at the run's mark; a name resolving to loopback, link-local or a private range, or an IP literal, is refused unless a grant names it.|A proxy that forwards to `169.254.169.254`; one that allows a host by suffix.|
|C24|`unattended_writes_in_copy`|For scheduled, loop and autoresearch runs, every write tree of every profile lies inside the harness-owned copy, and a provider request declaring execution is a program run decided like any other.|An autoresearch run writing the live project; a provider-side execution request let through as a model request.|

Each law gets the bend skill's process at the commit `scripts/toolchain.env`
pins: mutation before and after, fresh blind adversaries until two in a row
find no gap, two blind triviality reviewers.

Rust keeps IO: platform facts, real paths, inodes and the listing; rendering
the profile (SBPL text with paths passed as `-D` parameters, Landlock rules,
the seccomp filter, namespace set-up); starting the program through
`eukhe-daemon confine <profile-fd> -- argv` (Linux: namespaces where used,
then Landlock and seccomp, then `exec`; macOS:
`/usr/bin/sandbox-exec -p … -D …`); reading denials (Landlock audit from
ABI 7; Seatbelt's log stream); writing each outcome to the record.

## 7. Unconfined runs and platforms without a mechanism

- `Unconfined` is a grant like any other: recorded with its setter, counted
  (one irreversible count per program run, sr113), named in the report.
- Shipped interactive default: holds `Unconfined`, used per program run
  only when the step asks for it or the platform cannot enforce the
  profile. Scheduled, loop and autoresearch defaults: never; their program
  runs are confined or refused (C24).
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
- Deferred execution files written by the run are listed as witnessed facts
  (from the snapshot's difference), so the principal sees them before
  running software that executes them.
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
  listing); seccomp construction (arch, x32); namespace set-up (bubblewrap
  CVE-2026-87766, CVE-2026-41163); terminal injection; inherited
  descriptors; pathname sockets below ABI 9; stream protocols other than
  TCP, outside Landlock's TCP rights (erratum 1, R§2.1); mounts a program
  can change inside its own user namespace.
- Both: auto-start locations and other files the system runs later with
  the user's full access; aliases of state (hard links, bind mounts,
  firmlinks).

An instance voids confinement for its affected versions. A kernel or build
at or above the fixed version is outside it; a distribution kernel that
backports the fix without the version is outside it only by a passing
probe, and that judgement is reported as measured.

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
  +4.9 ms per start; the Landlock and seccomp launcher not yet measured).
- Denial rate: share of program runs in recorded interactive sessions that
  a confined profile denies, per command family; gates phase 3.

## 10. Trust

Proven: the profile against the grants and the state list, the outcome,
isolation positions, label bits, over the host model. Tested: the rendering
into SBPL, Landlock rules, seccomp and namespaces (a probe suite per
platform in the nightly gate, R§5); that every program start passes through
the launcher (a permit type only `decide` makes, and a test over every
spawn site of §3). Trusted: the kernel and its mechanisms, the escape
list's content, the real-path, inode and listing code in Rust, the proxy's
forwarding (it sees the name a program presents, never the content; a grant
to a host covers whatever that host relays, R§6).

## 11. What stops working, and migration

Under a confined profile with the shipped interactive grants (sr51: the
project scope, plus a base read set listed per release with the default
tools: system and toolchain paths, the home directory but state and
secrets; writes in the project and temp dir; no network):

|Workload|Under the profile|Path back|
|---|---|---|
|editing, build, test, search, local `git`|works (R§5)|—|
|package installs, `git push` and `fetch`, downloads|no network|`Send` grants per registry host (phase 2), or `Unconfined`|
|caches outside the project (`~/.cargo`, `~/.npm`, `~/.cache`, `~/Library/Caches`, `~/go/pkg/mod`)|read-only; tools that lock or fill a cache fail|decision 5|
|Xcode tool shims (`/usr/bin/git` and others)|need per-user temp and cache dirs and `dirhelper` (R§5.1)|in the base profile|
|new entries directly in a directory above a state part (Landlock tiers, broad write grants on the home directory)|narrowed|tier N or macOS|
|ssh, gpg signing, Docker, Podman, Nix daemon, desktop bus|sockets denied; Docker and Nix daemon sockets reach the whole machine|`Socket` grant (ssh and gpg agents); brokers only `Unconfined`|
|GUI apps, `open`, browsers, AppleScript, clipboard, Keychain|denied (R§5.1 probes)|`Unconfined`|
|local servers and tests binding ports|loopback works on macOS and tier N; L1-L3 need `Serve{Any, c}`|tier N|
|debuggers attaching to other processes|denied outside the run|`Unconfined`|
|a long-lived kernel after a grant change|keeps its start profile|restart (C21)|

Migration:

1. Phase 1 confines checks and non-interactive runs. In interactive runs,
   steps that declare no network (the shell's effect classes) run
   confined; steps that declare it run under the shipped `Unconfined`, as
   today.
2. A confined program that hits a denial returns its output with the
   denied access and the grant that would allow it; the agent may ask for
   the step again unconfined. That is a new ruled effect, counted; no run is
   relaunched on its own (va6).
3. Interactive network steps become confined (per-host grants for
   configured registries) once the measured denial rate on recorded
   sessions is under the threshold the owner sets.

## 12. Phases and effort

Estimates are engineer-weeks [INFERENCE: from the size of comparable laws
and Rust in this repository, not measured].

|Phase|Content|Removes the qualifier for|Effort|
|---|---|---|---|
|0|State relocation: sockets to `~/.eukhe/run/`, copies and snapshots to a work root; the state list in one place; project trust bound to a digest; checks on a copy (copy-on-write clone, R§3.4)|nothing yet|2|
|1|Core and laws of §6 but `proxy_connect_is_send`; launcher; Seatbelt and Landlock+seccomp renderers; `NoNet` and direct `SendAny` only; record, report and pre-loss notice; escape list v1 with disclosure ingestion (C19); probe suite; cost figures; a first escape-rate and recall measurement per mechanism (C25), referenced by every report that relies on confinement|runs whose programs need no network, on macOS and tiers L1-L2: checks, autoresearch and loop runs, interactive edit-build-test sessions|9|
|2|Proxy with per-run port and token; per-host `Send`; `SendAny` through the proxy; tier N (own launcher, bubblewrap ≥ 0.12 as fallback); `Socket` grants|runs that fetch only from granted hosts|5|
|3|Interactive network steps confined; cache policy; long-lived program restart on grant change; cgroup limits where delegated|interactive sessions with package installs from granted registries|3|
|4|Red-team harness at full size, closure seeds, side-channel measurement, publication per release (C25)|— (measures)|2, then per release|

## 13. Decisions for the owner

1. Same OS user: sr179 counts a program run "sharing the core's OS identity"
   as able to break isolation. Every confined run here shares the user's
   uid, held off state by the mechanism. Read sr179 as "unconfined, or
   confined yet able to reach the core's files, credentials, sockets or
   processes", or require a separate uid (needs root at install).
2. Linux floor for "confined and isolated": tier L1, L2 or N (§5); L3 runs
   confined but not isolated.
3. Daemon and worker IPC on Linux: pathname sockets under `~/.eukhe/run/`
   (scoped by ABI 9, seccomp `AF_UNIX` denial or a mount namespace), or
   abstract sockets with peer-credential checks on both ends (scoped from
   ABI 6).
4. User namespaces when the system allows them (per-host network and PID
   isolation on Linux), with Eukhe's own launcher or bubblewrap ≥ 0.12.
5. Caches: shipped write grant on known cache dirs, caches redirected into
   a per-project dir, or read-only.
6. Interactive default per §11 migration steps 1-3, and the denial-rate
   threshold for step 3.
7. Escape list policy: an instance counts when it bypasses the mechanism
   from the shipped profile with an advisory or reproducer; a distribution
   kernel counts as fixed by version, or by a passing probe reported as
   measured.
8. Law changes in `SPEC.md` §4: `profile_within_allowed` becomes
   `profile_fs_within`, `profile_fs_covers` and `profile_net_exact`;
   `run_unconfined_needed` becomes `unconfined_only_by_grant`;
   `run_unconfined_not_default_not_passed` becomes
   `unconfined_not_unattended_not_passed` (the interactive default holds
   `Unconfined`: sr51, sr73, decision D3 3a). C9 and C11 text replaced by
   §2.
9. Subagents of interactive runs: keep the current law (no spawn passes
   `Unconfined`; their programs run confined or are refused), or let the
   root's grant apply to them, which changes that law.
10. Deferred execution files: listed in the report (§8), or denied on
    macOS and tier N (Landlock cannot carve them out of a project write
    grant without blocking new entries in the project root and `.git`).
11. New dependencies: a Landlock crate and a seccomp crate with safe APIs;
    `/usr/bin/sandbox-exec` on macOS (marked deprecated in its man page,
    no replacement for command-line programs, R§1.1).
12. Windows: unsupported.
