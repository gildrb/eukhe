# security (spec): confinement research

Appendix to `spec/security/CONFINEMENT.md`. Sources read 2026-11-13.
Measurements in §5 are this design's own; the rest cites primary sources
or code at a pinned commit. Unconfirmed items are marked.

## 1. macOS

### 1.1 Seatbelt

- `/usr/bin/sandbox-exec` ships on macOS 27.3 (build 26C5035r, file dated
  2026-10-31); its man page heads "execute within a sandbox (DEPRECATED)"
  and points to App Sandbox (`/usr/share/man/man1/sandbox-exec.1`,
  observed). `sandbox_init` in `<sandbox.h>` is deprecated since 10.8.
  Apple publishes no removal date and no replacement for confining
  command-line programs:
  <https://github.com/apple/containerization/issues/737> (open).
- Profile language (SBPL): `(deny default)`, then `allow`/`deny` rules on
  operations (`file-read*`, `file-write*`, `process-exec`,
  `process-fork`, `mach-lookup`, `network-outbound`, `network-bind`,
  `signal`, `process-info*`, `sysctl-read`, `iokit-open`,
  `system-fcntl`); later rules win; parameters via `-D KEY=value` and
  `(param "KEY")`. Community reference of private API and operations:
  <https://github.com/mkke/seatbelt>; Chromium's use of the private
  compile and apply calls:
  <https://chromium.googlesource.com/chromium/src/+/main/sandbox/mac/seatbelt.cc>.
- Network filters accept only `localhost` or `*` as host
  (`remote ip "localhost:PORT"`); no per-address or per-name egress. The
  `localhost` filter does not match `::ffff:127.0.0.1`, which breaks
  dual-stack JVM sockets (reported by CLI B, §3.2; unconfirmed here).
- Unix sockets are filtered by path:
  `(remote unix-socket (path-literal …))` or `(subpath …)` (CLI A, §3.1).

### 1.2 Nesting

- A Seatbelt profile cannot be applied inside a process already under a
  deny-default profile: reproduced on macOS 27.3,
  `sandbox-exec -p '(version 1)(deny default)(allow process-exec)…' sandbox-exec -p '(version 1)(allow default)' true`
  prints `sandbox_apply: Operation not permitted`, exit 71. Under an
  allow-default outer profile the inner one applies (exit 0).

### 1.3 App Sandbox and Endpoint Security

- App Sandbox needs the `com.apple.security.app-sandbox` entitlement in a
  signed binary; it is applied before `main`; children created by fork
  inherit it, programs launched through LaunchServices do not
  (<https://jhftss.github.io/A-New-Era-of-macOS-Sandbox-Escapes/>). It
  cannot be put on arbitrary command-line programs an agent runs.
- Endpoint Security: AUTH events (exec, open, signal, XPC connect) can
  deny before the action; ships as a system extension with the
  `com.apple.developer.endpoint-security.client` entitlement, granted by
  Apple on request
  (<https://developer.apple.com/documentation/endpointsecurity>,
  <https://developer.apple.com/documentation/bundleresources/entitlements/com.apple.developer.endpoint-security.client>).
  A missed AUTH deadline kills the client by default. Not usable by an
  unsigned user-level install; system-wide, not per-program profiles.

## 2. Linux

### 2.1 Landlock ABI

Sources: <https://wiki.gnoack.org/LandlockAbiVersioning>;
<https://docs.kernel.org/userspace-api/landlock.html> (ABI 9
`LANDLOCK_ACCESS_FS_RESOLVE_UNIX`, ABI 10 UDP, ABI 11 no_new_privs flag
confirmed in the text); <https://landlock.io/talks/2026-10-08_landlock-lss.pdf>.

|ABI|Kernel|Adds|
|---|---|---|
|1|5.13|file rights (execute, read, write, read dir, remove, make)|
|2|5.19|`REFER` (rename and link across directories)|
|3|6.2|`TRUNCATE`|
|4|6.7|TCP bind and connect, by port only|
|5|6.10|`IOCTL_DEV`|
|6|6.12|scoped abstract Unix sockets and signals|
|7|6.15|audit logging of denials|
|8|7.0|`TSYNC` (all threads)|
|9|7.1|connect to pathname Unix sockets, by path|
|10|7.2|UDP bind, connect and send, by port|
|11|7.3|no_new_privs set by `landlock_restrict_self`|

- Allow-only: a rule adds access beneath a path; no rule can remove access
  inside an allowed tree. Rules are bound to the inode the path resolves
  to when the rule is added, links followed.
- Not covered (kernel doc, "Current limitations" and "Filesystem flags"):
  socket creation by family; `chroot`; descriptors opened before
  enforcement (inherited terminals); at most 16 stacked layers; path
  lookup; `chdir`, `stat`, `flock`, `chmod`, `chown`, `setxattr`, `utime`,
  `fcntl` and `access` ("It is currently not possible to restrict some
  file-related actions accessible through these syscall families"), so
  a program changes the mode, times and extended attributes of any file it
  owns and can name. Ptrace is limited to the same or a nested domain in
  every ABI; the ABI 6 signal scope covers sending signals, not
  `prlimit64`, `setpriority`, `sched_setaffinity`, `sched_setscheduler` or
  `ioprio_set` on another process of the same user.
- The TCP connect right is checked only in the `connect` hook: TCP Fast
  Open (`sendto` with `MSG_FASTOPEN` on a fresh stream socket) connects
  without it (§4).
- `file_getattr` and `file_setattr` (Linux 6.17) read and set inode flags
  (`FS_XFLAG_NOATIME` among them) by path, and `inotify_add_watch`
  reports entry names in a watched directory; Landlock has no right for
  either, so they follow the "not covered" list above.
- Landlock's scopes are abstract Unix sockets and signals only (kernel
  doc, "IPC scoping"): SysV IPC, POSIX message queues and
  `/proc/<pid>/cmdline` of other processes of the same user stay
  reachable between sandboxed programs.
- Mount namespaces: since Linux 3.18 a file or directory that is a mount
  point only in another namespace can be renamed or unlinked, and the
  mount disappears there (mount_namespaces(7)); a file-level bind over a
  path the host replaces by rename stops covering it.
- `listen` on a socket that was never bound picks an ephemeral port
  without the bind hook, so a TCP bind rule does not stop a program from
  accepting connections (<https://wiki.gnoack.org/LandlockTcpPortControl>,
  "Known issues": "listen(2) without bind(2) also works").
- Errata are queryable (`LANDLOCK_CREATE_RULESET_ERRATA`). Erratum 1: TCP
  rights used to restrict other IPv4 and IPv6 stream protocols (SMC, MPTCP,
  SCTP); since the fix only TCP sockets are subject to them, so a sandbox
  that relies on TCP rights alone leaves those protocols open. Erratum 3:
  disconnected directories (same description as CVE-2025-68736; mapping
  inferred). Erratum 4: whiteout creation.
  (Kernel doc, "Errata"; <https://landlock.io/news/5/>.)

### 2.2 Distribution kernels

- Landlock in the default LSM list: Ubuntu, Debian, Arch, SUSE; not in
  Fedora and RHEL's default list
  (<https://bugs.launchpad.net/ubuntu/+source/linux/+bug/2166235>);
  RHEL 9.6 enables it with ABI 5 backported
  (<https://landlock.io/news/5/>); on by default in WSL2
  (<https://landlock.io/news/3/>). Fedora reports conflict: unconfirmed.
- ABI by release follows from the kernel: Ubuntu 22.04 (5.15) ABI 1, 24.04
  GA (6.8) ABI 4, Debian 12 (6.1) ABI 2, Debian 13 (6.12) ABI 6
  [kernel versions unconfirmed from a primary source].
- Observed: NixOS 26.05, kernel 6.18.50: LSM list
  `capability,landlock,yama,bpf,ima`, Landlock ABI 7.

### 2.3 User namespaces and bubblewrap

- Ubuntu 23.10 added AppArmor restriction of unprivileged user namespaces;
  24.04 enables it: namespaces need an AppArmor profile with `userns`
  (<https://ubuntu.com/blog/ubuntu-23-10-restricted-unprivileged-user-namespaces>).
  Bubblewrap from the archive then fails with "setting up uid map:
  Permission denied" (<https://bugs.launchpad.net/ubuntu/+source/bubblewrap/+bug/2069526>).
  Three bypasses of the restriction were published
  (<https://www.openwall.com/lists/oss-security/2025/03/27/6>).
- Debian ≥ 11, RHEL ≥ 8 and Arch allow unprivileged user namespaces by
  default (<https://github.com/flatpak/flatpak/wiki/User-namespace-requirements>).
- Rationale for restricting them: Google reported that 44% of kCTF exploits
  needed unprivileged user namespaces, and 60% of kCTF submissions used
  io_uring (<https://security.googleblog.com/2023/06/learnings-from-kctf-vrps-42-linux.html>).
  Namespaces add kernel attack surface to the confined program.

### 2.4 seccomp

- A filter must check `seccomp_data.arch`; on x86-64 the x32 ABI shares
  `AUDIT_ARCH_X86_64`, so a deny list must also cover numbers with
  `__X32_SYSCALL_BIT` (<https://man7.org/linux/man-pages/man2/seccomp.2.html>,
  <https://docs.kernel.org/userspace-api/seccomp_filter.html>).
- BPF cannot dereference pointers: no filtering by path or socket address.
- io_uring submits operations without a syscall each; filters see only
  `io_uring_setup` and `io_uring_enter`; Docker's default profile blocks
  them (<https://github.com/moby/moby/pull/46762>).
- `SECCOMP_RET_USER_NOTIF` "must not be used to make security policy
  decisions": arguments can change after the check
  (<https://man7.org/linux/man-pages/man2/seccomp_unotify.2.html>).

### 2.5 Resource limits

- cgroup v2: by default only `memory` and `pids` are delegated to users;
  `cpu` and `io` need a `user@.service` drop-in
  (<https://rootlesscontaine.rs/getting-started/common/cgroup2/>,
  <https://systemd.io/CGROUP_DELEGATION/>).
- macOS: `setrlimit` per process; no limit over a process tree (Apple
  containerization issue above).

## 3. Coding-agent command-line tools

Four open-source coding-agent CLIs, read at their default branches on
2026-11-12 and 2026-11-13. Repository names, commits and file positions
are kept with the design's working notes, outside this repository.

### 3.1 CLI A (Rust)

- macOS: `/usr/bin/sandbox-exec -p <profile>` by absolute path, every path
  a `-D` parameter, never spliced into the profile text. Base
  `(deny default)`, signals and `process-info*` limited to the same
  sandbox, `mach-lookup` limited to named services, all XPC denied.
- Writes: per writable root, exclusions for its own config dir and `.git`;
  a `literal` deny as well as `subpath`, because `mkdir` of the excluded
  name slipped past `subpath` alone; unlink of each root and of ancestors
  of read-only paths denied.
- `(deny system-fcntl (fcntl-command 80 110))`: `F_MAKECOMPRESSED` (80) and
  `F_TRANSFEREXTENTS` (110) change files through read-only descriptors and
  pass `file-write*`. 110 is in the SDK's `sys/fcntl.h`; 80 is not in the
  public header (its value as CLI A states it).
- Its daemon socket directory is denied for read, write and connect after
  every grant.
- Linux: bubblewrap (first on `PATH` outside the cwd, else a vendored
  build) with user, PID, IPC and, without network, network namespaces;
  `--ro-bind / /`, `--bind` for writable roots, read-only binds and tmpfs
  over protected paths. Landlock (ABI 5, best effort) is a legacy path,
  refused for restricted policies because it cannot isolate its daemon's
  Unix sockets.
- seccomp (default allow): every rule also with the x32 bit; `io_uring_*`
  denied in every mode (it creates sockets without `socket()`); without
  network, `socket` and `socketpair` only for `AF_UNIX`, connect, bind and
  listen denied; `ptrace`, `process_vm_*`, `request_key` denied.
- Network grants: the program reaches only a loopback listener inside its
  namespace; a host-side bridge forwards to the proxy, which decides per
  host.
- Denials are detected by keywords in the output; its code calls this
  non-deterministic. After a denial, a retry without the sandbox follows
  an approval.

### 3.2 CLI B (TypeScript)

- macOS: deny-default profile tagged per session; reads allowed everywhere
  then a deny list; writes an allow list with mandatory denies
  (`.git/hooks`, `.git/config`, shell start-up files, editor task dirs)
  found at any depth; rename and unlink of denied paths and their
  ancestors denied, so `mv .env x; cat x` fails. Denials read from
  `log stream` filtered by the tag.
- Linux: bubblewrap with a new network namespace; the host proxy is reached
  through a Unix socket bound into the sandbox and a TCP listener inside;
  seccomp denies `socket(AF_UNIX)` (32-bit masked compare), `AF_VSOCK`,
  `io_uring_*`, and namespace and mount calls; `socketpair` allowed;
  inherited descriptors stay usable. Without bubblewrap it refuses to run.
- Proxy: per-session token on every request; deny list before allow list;
  `*.example.com` matches strict subdomains only; host names canonicalised
  so `2852039166` or `127.1` cannot dodge a deny; resolve once and dial the
  checked address; loopback, link-local and metadata addresses refused.
- Stated limits: allowing a host allows anything that host accepts
  (pushing to any repository on an allowed code host); domain fronting may
  pass; a Docker socket grant escapes; broad write grants on `PATH` dirs or
  start-up files escape later.

### 3.3 CLI C (TypeScript)

- macOS: per command, a temporary profile file, `(deny default)` with
  `(import "system.sb")`; network all or nothing.
- Linux: bubblewrap required, all namespaces new, the network shared when
  network is on; secret files found with `find -maxdepth 3` and masked at
  start.
- seccomp: seven instructions, kill on foreign arch, `EPERM` for `ptrace`;
  the x32 bit is not checked, so on a kernel with `CONFIG_X86_X32_ABI` the
  x32 `ptrace` number passes [inference from its code and the kernel doc].
- Denial detection is a keyword heuristic; a denial proposes a widened
  grant for approval.

### 3.4 CLI D (reference harness)

- No operating-system confinement of programs: no Seatbelt, Landlock,
  seccomp or namespace code.
- Copy-on-write work copies for subagents: APFS `clonefile(2)`, btrfs and
  ZFS snapshots, `FICLONE` reflinks, overlayfs with a fuse-overlayfs
  fallback, and a copy or `git worktree` fallback; changes return as a
  patch or a branch. A copy, not a security boundary. Its `clonefile`,
  `FICLONE` and plain copy are used here for check copies (C20); its
  `git worktree` fallback is not, since `git` runs hooks and configured
  commands from a tree an agent can write.
- Expects an embedding host to impose Seatbelt or an LSM, and routes a
  denied write to that host.

### 3.5 What the design takes from them

- Paths as Seatbelt parameters; `literal` plus `subpath` exclusions;
  `fcntl` 80 and 110 denied; XPC denied; daemon sockets denied after every
  grant; unlink of ancestors of protected parts denied.
- seccomp with the x32 bit, `io_uring` denied, `AF_UNIX` socket creation
  denied where sockets are not otherwise scoped, `socketpair` kept.
- Network only through a proxy that decides per host, resolves once, and
  refuses private addresses; a per-run token.
- Write denies on deferred execution files inside a write grant (CLI B),
  on macOS and with namespaces only; on Landlock alone they are listed
  instead (`CONFINEMENT.md` decision 10).
- Not taken: a retry after a denial by approval of a wider sandbox for the
  same command (va6: a run is not relaunched on its own); denial keyword
  heuristics as fact (here: measured); bubblewrap as a dependency (Eukhe's
  own launcher sets up namespaces, decision 4).

## 4. Escape history

|Mechanism|Instance|Class|Fixed|Source|
|---|---|---|---|---|
|App Sandbox, Seatbelt|CVE-2023-32364: devfs mount drops quarantine, then a LaunchServices launch|file system, launch|macOS 13.5|<https://nvd.nist.gov/vuln/detail/cve-2023-32364>|
|App Sandbox|CVE-2023-42961, CVE-2024-27864 and others: XPC services in the app's PID domain without client checks|XPC|macOS 14.0, 14.4|<https://jhftss.github.io/A-New-Era-of-macOS-Sandbox-Escapes/>|
|App Sandbox|CVE-2025-31191: security-scoped bookmark forgery via a keychain item|XPC, keychain|macOS 15.4|<https://www.microsoft.com/en-us/security/blog/2025/05/01/analyzing-cve-2025-31191-a-macos-security-scoped-bookmarks-based-sandbox-escape/>|
|App Sandbox|CVE-2025-24277: crash reporter path parsing|service bug|macOS 15.4, 14.7.5, 13.7.5|<https://www.iru.com/blog/crashone-cve-2025-24277-macos-sandbox-escape>|
|Seatbelt|`F_MAKECOMPRESSED`, `F_TRANSFEREXTENTS` write through read-only descriptors|fcntl|deny rule in profile|CLI A, §3.1|
|Landlock|CVE-2025-68736: disconnected directories through bind mounts widen rights on rename|logic|kernel fix; versions to record from the stable tree|<https://cveawg.mitre.org/api/cve/CVE-2025-68736>|
|Landlock|CVE-2026-72183: signal scope bypassed through `SIGIO`|logic|kernel fix; versions to record from the stable tree|<https://cveawg.mitre.org/api/cve/CVE-2026-72183>|
|bubblewrap|CVE-2017-5226: `TIOCSTI` into the parent's terminal|terminal|`setsid`; kernel 6.2 `legacy_tiocsti`|<https://nvd.nist.gov/vuln/detail/CVE-2017-5226>|
|bubblewrap|CVE-2026-41163: setuid mode, ptrace during set-up|set-up|0.11.2|<https://cveawg.mitre.org/api/cve/CVE-2026-41163>|
|bubblewrap|CVE-2026-87766: set-up follows a parent symlink onto the host via `/oldroot`|set-up|0.12.0|<https://cveawg.mitre.org/api/cve/CVE-2026-87766>|
|Landlock|TCP Fast Open: `sendto` with `MSG_FASTOPEN` on a fresh stream socket connects without the `socket_connect` hook, every port, ABI ≥ 4 (reproduced by the reporter on 7.0.11; MPTCP fast open alike by source reading)|logic, network|denied by a seccomp rule on the flag in the shipped profile; kernel fix versions to record from the stable tree|<https://lkml.iu.edu/2606.2/01737.html>|
|seccomp filters|x32 numbers pass an x86-64 deny list|construction|filter rule|seccomp(2)|

- Apple's notes for macOS 15.4 list 8 entries describing an app able to
  break out of its sandbox (<https://support.apple.com/en-us/122373>); for
  macOS 27, 12 (<https://support.apple.com/en-us/149035>); counts from the
  notes' wording. Whether each
  is reachable from a deny-default profile with XPC denied is decided per
  instance (`CONFINEMENT.md` decision 7).
- The observed server runs bubblewrap 0.11.2, affected by CVE-2026-87766
  when binding trees a sandboxed program can write.

## 5. Measurements

### 5.1 macOS (Apple M4, macOS 27.3)

Script: a deny-default profile with reads everywhere except a state
directory, writes to a work dir, per-user temp and cache dirs and
`/private/tmp`, no network, `mach-lookup` for libinfo, dirhelper and
FSEvents; probes, then timings.

|Probe inside the profile|Result|
|---|---|
|read a canary in the state dir|`Operation not permitted`|
|write in the state dir; write in `$HOME` outside the work dir|`Operation not permitted`|
|`curl https://example.com`|"Could not resolve host"|
|`kill -0` on the parent|`Operation not permitted`|
|`open -a TextEdit` (LaunchServices)|"Unable to find application"|
|`osascript` to Finder (Apple Events)|"Connection invalid"|
|write in the work dir; `git status` in a repository|works|

|Timing|Unconfined|Confined|
|---|---|---|
|start `/usr/bin/true` (N = 300)|1.70 ms|8.32 ms|
|`git ls-files -s` in a checkout of 10,287 files (mean of 20)|7.3 ms|14.0 ms|
|`grep -r` over the same tree (mean of 5, warm)|875 ms|882 ms|

- A profile without dirhelper and per-user temp dirs broke `/usr/bin/git`
  (an Xcode shim): `confstr` could not get `DARWIN_USER_TEMP_DIR`, `xcrun`
  could not write its cache, and each call took 2.2 s instead of 17 ms.
- Under `(deny default)` with `file-write*` allowed on two directories and
  `(allow network-bind (local unix-socket (subpath a)))` on one, a Python
  `bind` and `listen` of a pathname socket worked in `a` and failed with
  `EPERM` in the other: Seatbelt checks a Unix socket bind as
  `network-bind` on its path, apart from the file write.
- With `xcrun_db` set to a file in another directory, `/usr/bin/git
  --version` wrote its cache there (a 1,089-byte file).
- Hard links under `(deny default)` with `file-read*` everywhere but a
  state directory and `file-write*` on one directory `t`: `ln t/a t/b`
  worked; `ln` of a file outside `t` into `t` failed with `EPERM`, and so
  did `ln` of a state file into `t`, with or without `(allow file-link)`.
- A symlink inside a write tree `w` pointing at a directory outside it:
  under `(allow file-write* (subpath w))`, writing `w/link/f` failed with
  `EPERM`; Seatbelt matched the path the access resolved to.
- Under `(allow network-outbound (remote tcp "localhost:9999"))` and
  `(allow network-bind network-inbound (local tcp "localhost:*"))`, a TCP
  connect to `127.0.0.1:9999` reached the network stack (refused, no
  listener), while a UDP `sendto` to that port and a UDP bind on loopback
  failed with `EPERM`: the `tcp` filters exclude UDP, which `ip` filters
  admit.
- A Unix socket bound and listening in an allowed directory `d` could be
  renamed and hard-linked into another write tree under `file-write*`;
  with `(deny file-write-create (require-all (vnode-type SOCKET)
  (require-not (subpath d))))` both failed with `EPERM`, while renaming
  and linking regular files there still worked.
- The measured profile above allowed `mach-lookup` of FSEvents; the design
  now omits it, since fseventsd is reported to deliver changes by path to
  a subscriber whatever its sandbox allows [unconfirmed from a primary
  source: a 2019 report on Apple's filesystem-dev list]; a probe in the
  suite checks that a confined program gets no FSEvents stream at all.
- `kern.procargs2` (`sysctl` with `CTL_KERN`, `KERN_PROCARGS2`, pid) on a
  same-user Node process started with `SBXSECRET=hunter2`: a program under
  `(deny default)` read its environment, with `(allow sysctl-read)`, with
  `sysctl-read` limited to five names, with no `sysctl-read` rule at all,
  and with no `process-info*` rule, while the same profile denied a file
  write. Apple's own `/bin/sleep` returned no environment, confined or
  not. No Seatbelt rule tried here filters the call.

### 5.2 Linux (AMD Ryzen 7 5800X, NixOS 26.05, kernel 6.18.50, Landlock ABI 7, bubblewrap 0.11.2)

Script: a Landlock ruleset with read rules on every top-level directory but
the one holding the home directory, and on every home child but a state
directory; write on a work dir; TCP handled with no rule; signals and
abstract sockets scoped.

|Probe|Result|
|---|---|
|read the state canary, first run|**allowed**: a home child `.home -> /home/<user>` was a link; the rule followed it and opened the whole home directory, the state dir included|
|read the state canary, links skipped|denied|
|write outside the work dir|denied|
|TCP connect to 1.1.1.1:443|denied|
|signal the unconfined parent|denied (ABI 6 scope)|
|connect to a pathname Unix socket in the state dir|**allowed** (ABI 7; covered from ABI 9)|

|Timing|Unconfined|Confined|
|---|---|---|
|start `true` (N = 300)|1.1 ms|6.0 ms (bubblewrap, all namespaces)|
|`git ls-files -s` (mean of 20)|4.8 ms|10.0 ms (bubblewrap)|
|building and enforcing 69 Landlock rules (Python, `ctypes`)|—|1.0 ms|

- Both findings in bold are requirement laws in `CONFINEMENT.md` §6:
  `profile_fs_within` (rules on real paths, links not followed) and
  `profile_sockets_exact`.

### 5.3 Published figures

- Process start, Ryzen 2700X, NixOS: plain 0.653 ms, bubblewrap 2.171 ms,
  bubblewrap with namespaces 2.903 ms, `sh -c` 3.670 ms
  (<https://tech.kmicklas.com/posts/benchmarking-linux-sandboxing/>,
  2023-10-22).
- seccomp: about 600 ns per call path for one or two bitmapped filters
  (<https://regressions.linaro.org/lkft/linux-next-master/next-20250905/kselftest-seccomp/seccomp_seccomp_bpf>);
  allow-only syscalls cost O(1) since 5.11.
- bubblewrap set-up grows with the square of the number of `--bind`
  arguments (<https://github.com/containers/bubblewrap/issues/384>).
- No published Landlock or Seatbelt per-call cost found.

## 6. Network per host

- Seatbelt: loopback ports only; Landlock: ports only. Per-host control
  needs a proxy that the program cannot bypass: on macOS, a loopback port
  is the only egress; on Linux, an empty network namespace with a bridge
  to the proxy (§3.1, §3.2).
- A CONNECT proxy sees the requested name and the TLS server name, never
  the content. Domain fronting
  (<https://www.petsymposium.org/popets/2015/popets-2015-0009.pdf>) and
  Encrypted Client Hello (RFC 9849, March 2026,
  <https://www.rfc-editor.org/rfc/rfc9849>) mean a grant to a host covers
  whatever that host relays.
- DNS rebinding: resolve once in the proxy, check the address, dial it.
  The refused set names `0.0.0.0/8`, `::` and IPv4-mapped addresses as
  well as loopback and private ranges, since dialling `0.0.0.0` or
  `::ffff:127.0.0.1` reaches this machine's services.
- Programs that ignore proxy variables get no network: they fail closed.

## 7. Threat model triage

### 7.1 Covert channel measurements

Single runs on 2026-11-14; each states one host's behaviour, not a rate.

- File locks, macOS 27.3 (Apple M4): a Python process under
  `(deny default)` with `process-exec`, `process-fork`, `file-read*` and
  `sysctl-read` opened a file read-only and took `LOCK_EX` with `flock`;
  an unconfined process's `LOCK_EX | LOCK_NB` on the same file failed with
  `EWOULDBLOCK` (errno 35) while it held the lock.
- Access times, Linux 6.18.50 (NixOS): a file with an access time two days
  old and a modification time three days old, read once with `cat`: on a
  `relatime` tmpfs (`$XDG_RUNTIME_DIR`) and on `/dev/shm` the access time
  became the read time; on the home and `/tmp` btrfs mounts (`noatime`) it
  did not change. macOS 27.3, APFS data volume: the same read left the
  access time unchanged.
- Abstract names, Linux 6.18.50: `/proc/net/unix` and `/proc/net/tcp` are
  mode 0444; `/proc/net/unix` listed 23 abstract names (entries starting
  with `@`). Not repeated under Landlock.
- inotify across binds and FSEvents paths: reported by reviews (rounds 11
  and 13), not measured here.

### 7.2 Rounds 6 to 14 against the threat model

Each gap the blind reviews of rounds 6 to 14 reported, classed by the
guarantee of `CONFINEMENT.md` §2 it broke. A covert channel breaks none;
it is listed under §2's limits with the evidence of §7.1. Totals: 50
broke a guarantee and are fixed; 5 are covert channels, now limits (their
narrowings stay); 1 was measured not to hold; 1 broke no guarantee.

|Round|Gap|Finding|Guarantee|Disposition|
|---|---|---|---|---|
|6|1|Descriptor-form metadata changes in check and unattended profiles on Landlock tiers|G1|fixed: denied there|
|6|2|Re-establishment trusts files an unconfined program could rewrite|G6|fixed: verified launch, head-digest check|
|6|3|Loopback service ports squatted on the other address|G5|fixed: fixed ports held on both addresses, unbindable|
|6|4|Abstract daemon name squatted, pid check defeated by pid reuse|G5|fixed: random name per start, server secret|
|6|5|Credentials denied only for reading|G2, G4|fixed: every access denied|
|6|6|Seatbelt hard link from outside a write tree into it|G2|measured not to hold (R§5.1); no change|
|6|7|"highest mark" missed live programs|G6|fixed|
|6|8|Deferred execution files shown only after the TUI shell ran them|G4|fixed: shown before each TUI command|
|7|1|Inode flag ioctls outside every grant on Landlock tiers|G1|fixed: denied by seccomp|
|7|2|Loopback TCP between confined programs carried marked data|G3|fixed: mark channel|
|7|3|Trusted-base helpers resolved from a write reach|G4, G5|fixed: clean PATH, helpers are state|
|7|4|Deferred execution files noticed too late|G4|fixed; other terminals stated as a limit|
|7|5|`unconfined_only_by_grant` allowed no refusal by cause|G6|fixed|
|7|6|Re-establishment binary substitution|G6|fixed: Team-ID check, `env -i` start|
|7|7|Software delegates missing from state|G4, G5|fixed|
|8|1|Symlink swap between listing and Landlock rule|G1, G2|fixed: rules on `openat2` descriptors checked against the listing|
|8|2|Script helpers load code from interpreter load directories|G4|fixed: isolation flags, refusal|
|8|3|Escape instances matched by version across release branches|G6|fixed: per-branch introducing version, probes everywhere|
|8|4|macOS loopback bind missing from the mark-rise stop|G3|fixed|
|8|5|Entries named like Eukhe executables on `PATH`|G5|fixed: deny set|
|8|6|Bare repository layouts in write trees|G4|fixed: listed|
|8|7|Access times of read files as a channel from a held-out check|covert|limit; narrowed by tier N read-only binds|
|8|8|Abstract daemon name visible in `/proc/net/unix`|covert (visibility); G5 (squat)|limit for visibility; squat closed by the handshake|
|9|1|macOS `ip` filters admit UDP to proxy and loopback ports|G3|fixed: `tcp` filters (measured)|
|9|2|Socket bound in the private temp dir renamed into a write tree|G5|fixed: vnode-type deny (measured)|
|9|3|gpg-agent honours a caller's terminal options|G5|fixed: probe condition|
|9|4|Check tools and closure parts writable by agent programs|G4, G6|fixed: copied by digest, state|
|9|5|Held-out source path readable|G2|fixed: state from when a contract names it|
|9|6|Held-out check with a send grant|G2, G3|fixed: `NoNet`|
|9|7|NAT64 prefixes bypass the refused-address list|G3|fixed|
|9|8|§9 and C19 disagreed on affected hosts|G6|fixed|
|10|1|Crash handler writes program-chosen data outside every profile|G1, G2|fixed: stores are state, `RLIMIT_CORE` 0|
|10|2|File poisoned before it becomes a credential state part|G4|fixed: commands confirmed, digest bound|
|10|3|gpg-agent and ssh-agent exceptions reach the principal channel|G2, G5|fixed: extra socket under probe; ssh confirm prompt stated as a limit|
|10|4|Abstract names and bound ports as a channel between runs on L1|covert|limit|
|10|5|Held-out check exclusive window undefined for live programs|G2, G6|fixed: start stops every live program|
|10|6|Decisions 6 and 13 stall unattended runs unstated|G6|fixed: stated in §7, §11, C24|
|11|1|Loopback endpoints of the trusted base and delegates taken over|G5|fixed: unbindable ports|
|11|2|FSEvents reports file names whatever the sandbox|covert|limit; narrowed: no profile reaches FSEvents|
|11|3|Proxy allowed on-link addresses|G3|fixed|
|12|1|Ephemeral-range endpoint taken by a port-0 bind|G5|fixed|
|12|2|Path that becomes state stays reachable to a live program|G2|fixed: live programs stopped first|
|12|3|Proxy could resolve a refused name|G3|fixed: decided before lookup|
|12|4|Control sequences in program output on the TUI|G5|fixed: escaped|
|12|5|Private temp dir inside a copy other programs write|G1, G4|fixed: in the work root|
|13|1|`kern.procargs2` exposes argv and environment on macOS|G2, G3|fixed: no credential in argv or environment; mark channel|
|13|2|File locks and inotify access events between runs|covert|limit; narrowed: held-out check runs alone|
|13|3|Datagram `socketpair` sends to any pathname socket|G1, G5|fixed: stream and seqpacket only|
|13|4|Abstract endpoints of delegates and helper agents squatted|G5|fixed: proof of a secret|
|14|1|Loader variables reach the launcher before any rule|G1, G2|fixed: fixed launcher environment|
|14|2|Environment-supplied provider credential readable through `kern.procargs2`|G2|fixed: re-exec without it; loss on macOS|
|14|3|Held-out check stores content in an agent with `PUTVAL`|G2|fixed: no `Socket` grant|
|14|4|No law bound `not_isolated`|G6|fixed|
|14|5|L3 signal scope contradicted C9|G6|fixed: platform fact with a loss|
|14|6|Dashboard renders program output|G5, G3|fixed: escaped, no outside resource|
|14|7|POSIX shared memory namespace uncounted|G1|fixed: shared write under tm8|
|14|8|Tools that apply their own Seatbelt profile missing from §11|none (usability)|not a gap under the rubric; the row stays|

### 7.3 Review rubric from round 15

A gap is a concrete way to violate one of the guarantees G1 to G6 of
`CONFINEMENT.md` §2 as the design is written: the steps a program takes
(or a builder takes following the text), the platform and tier, and the
guarantee that fails. A mechanism fact the design gets wrong, a law that
admits the violating program, and a contradiction a builder must resolve
in a way that breaks a guarantee are gaps when shown by such steps. Covert
and side channels between processes of the same user, and every other
limit §2 states, are not gaps; neither are kernel or hardware isolation
beyond tier N's namespaces, wording, usability or migration cost, unless
the design claims something false about them (G6). Each round's reviewer
is fresh and sees only the design, its appendix and the cited philosophy.
The reviews stop after two rounds in a row report no gap under this
rubric.

### 7.4 Rounds under the rubric

|Round|Gaps|Guarantees|Closed by|
|---|---|---|---|
|15|3|G4, G1, G4|auto-start locations defined as files run with no principal command, D-Bus session services and user-tmpfiles.d listed; an audited `ioctl` list on tiers without a mount namespace (btrfs subvolume and fscrypt commands); helpers and delegate executables in any past write reach need the principal's digest acceptance|
|16|3|G3, G5, G4|no profile reaches `trustd`, whose AIA, OCSP and CRL fetches leave the proxy; G5 narrowed to Eukhe, the trusted base and delegates, with the principal's own loopback ports and abstract names a stated exposure (owner decision); acceptance binds every file under a helper's load directories|
