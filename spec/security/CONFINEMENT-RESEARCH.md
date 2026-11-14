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
