# eukhe: the laws of area kernel_local

import Base
import ../bend/kernel_local.bend as KL
import ../bend/ffi_kernel_local.bend as FKL
import ../bend/wire.bend as Wr
import ./base.bend as LawsBase

# ---- kernel_local ----

# LAWS (K1): the kernel environment is local. A session never downloads;
# `eukhe kernel install` is the only download, and it checks every file
# against its hash before the kernel uses it; a missing kernel never
# blocks the other tools; a bootstrap lock candidate never outlives its
# attempt. The setup's plan, the sweep's verdicts and the lock attempt's
# verdict run as bend/kernel_local.bend (`plan`, `keeps`, `attempt` of
# `lock.of`) through the entry bend/ffi_kernel_local.bend; PROOF.bend
# proves the laws (as KernelLocal.<law>) with the lemmas of
# proof/kernel_local/.
#
# Requirements (crates/eukhe-core/src/kernel/bootstrap: setup.rs,
# venv.rs, venv/tests.rs, dir_lock.rs, mod.rs):
# R1 (K1.1): a session (every path but `eukhe kernel install`) never
#   downloads (setup.rs `KernelSetup::Local`).
# R2 (K1.1): `eukhe kernel install` downloads only to rebuild a venv that
#   is missing or not this build's, and then only the Python install and
#   the hash-locked requirements, each checked against its pinned hash; the
#   venv and the runtime always come from local files (venv.rs
#   `venv_build_commands`; venv/tests.rs
#   `venv_builds_only_from_the_hash_locked_runtime_source`).
# R3 (K1.1): the kernel starts only after `uv pip check` of the venv built
#   since the last download, and every setup ends with the kernel started
#   (setup.rs `SetupStep::Build`).
# R4 (K1.1): Rust's plan reader (setup.rs `step_of`, `fetch_of`) reads
#   every plan, as the step the found venv calls for: a current venv starts
#   as it is, a venv with stale skills syncs them, a stale venv is rebuilt.
# R5 (K1.2): a missing kernel never blocks another tool, and the ipython
#   tool answers with the install command. Not modelled in Bend: the Rust
#   test crates/eukhe-core/src/kernel/bootstrap/missing_kernel_tests.rs runs
#   the real session (tested, not proven).
# R6 (K1.3): the sweep answers one verdict per file beside the lock, in
#   order: it removes an attempt's candidate or a stale lock renamed aside
#   whose owner is dead, and keeps a live owner's leftover and every other
#   file (dir_lock.rs `sweep_leftovers`; test
#   `the_lock_verdicts_come_from_the_compiled_core`).
# R7 (K1.3): an attempt holds the lock exactly when it linked its
#   candidate; it waits (busy) while the lock may be in use: its owner
#   lives, or it names no owner and its age is unknown or at most 30 s; it
#   frees a lock whose owner is dead, that vanished, or that names no owner
#   and is older than 30 s (dir_lock.rs `Seen`, `Verdict`; test
#   `the_lock_verdicts_come_from_the_compiled_core`: 30 001 ms frees,
#   30 000 ms waits).
# R8 (K1.3): an attempt's candidate never outlives the attempt: Rust's
#   `Candidate` guard (dir_lock.rs) removes it on every return path (not
#   modelled in Bend); a candidate left by a process that died inside its
#   attempt is a dead owner's leftover, which the sweep removes (R6).
# R9 (K1.4): the entry answers every request Rust writes with the spelled
#   decision, reads nothing else (an answer that is no error form means
#   the input was one request, spelled, whose numbers fit the wire), and
#   every error it answers is the one form `E kernel_local: malformed
#   request`.

# (K1.1) The setup
# ----------------
# Every input is free: any venv found, either setup.

# LAW kernel_session_never_downloads (R1): a session (any path but `eukhe kernel install`) fetches nothing,
# whatever kernel venv it finds
law kernel_session_never_downloads:
  for f: KL.Found
  {KL.acts.fetching(KL.plan(f, KL.Local{})) == False{} : Bool}

# LAW kernel_download_only_on_install (R1): a setup that fetches is `eukhe kernel install`
law kernel_download_only_on_install:
  for f: KL.Found
  for s: KL.Setup
  for fetches: {KL.acts.fetching(KL.plan(f, s)) == True{} : Bool}
  {s == KL.Install{} : KL.Setup}

# LAW kernel_fetch_verified_before_use (R3): every fetch is checked against a pinned hash, and the kernel starts
# only after a check of the venv that came after the last fetch
law kernel_fetch_verified_before_use:
  for f: KL.Found
  for s: KL.Setup
  {KL.acts.verified(KL.plan(f, s), True{}) == True{} : Bool}

# LAW kernel_setup_runs (R3): every setup ends with the kernel started: no setup is a no-op
law kernel_setup_runs:
  for f: KL.Found
  for s: KL.Setup
  {KL.acts.runs(KL.plan(f, s)) == True{} : Bool}

# a venv that must be built again: missing, or its runtime not this build's
def kl_must_build(f: KL.Found) -> Bool:
  match f:
    case KL.Current{}:
      False{}
    case KL.Skills{}:
      False{}
    case KL.Stale{}:
      True{}

# LAW kernel_install_downloads_only_stale (R2): `eukhe kernel install` fetches exactly when the venv it finds
# must be built again (missing or stale); a current venv, or one whose skills
# alone are stale, installs from local files
# EXCLUDES: an install that downloads to sync skills or to start a current
#   venv, an install of a stale venv that builds offline only
law kernel_install_downloads_only_stale:
  for f: KL.Found
  {KL.acts.fetching(KL.plan(f, KL.Install{})) == kl_must_build(f) : Bool}

# How a build command may get its files, as Rust's plan reader reads it
# (setup.rs `Fetch`): local files only (--offline), or a download whose
# every file uv checks against a pinned hash
type KlFetch is Data:
  KlOffline{}
  KlDownload{}

# The step Rust's plan reader makes of a plan (setup.rs `SetupStep`):
# start the kernel as it is; sync the skills; build the venv with four
# commands (the Python install, the venv, the hash-locked requirements,
# the runtime), each getting its files as its KlFetch says
type KlStep is Data:
  KlUse{}
  KlSync{}
  KlBuild{python: KlFetch, venv: KlFetch, reqs: KlFetch, runtime: KlFetch}

# setup.rs `fetch_of`: a build command is local only (Offline) or a
# hash-checked fetch (Fetch{True}); any other action there is no plan
def kl_fetch_of(x: KL.Act) -> Maybe<&2, KlFetch>:
  match x:
    case KL.Fetch{h}:
      match h:
        case True{}:
          Some{KlDownload{}}
        case False{}:
          None{}
    case KL.Offline{}:
      Some{KlOffline{}}
    case KL.Check{}:
      None{}
    case KL.Run{}:
      None{}

def kl_is_run(x: KL.Act) -> Bool:
  match x:
    case KL.Fetch{h}:
      False{}
    case KL.Offline{}:
      False{}
    case KL.Check{}:
      False{}
    case KL.Run{}:
      True{}

def kl_is_check(x: KL.Act) -> Bool:
  match x:
    case KL.Fetch{h}:
      False{}
    case KL.Offline{}:
      False{}
    case KL.Check{}:
      True{}
    case KL.Run{}:
      False{}

def kl_is_offline(x: KL.Act) -> Bool:
  match x:
    case KL.Fetch{h}:
      False{}
    case KL.Offline{}:
      True{}
    case KL.Check{}:
      False{}
    case KL.Run{}:
      False{}

def kl_guard(ok: Bool, m: Maybe<&2, KlStep>) -> Maybe<&2, KlStep>:
  match ok:
    case True{}:
      m
    case False{}:
      None{}

# a build of four commands Rust accepts
def kl_build_of(p: KL.Act, v: KL.Act, r: KL.Act, t: KL.Act) -> Maybe<&2, KlStep>:
  do Maybe<&2, KlStep>:
    fp : KlFetch <- kl_fetch_of(p)
    fv : KlFetch <- kl_fetch_of(v)
    fr : KlFetch <- kl_fetch_of(r)
    ft : KlFetch <- kl_fetch_of(t)
    return KlBuild{fp, fv, fr, ft}

# setup.rs `step_of`, by the plan's length: [Run] is Use, [Offline, Run]
# is SyncSkills, [four build commands, Check, Run] is Build; any other plan
# is "not a plan" (None)
def kl_rust_step.six(p: KL.Act, v: KL.Act, r: KL.Act, t: KL.Act, +c: KL.Act, +g: KL.Act, more: List<&2, KL.Act>) -> Maybe<&2, KlStep>:
  match more:
    case Nil{}:
      kl_guard(Bool.and(kl_is_check(c), kl_is_run(g)), kl_build_of(p, v, r, t))
    case x <> rest:
      None{}

def kl_rust_step.five(p: KL.Act, v: KL.Act, r: KL.Act, t: KL.Act, c: KL.Act, more: List<&2, KL.Act>) -> Maybe<&2, KlStep>:
  match more:
    case Nil{}:
      None{}
    case g <> rest:
      kl_rust_step.six(p, v, r, t, c, g, rest)

def kl_rust_step.four(p: KL.Act, v: KL.Act, r: KL.Act, t: KL.Act, more: List<&2, KL.Act>) -> Maybe<&2, KlStep>:
  match more:
    case Nil{}:
      None{}
    case c <> rest:
      kl_rust_step.five(p, v, r, t, c, rest)

def kl_rust_step.three(p: KL.Act, v: KL.Act, r: KL.Act, more: List<&2, KL.Act>) -> Maybe<&2, KlStep>:
  match more:
    case Nil{}:
      None{}
    case t <> rest:
      kl_rust_step.four(p, v, r, t, rest)

def kl_rust_step.two(+p: KL.Act, +v: KL.Act, more: List<&2, KL.Act>) -> Maybe<&2, KlStep>:
  match more:
    case Nil{}:
      kl_guard(Bool.and(kl_is_offline(p), kl_is_run(v)), Some{KlSync{}})
    case r <> rest:
      kl_rust_step.three(p, v, r, rest)

def kl_rust_step.one(+p: KL.Act, more: List<&2, KL.Act>) -> Maybe<&2, KlStep>:
  match more:
    case Nil{}:
      kl_guard(kl_is_run(p), Some{KlUse{}})
    case v <> rest:
      kl_rust_step.two(p, v, rest)

def kl_rust_step(xs: List<&2, KL.Act>) -> Maybe<&2, KlStep>:
  match xs:
    case Nil{}:
      None{}
    case p <> rest:
      kl_rust_step.one(p, rest)

# how a build's Python install and its hash-locked requirements get their
# files under a setup (venv/tests.rs
# `venv_builds_only_from_the_hash_locked_runtime_source`: no --offline
# under install, --offline in a session)
def kl_may_download(s: KL.Setup) -> KlFetch:
  match s:
    case KL.Local{}:
      KlOffline{}
    case KL.Install{}:
      KlDownload{}

# the step the venv found calls for (setup.rs `Found`, `SetupStep`): a
# current venv starts as it is, stale skills are synced, a stale venv is
# built; the venv and the runtime commands of a build always carry
# --offline (the same test)
def kl_step(f: KL.Found, +s: KL.Setup) -> KlStep:
  match f:
    case KL.Current{}:
      KlUse{}
    case KL.Skills{}:
      KlSync{}
    case KL.Stale{}:
      KlBuild{kl_may_download(s), KlOffline{}, kl_may_download(s), KlOffline{}}

# LAW kernel_plan_read_by_rust (R2, R4): Rust's plan reader (setup.rs `step_of`) reads the plan of every
# setup, as the step the venv found calls for: a current venv starts as it
# is, a venv with stale skills syncs them, a stale venv is built with the
# Python install and the hash-locked requirements downloading under
# `eukhe kernel install` and offline in a session, and the venv and the
# runtime always offline (the commands of venv/tests.rs
# `venv_builds_only_from_the_hash_locked_runtime_source`)
# EXCLUDES: a plan Rust refuses (the setup stops on "not a plan"), a plan
#   read as another step (a build of a current venv, a sync of a stale
#   one), a download of the venv or the runtime, an install that builds
#   Python or the locked packages offline, a fetch that is not hash-checked
law kernel_plan_read_by_rust:
  for f: KL.Found
  for s: KL.Setup
  {kl_rust_step(KL.plan(f, s)) == Some{kl_step(f, s)} : Maybe<&2, KlStep>}

# The setup's predicates, by their meaning
# ----------------------------------------
# The laws above read the model's predicates acts.fetching, acts.runs and
# acts.verified; these state what each means, by where the actions stand
# in the list (pre ++ [x] ++ post), not by a recursion over it.

# LAW kernel_fetching_finds_a_fetch (R1, R2): a list with a fetch anywhere in it fetches
# EXCLUDES: a fetching test that misses a fetch (so that
#   kernel_session_never_downloads holds of a session that downloads)
law kernel_fetching_finds_a_fetch:
  for pre: List<&2, KL.Act>
  for h: Bool
  for post: List<&2, KL.Act>
  {KL.acts.fetching(List.append(&2, KL.Act, pre, KL.Fetch{h} <> post)) == True{} : Bool}

# LAW kernel_fetching_means_a_fetch (R2): a list that fetches has a fetch in it
# EXCLUDES: a fetching test true of a plan with no download (so that
#   kernel_install_downloads_only_stale holds of an offline install)
law kernel_fetching_means_a_fetch:
  for +xs: List<&2, KL.Act>
  for fetches: {KL.acts.fetching(xs) == True{} : Bool}
  exs pre: List<&2, KL.Act>
  exs h: Bool
  exs post: List<&2, KL.Act>
  {xs == List.append(&2, KL.Act, pre, KL.Fetch{h} <> post) : List<&2, KL.Act>}

# LAW kernel_runs_means_a_run (R3): a list that runs has the kernel's start in it
# EXCLUDES: a runs test true of a plan that never starts the kernel (so
#   that kernel_setup_runs holds of a no-op setup)
law kernel_runs_means_a_run:
  for +xs: List<&2, KL.Act>
  for runs: {KL.acts.runs(xs) == True{} : Bool}
  exs pre: List<&2, KL.Act>
  exs post: List<&2, KL.Act>
  {xs == List.append(&2, KL.Act, pre, KL.Run{} <> post) : List<&2, KL.Act>}

# LAW kernel_verified_fetches_hashed (R2): in a list that is verified (from the start, nothing
# fetched yet), every fetch is hash-checked
# EXCLUDES: a verified test that passes a fetch with no hash check
law kernel_verified_fetches_hashed:
  for pre: List<&2, KL.Act>
  for +h: Bool
  for post: List<&2, KL.Act>
  for ok: {KL.acts.verified(List.append(&2, KL.Act, pre, KL.Fetch{h} <> post), True{}) == True{} : Bool}
  {h == True{} : Bool}

# some action of the list is the check
def kl_has_check(xs: List<&2, KL.Act>) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case x <> t:
      Bool.or(kl_is_check(x), kl_has_check(t))

# LAW kernel_verified_checks_between (R3): in a list that is verified (from the start), a check lies
# between every fetch and every start of the kernel after it
# EXCLUDES: a verified test that passes a start on files fetched since the
#   last check (unchecked packages run)
law kernel_verified_checks_between:
  for a: List<&2, KL.Act>
  for h: Bool
  for +b: List<&2, KL.Act>
  for c: List<&2, KL.Act>
  for ok: {KL.acts.verified(List.append(&2, KL.Act, a, KL.Fetch{h} <> List.append(&2, KL.Act, b, KL.Run{} <> c)), True{}) == True{} : Bool}
  {kl_has_check(b) == True{} : Bool}

# (K1.2) The session's tools
# --------------------------
# R5 is Rust's: crates/eukhe-core/src/kernel/bootstrap/mod.rs
# `format_setup_failure` and the ipython tool (durable/rlm/tool.rs); the
# test missing_kernel_tests.rs runs the session. No Bend code decides it.

# (K1.3) The bootstrap lock
# -------------------------
# crates/eukhe-core/src/kernel/bootstrap/dir_lock.rs
# `try_acquire_dir_lock` and `sweep_leftovers`.

# LAW kernel_lock_sweep_removes_dead (R6): the sweep removes every leftover of a dead attempt (a process that
# died inside its attempt)
law kernel_lock_sweep_removes_dead:
  for ls: List<&2, KL.Left>
  {KL.lefts.dead(KL.sweep(ls)) == 0n : Nat}

# LAW kernel_lock_sweep_keeps_live (R6): the sweep keeps every leftover of a live attempt and every other
# file
law kernel_lock_sweep_keeps_live:
  for ls: List<&2, KL.Left>
  {KL.lefts.live(KL.sweep(ls)) == KL.lefts.live(ls) : Nat}

# LAW kernel_sweep_one_verdict_per_file (R6): the sweep's answer (`keeps`, what the entry answers Rust)
# has one verdict per file
# EXCLUDES: a verdict list shorter or longer than the files (Rust zips them:
#   files left unswept or verdicts shifted)
law kernel_sweep_one_verdict_per_file:
  for ls: List<&2, KL.Left>
  {List.length(&2, Bool, KL.keeps(ls)) == List.length(&2, KL.Left, ls) : Nat}

# an attempt's file: its candidate or a lock it renamed aside
def kl_attempt_file(k: KL.FileKind) -> Bool:
  match k:
    case KL.Cand{}:
      True{}
    case KL.Aside{}:
      True{}
    case KL.Foreign{}:
      False{}

# LAW kernel_sweep_removes_dead_leftovers (R6): the verdict on the i-th file is "remove" when it is an
# attempt's candidate or renamed-aside lock whose owner is dead
# EXCLUDES: a dead process's candidate or stale lock left in place, a
#   verdict given to another position
law kernel_sweep_removes_dead_leftovers:
  for ls: List<&2, KL.Left>
  for i: Nat
  for +k: KL.FileKind
  for at: {List.get(&2, KL.Left, ls, i) == Some{KL.Left{k, KL.Dead{}}} : Maybe<&2, KL.Left>}
  for mine: {kl_attempt_file(k) == True{} : Bool}
  {List.get(&2, Bool, KL.keeps(ls), i) == Some{False{}} : Maybe<&2, Bool>}

# LAW kernel_sweep_keeps_live_owner (R6): the verdict on the i-th file is "keep" when its owner lives
# EXCLUDES: a running attempt's candidate or renamed lock removed under it
law kernel_sweep_keeps_live_owner:
  for ls: List<&2, KL.Left>
  for i: Nat
  for k: KL.FileKind
  for at: {List.get(&2, KL.Left, ls, i) == Some{KL.Left{k, KL.Alive{}}} : Maybe<&2, KL.Left>}
  {List.get(&2, Bool, KL.keeps(ls), i) == Some{True{}} : Maybe<&2, Bool>}

# LAW kernel_sweep_keeps_other_files (R6): the verdict on the i-th file is "keep" when it is no
# attempt's file, whatever owner it is read with
# EXCLUDES: a file beside the lock that no attempt wrote removed
law kernel_sweep_keeps_other_files:
  for ls: List<&2, KL.Left>
  for i: Nat
  for o: KL.Owner
  for at: {List.get(&2, KL.Left, ls, i) == Some{KL.Left{KL.Foreign{}, o}} : Maybe<&2, KL.Left>}
  {List.get(&2, Bool, KL.keeps(ls), i) == Some{True{}} : Maybe<&2, Bool>}

def kl_got(e: KL.End) -> Bool:
  match e:
    case KL.Got{}:
      True{}
    case KL.Busy{}:
      False{}
    case KL.Freed{}:
      False{}
    case KL.Crash{}:
      False{}

def kl_linked(x: KL.Seen) -> Bool:
  match x:
    case KL.Linked{}:
      True{}
    case KL.Vanished{}:
      False{}
    case KL.Owner{alive}:
      False{}
    case KL.NoOwner{age}:
      False{}

# LAW kernel_lock_got_iff_linked (R7): an attempt holds the lock (the verdict the entry answers,
# `attempt` of `lock.of`) exactly when it linked its candidate to the lock
# path
# EXCLUDES: two holders (a lock taken that another attempt linked), an
#   attempt that linked and still waits
law kernel_lock_got_iff_linked:
  for x: KL.Seen
  {kl_got(KL.attempt(KL.lock.of(x))) == kl_linked(x) : Bool}

# LAW kernel_lock_busy_while_in_use (R7): an attempt waits (busy) while the lock may be in use: its
# owner lives, or it names no owner and its age is unknown or not past 30 s
# (30 000 ms, dir_lock.rs test: 30 000 ms waits)
# EXCLUDES: a live owner's lock freed, a lock whose writer may still be
#   writing its pid freed, an unknown age read as old
law kernel_lock_busy_while_in_use:
  for a: Nat
  for young: {Nat.is_lt(30000n, a) == False{} : Bool}
  {KL.attempt(KL.lock.of(KL.Owner{True{}})) == KL.Busy{} : KL.End} & {KL.attempt(KL.lock.of(KL.NoOwner{None{}})) == KL.Busy{} : KL.End} & {KL.attempt(KL.lock.of(KL.NoOwner{Some{a}})) == KL.Busy{} : KL.End}

# LAW kernel_lock_frees_stale (R7): an attempt frees a stale lock: its owner is dead, it vanished
# before it was read, or it names no owner and is past 30 s old (dir_lock.rs
# test: 30 001 ms frees)
# EXCLUDES: a dead owner's lock waited on forever, an old half-written lock
#   never reclaimed
law kernel_lock_frees_stale:
  for a: Nat
  for old: {Nat.is_lt(30000n, a) == True{} : Bool}
  {KL.attempt(KL.lock.of(KL.Owner{False{}})) == KL.Freed{} : KL.End} & {KL.attempt(KL.lock.of(KL.Vanished{})) == KL.Freed{} : KL.End} & {KL.attempt(KL.lock.of(KL.NoOwner{Some{a}})) == KL.Freed{} : KL.End}

# (K1.4) The entry Rust calls
# ---------------------------
# The spellers below are the wire grammar of bend/ffi_kernel_local.bend's
# header (crates/eukhe-bend/WIRE.md), written with the wire primitives
# alone (laws/wire.bend proves them): the requests Rust writes (setup.rs
# `ask`, dir_lock.rs `keeps`, `verdict`) and the replies it reads.

# Spellers: the request

def spell_found(f: KL.Found, rest: String) -> String:
  match f:
    case KL.Current{}:
      Wr.put_nat(0n, rest)
    case KL.Skills{}:
      Wr.put_nat(1n, rest)
    case KL.Stale{}:
      Wr.put_nat(2n, rest)

def spell_setup(s: KL.Setup, rest: String) -> String:
  match s:
    case KL.Local{}:
      Wr.put_nat(0n, rest)
    case KL.Install{}:
      Wr.put_nat(1n, rest)

def spell_left.kind(k: KL.FileKind, rest: String) -> String:
  match k:
    case KL.Cand{}:
      Wr.put_nat(0n, rest)
    case KL.Aside{}:
      Wr.put_nat(1n, rest)
    case KL.Foreign{}:
      Wr.put_nat(2n, rest)

def spell_left.owner(o: KL.Owner, rest: String) -> String:
  match o:
    case KL.Alive{}:
      Wr.put_bool(True{}, rest)
    case KL.Dead{}:
      Wr.put_bool(False{}, rest)

def spell_left(l: KL.Left, rest: String) -> String:
  match l:
    case KL.Left{k, o}:
      spell_left.kind(k, spell_left.owner(o, rest))

def spell_lefts(ls: List<&2, KL.Left>, rest: String) -> String:
  match ls:
    case Nil{}:
      rest
    case l <> t:
      spell_left(l, spell_lefts(t, rest))

def spell_seen(x: KL.Seen, rest: String) -> String:
  match x:
    case KL.Linked{}:
      Wr.put_nat(0n, rest)
    case KL.Vanished{}:
      Wr.put_nat(1n, rest)
    case KL.Owner{alive}:
      Wr.put_nat(2n, Wr.put_bool(alive, rest))
    case KL.NoOwner{age}:
      match age:
        case None{}:
          Wr.put_nat(3n, Wr.put_nat(0n, rest))
        case Some{a}:
          Wr.put_nat(3n, Wr.put_nat(1n, Wr.put_nat(a, rest)))

# the request Rust writes for a
def spell_ask(a: KL.Ask) -> String:
  match a:
    case KL.AskPlan{f, s}:
      Wr.put_nat(0n, spell_found(f, spell_setup(s, "")))
    case KL.AskSweep{+ls}:
      Wr.put_nat(1n, Wr.put_nat(List.length(&2, KL.Left, ls), spell_lefts(ls, "")))
    case KL.AskLock{x}:
      Wr.put_nat(2n, spell_seen(x, ""))

# every number of a fits the wire
def ask_fits(a: KL.Ask) -> Bool:
  match a:
    case KL.AskPlan{f, s}:
      True{}
    case KL.AskSweep{ls}:
      LawsBase.wire_fits(List.length(&2, KL.Left, ls))
    case KL.AskLock{x}:
      match x:
        case KL.Linked{}:
          True{}
        case KL.Vanished{}:
          True{}
        case KL.Owner{alive}:
          True{}
        case KL.NoOwner{age}:
          match age:
            case None{}:
              True{}
            case Some{n}:
              LawsBase.wire_fits(n)

# Spellers: the reply

def spell_act(x: KL.Act, rest: String) -> String:
  match x:
    case KL.Fetch{h}:
      Wr.put_nat(0n, Wr.put_bool(h, rest))
    case KL.Offline{}:
      Wr.put_nat(1n, rest)
    case KL.Check{}:
      Wr.put_nat(2n, rest)
    case KL.Run{}:
      Wr.put_nat(3n, rest)

def spell_acts(xs: List<&2, KL.Act>, rest: String) -> String:
  match xs:
    case Nil{}:
      rest
    case x <> t:
      spell_act(x, spell_acts(t, rest))

def spell_bools(xs: List<&2, Bool>, rest: String) -> String:
  match xs:
    case Nil{}:
      rest
    case b <> t:
      Wr.put_bool(b, spell_bools(t, rest))

def spell_end(e: KL.End, rest: String) -> String:
  match e:
    case KL.Got{}:
      Wr.put_nat(0n, rest)
    case KL.Busy{}:
      Wr.put_nat(1n, rest)
    case KL.Freed{}:
      Wr.put_nat(2n, rest)
    case KL.Crash{}:
      Wr.put_nat(3n, rest)

# the reply to a, spelled: the plan (a count, then each action), the
# sweep's verdicts (a count, then each), the attempt's end; the decisions
# are the model's (`plan`, `keeps`, `attempt` of `lock.of`), which the laws
# of K1.1 and K1.3 pin
def spell_answer(a: KL.Ask) -> String:
  match a:
    case KL.AskPlan{f, s}:
      +xs = KL.plan(f, s)
      Wr.put_nat(List.length(&2, KL.Act, xs), spell_acts(xs, ""))
    case KL.AskSweep{ls}:
      +bs = KL.keeps(ls)
      Wr.put_nat(List.length(&2, Bool, bs), spell_bools(bs, ""))
    case KL.AskLock{x}:
      spell_end(KL.attempt(KL.lock.of(x)), "")

# LAW kernel_ffi_answers (R9): on every request Rust writes, the entry answers the plan, the sweep's verdict on each file in order, or the attempt's end
law kernel_ffi_answers:
  for +a: KL.Ask
  for fits: {ask_fits(a) == True{} : Bool}
  {FKL.ffi(spell_ask(a)) == spell_answer(a) : String}

# LAW kernel_ffi_reads_only_requests (R9): an input the entry answers with no error form is the
# spelling of one request whose numbers fit the wire
# EXCLUDES: a default answer to malformed input, input left over ignored,
#   an unknown tag read as a request, a count or an age past the wire read
law kernel_ffi_reads_only_requests:
  for +s: String
  for ok: {LawsBase.wire_opens_err(FKL.ffi(s)) == False{} : Bool}
  exs a: KL.Ask
  {s == spell_ask(a) : String} & {ask_fits(a) == True{} : Bool}

# LAW kernel_ffi_refuses_one_error (R9): every error the entry answers is exactly
# `E kernel_local: malformed request`
# EXCLUDES: an error text that varies with the input, a second error form
law kernel_ffi_refuses_one_error:
  for +s: String
  for bad: {LawsBase.wire_opens_err(FKL.ffi(s)) == True{} : Bool}
  {FKL.ffi(s) == Wr.err("kernel_local: malformed request") : String}

# LAW kernel_ffi_example (R9): anchor: the strings Rust sends: the install's plan of a stale venv, a sweep of three files, a lock naming no owner 30001 ms old, a lock of a live owner; a request with input left over is refused
law kernel_ffi_example:
  {FKL.ffi("0,2,1,") == "6,0,T1,0,T1,2,3," : String} &
  {FKL.ffi("1,3,0,T0,F2,F") == "3,TFT" : String} &
  {FKL.ffi("2,3,1,30001,") == "2," : String} &
  {FKL.ffi("2,2,T") == "1," : String} &
  {LawsBase.wire_opens_err(FKL.ffi("2,2,Tx")) == True{} : Bool}
