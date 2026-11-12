# eukhe: the laws of area kernel_local

import Base
import ../bend/kernel_local.bend as KL
import ../bend/ffi_kernel_local.bend as FKL
import ../bend/wire.bend as Wr
import ./base.bend as LawsBase

# ---- kernel_local ----

# LAWS (K1): the kernel environment is Eukhe's own. The kernel runs on
# one pinned CPython that Eukhe fetches itself, with a pinned uv that it
# also fetches itself, into its own directory, on the first kernel use:
# no install step is asked of the user, and a session and `eukhe kernel
# install` run the same setup. Every fetch is checked against its pinned
# sha256 before what it fetched is used; once uv and the CPython are
# there the kernel works offline; a missing kernel never blocks the other
# tools; a bootstrap lock candidate never outlives its attempt. The
# setup's plan, the sweep's verdicts and the lock attempt's verdict run as
# bend/kernel_local.bend (`plan`, `keeps`, `attempt` of `lock.of`) through
# the entry bend/ffi_kernel_local.bend; PROOF.bend proves the laws (as
# KernelLocal.<law>) with the lemmas of proof/kernel_local/.
#
# Requirements (crates/eukhe-core/src/kernel/bootstrap: setup.rs, mod.rs,
# pinned_kernel_tests.rs, dir_lock.rs):
# R1 (K1.1): the setup asks nothing of the user: a session and `eukhe
#   kernel install` run the same plan, which fetches the pinned uv and the
#   pinned CPython exactly when they are not there and makes the kernel env
#   exactly when it is not there; once the uv and the CPython are there no
#   setup downloads, so the kernel works offline (setup.rs `setup_steps`;
#   test `the_steps_come_from_the_compiled_core`).
# R2 (K1.1): every fetch is checked against its pinned sha256 before what
#   it fetched is unpacked or installed; the env is made from local files
#   only (`uv venv --offline`).
# R3 (K1.1): every action runs with what it uses already there (the
#   CPython is fetched by a uv that is there, the env is made by a uv and
#   from a CPython that are there, the kernel starts on an env and a
#   CPython that are there), and every setup ends with the kernel started,
#   once, as its last action.
# R4 (K1.1): Rust's plan reader (setup.rs `steps_of`) reads every plan, as
#   the steps for what is not there, in order: the uv fetch, the CPython
#   fetch, the env's making; it refuses (not a plan) a fetch that is not
#   hashed, a plan that does not end with the start or starts before its
#   end, and a step out of order or twice (test
#   `a_reply_that_is_not_a_plan_is_malformed`).
# R5 (K1.2): a missing kernel (a step of the setup failed, e.g. a fetch
#   while offline) never blocks another tool, and the python tool answers
#   with the failed step (mod.rs `KERNEL_FETCH_FAILED`; the test
#   pinned_kernel_tests.rs runs the real session).
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
# crates/eukhe-core/src/kernel/bootstrap/setup.rs `setup_steps`. Every
# input is free: the pinned uv, the pinned CPython and the kernel env are
# each there (True) or not.

# LAW kernel_offline_once_fetched (R1): a setup that finds the pinned uv and the pinned CPython fetches nothing,
# whether the kernel env is there or not: once they are fetched, the kernel works offline
law kernel_offline_once_fetched:
  for env: Bool
  {KL.acts.fetching(KL.plan(True{}, True{}, env)) == False{} : Bool}

# LAW kernel_downloads_only_absent (R1): a setup downloads exactly when the pinned uv or the pinned
# CPython is not there; with both there it uses local files only
# EXCLUDES: a setup that downloads with the uv and the CPython there (no
#   offline use), a setup that starts without fetching an absent uv or
#   CPython
law kernel_downloads_only_absent:
  for uv: Bool
  for python: Bool
  for env: Bool
  {KL.acts.fetching(KL.plan(uv, python, env)) == Bool.not(Bool.and(uv, python)) : Bool}

# LAW kernel_uv_fetched_iff_absent (R1): the setup fetches the pinned uv exactly when it is not there: nothing
# is asked of the user, and a uv that is there is not fetched again
law kernel_uv_fetched_iff_absent:
  for uv: Bool
  for python: Bool
  for env: Bool
  {KL.acts.fetches_uv(KL.plan(uv, python, env)) == Bool.not(uv) : Bool}

# LAW kernel_python_fetched_iff_absent (R1): the setup fetches the pinned CPython exactly when it is not there:
# nothing is asked of the user, and a CPython that is there is not fetched again
law kernel_python_fetched_iff_absent:
  for uv: Bool
  for python: Bool
  for env: Bool
  {KL.acts.fetches_python(KL.plan(uv, python, env)) == Bool.not(python) : Bool}

# LAW kernel_env_made_iff_absent (R1): the setup makes the kernel env exactly when it is not there
law kernel_env_made_iff_absent:
  for uv: Bool
  for python: Bool
  for env: Bool
  {KL.acts.makes_env(KL.plan(uv, python, env)) == Bool.not(env) : Bool}

# LAW kernel_fetch_verified_before_use (R2): every fetch of every setup is checked against its pinned sha256
# before what it fetched is unpacked or installed
law kernel_fetch_verified_before_use:
  for uv: Bool
  for python: Bool
  for env: Bool
  {KL.acts.verified(KL.plan(uv, python, env)) == True{} : Bool}

# LAW kernel_setup_uses_only_present (R3): every action of a setup runs with what it uses already there: the
# CPython is fetched by a uv that is there, the env is made by a uv and from a CPython that are there,
# and the kernel starts on an env and a CPython that are there
law kernel_setup_uses_only_present:
  for uv: Bool
  for python: Bool
  for env: Bool
  {KL.acts.ready(KL.plan(uv, python, env), uv, python, env) == True{} : Bool}

# LAW kernel_setup_ends_started (R3): every setup ends with the kernel start, once: no setup is a no-op, and
# none starts the kernel before its last action
law kernel_setup_ends_started:
  for uv: Bool
  for python: Bool
  for env: Bool
  {KL.acts.ends_started(KL.plan(uv, python, env)) == True{} : Bool}

# The step Rust's plan reader makes of an action before the start
# (setup.rs `SetupStep`)
type KlStep is Data:
  KlFetchUv{}
  KlFetchPython{}
  KlMakeEnv{}

# setup.rs `steps_of`, per action before the last: a hashed fetch or the
# env's making is a step; an unhashed fetch or a start there is no plan
def kl_step_of(x: KL.Act) -> Maybe<&2, KlStep>:
  match x:
    case KL.FetchUv{h}:
      match h:
        case True{}:
          Some{KlFetchUv{}}
        case False{}:
          None{}
    case KL.FetchPython{h}:
      match h:
        case True{}:
          Some{KlFetchPython{}}
        case False{}:
          None{}
    case KL.MakeEnv{}:
      Some{KlMakeEnv{}}
    case KL.Run{}:
      None{}

def kl_is_run(x: KL.Act) -> Bool:
  match x:
    case KL.FetchUv{h}:
      False{}
    case KL.FetchPython{h}:
      False{}
    case KL.MakeEnv{}:
      False{}
    case KL.Run{}:
      True{}

# setup.rs `place`: where a step stands in a setup
def kl_place(s: KlStep) -> Nat:
  match s:
    case KlFetchUv{}:
      0n
    case KlFetchPython{}:
      1n
    case KlMakeEnv{}:
      2n

# every step stands before the next one (setup.rs `steps_of`: each pair
# of neighbours in place order)
def kl_ordered.next(more: List<&2, KlStep>, x: KlStep) -> Bool:
  match more:
    case Nil{}:
      True{}
    case +y <> rest:
      Bool.and(Nat.is_lt(kl_place(x), kl_place(y)), kl_ordered.next(rest, y))

def kl_ordered(xs: List<&2, KlStep>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case x <> rest:
      kl_ordered.next(rest, x)

def kl_guard(ok: Bool, m: Maybe<&2, List<&2, KlStep>>) -> Maybe<&2, List<&2, KlStep>>:
  match ok:
    case True{}:
      m
    case False{}:
      None{}

def kl_steps.cons(m: Maybe<&2, KlStep>, r: Maybe<&2, List<&2, KlStep>>) -> Maybe<&2, List<&2, KlStep>>:
  match m:
    case None{}:
      None{}
    case Some{s}:
      match r:
        case None{}:
          None{}
        case Some{ss}:
          Some{s <> ss}

# the steps of x and the actions after it: the last action must be the
# start, every one before it a step
def kl_steps.go(more: List<&2, KL.Act>, +x: KL.Act) -> Maybe<&2, List<&2, KlStep>>:
  match more:
    case Nil{}:
      kl_guard(kl_is_run(x), Some{Nil{}})
    case y <> rest:
      kl_steps.cons(kl_step_of(x), kl_steps.go(rest, y))

def kl_steps.ordered(r: Maybe<&2, List<&2, KlStep>>) -> Maybe<&2, List<&2, KlStep>>:
  match r:
    case None{}:
      None{}
    case Some{+ss}:
      kl_guard(kl_ordered(ss), Some{ss})

# setup.rs `steps_of`: the steps a plan describes, or "not a plan" (None):
# the empty plan, a plan that does not end with the start, a start or an
# unhashed fetch before the end, a step out of order or twice
def kl_rust_steps(xs: List<&2, KL.Act>) -> Maybe<&2, List<&2, KlStep>>:
  match xs:
    case Nil{}:
      None{}
    case x <> rest:
      kl_steps.ordered(kl_steps.go(rest, x))

# the steps a setup must run for what it finds (True: it is there), as
# setup.rs test `the_steps_come_from_the_compiled_core` lists them: what
# is not there is fetched or made, in order, and nothing else
def kl_steps(uv: Bool, python: Bool, env: Bool) -> List<&2, KlStep>:
  match uv python env:
    case True{} True{} True{}:
      []
    case True{} True{} False{}:
      [KlMakeEnv{}]
    case True{} False{} True{}:
      [KlFetchPython{}]
    case True{} False{} False{}:
      [KlFetchPython{}, KlMakeEnv{}]
    case False{} True{} True{}:
      [KlFetchUv{}]
    case False{} True{} False{}:
      [KlFetchUv{}, KlMakeEnv{}]
    case False{} False{} True{}:
      [KlFetchUv{}, KlFetchPython{}]
    case False{} False{} False{}:
      [KlFetchUv{}, KlFetchPython{}, KlMakeEnv{}]

# LAW kernel_plan_read_by_rust (R1, R4): Rust's plan reader (setup.rs `steps_of`) reads the plan of every
# setup, as the steps for what it finds not there: the uv fetch when the
# uv is not there, then the CPython fetch when the CPython is not there,
# then the env's making when the env is not there, every fetch hashed,
# then the start (the steps of setup.rs test
# `the_steps_come_from_the_compiled_core`)
# EXCLUDES: a plan Rust refuses (the setup stops on "not a plan"), a step
#   for something that is there (a fetch again, no offline use), a missing
#   step for something that is not, steps out of order, a fetch that is
#   not hash-checked
law kernel_plan_read_by_rust:
  for uv: Bool
  for python: Bool
  for env: Bool
  {kl_rust_steps(KL.plan(uv, python, env)) == Some{kl_steps(uv, python, env)} : Maybe<&2, List<&2, KlStep>>}

# The setup's predicates, by their meaning
# ----------------------------------------
# The laws above read the model's predicates acts.fetching, acts.verified,
# acts.ready and acts.ends_started; these state what each means, by where
# the actions stand in the list (pre ++ [x] ++ post), not by a recursion
# over it.

# a fetch: of the uv or of the CPython
def kl_is_fetch(x: KL.Act) -> Bool:
  match x:
    case KL.FetchUv{h}:
      True{}
    case KL.FetchPython{h}:
      True{}
    case KL.MakeEnv{}:
      False{}
    case KL.Run{}:
      False{}

# LAW kernel_fetching_finds_a_fetch (R1): a list with a fetch anywhere in it fetches
# EXCLUDES: a fetching test that misses a fetch (so that
#   kernel_offline_once_fetched holds of a setup that downloads)
law kernel_fetching_finds_a_fetch:
  for pre: List<&2, KL.Act>
  for x: KL.Act
  for post: List<&2, KL.Act>
  for fetch: {kl_is_fetch(x) == True{} : Bool}
  {KL.acts.fetching(List.append(&2, KL.Act, pre, x <> post)) == True{} : Bool}

# LAW kernel_fetching_means_a_fetch (R1): a list that fetches has a fetch in it
# EXCLUDES: a fetching test true of a plan with no download (so that
#   kernel_downloads_only_absent holds of a setup that never fetches)
law kernel_fetching_means_a_fetch:
  for +xs: List<&2, KL.Act>
  for fetches: {KL.acts.fetching(xs) == True{} : Bool}
  exs pre: List<&2, KL.Act>
  exs x: KL.Act
  exs post: List<&2, KL.Act>
  {xs == List.append(&2, KL.Act, pre, x <> post) : List<&2, KL.Act>} & {kl_is_fetch(x) == True{} : Bool}

# some action of the list is the start
def kl_has_run(xs: List<&2, KL.Act>) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case x <> t:
      match x:
        case KL.FetchUv{h}:
          kl_has_run(t)
        case KL.FetchPython{h}:
          kl_has_run(t)
        case KL.MakeEnv{}:
          kl_has_run(t)
        case KL.Run{}:
          True{}

# LAW kernel_runs_means_a_run (R3): a list that ends started has the kernel's start as its last action, and
# no start before it
# EXCLUDES: an ends-started test true of a plan that never starts the
#   kernel (so that kernel_setup_ends_started holds of a no-op setup), or
#   that starts it before its last action
law kernel_runs_means_a_run:
  for +xs: List<&2, KL.Act>
  for ends: {KL.acts.ends_started(xs) == True{} : Bool}
  exs pre: List<&2, KL.Act>
  {xs == List.append(&2, KL.Act, pre, [KL.Run{}]) : List<&2, KL.Act>} & {kl_has_run(pre) == False{} : Bool}

# what a fetch's archive is checked by: True when it is hash-checked (an
# action that fetches nothing has nothing to check)
def kl_hashed(x: KL.Act) -> Bool:
  match x:
    case KL.FetchUv{h}:
      h
    case KL.FetchPython{h}:
      h
    case KL.MakeEnv{}:
      True{}
    case KL.Run{}:
      True{}

# LAW kernel_verified_fetches_hashed (R2): in a list that is verified, every fetch is hash-checked
# EXCLUDES: a verified test that passes a fetch with no hash check
law kernel_verified_fetches_hashed:
  for pre: List<&2, KL.Act>
  for +x: KL.Act
  for post: List<&2, KL.Act>
  for ok: {KL.acts.verified(List.append(&2, KL.Act, pre, x <> post)) == True{} : Bool}
  {kl_hashed(x) == True{} : Bool}

# some action of the list is the CPython fetch
def kl_has_fetch_python(xs: List<&2, KL.Act>) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case x <> t:
      match x:
        case KL.FetchUv{h}:
          kl_has_fetch_python(t)
        case KL.FetchPython{h}:
          True{}
        case KL.MakeEnv{}:
          kl_has_fetch_python(t)
        case KL.Run{}:
          kl_has_fetch_python(t)

# some action of the list is the env's making
def kl_has_make_env(xs: List<&2, KL.Act>) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case x <> t:
      match x:
        case KL.FetchUv{h}:
          kl_has_make_env(t)
        case KL.FetchPython{h}:
          kl_has_make_env(t)
        case KL.MakeEnv{}:
          True{}
        case KL.Run{}:
          kl_has_make_env(t)

# LAW kernel_ready_starts_on_present (R3): in a list that is ready from what is there before it (uv,
# python, env), every start of the kernel comes after the CPython is there (it was there, or the CPython
# fetch comes before the start) and after the env is there (it was there, or its making comes before)
# EXCLUDES: a ready test that passes a start on a CPython or an env that
#   is not there (fetched or made after the start, or never)
law kernel_ready_starts_on_present:
  for a: List<&2, KL.Act>
  for +uv: Bool
  for +python: Bool
  for +env: Bool
  for b: List<&2, KL.Act>
  for ok: {KL.acts.ready(List.append(&2, KL.Act, a, KL.Run{} <> b), uv, python, env) == True{} : Bool}
  {Bool.or(python, kl_has_fetch_python(a)) == True{} : Bool} & {Bool.or(env, kl_has_make_env(a)) == True{} : Bool}

# (K1.2) The session's tools
# --------------------------
# R5: crates/eukhe-core/src/kernel/bootstrap/mod.rs (the failed step's
# message, `KERNEL_FETCH_FAILED`) and the python tool
# (durable/rlm/tool.rs); the laws kernel_missing_spares_tools,
# kernel_missing_names_failed_step, kernel_start_exact and
# kernel_answer_exact below state the model's part; the test
# pinned_kernel_tests.rs runs the real session.

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
    case KL.AskPlan{uv, python, env}:
      Wr.put_nat(0n, Wr.put_bool(uv, Wr.put_bool(python, Wr.put_bool(env, ""))))
    case KL.AskSweep{+ls}:
      Wr.put_nat(1n, Wr.put_nat(List.length(&2, KL.Left, ls), spell_lefts(ls, "")))
    case KL.AskLock{x}:
      Wr.put_nat(2n, spell_seen(x, ""))

# every number of a fits the wire
def ask_fits(a: KL.Ask) -> Bool:
  match a:
    case KL.AskPlan{uv, python, env}:
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
    case KL.FetchUv{h}:
      Wr.put_nat(0n, Wr.put_bool(h, rest))
    case KL.FetchPython{h}:
      Wr.put_nat(1n, Wr.put_bool(h, rest))
    case KL.MakeEnv{}:
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
    case KL.AskPlan{uv, python, env}:
      +xs = KL.plan(uv, python, env)
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

# LAW kernel_ffi_example (R9): anchor: the strings Rust sends: the plan of a first kernel use (nothing there), the plan of a setup that finds everything, a sweep of three files, a lock naming no owner 30001 ms old, a lock of a live owner; a request with input left over is refused
law kernel_ffi_example:
  {FKL.ffi("0,FFF") == "4,0,T1,T2,3," : String} &
  {FKL.ffi("0,TTT") == "1,3," : String} &
  {FKL.ffi("1,3,0,T0,F2,F") == "3,TFT" : String} &
  {FKL.ffi("2,3,1,30001,") == "2," : String} &
  {FKL.ffi("2,2,T") == "1," : String} &
  {LawsBase.wire_opens_err(FKL.ffi("2,2,Tx")) == True{} : Bool}

# LAW kernel_missing_spares_tools (R5): a missing kernel never blocks another tool: it runs whatever the
# setup found and whether its steps worked
law kernel_missing_spares_tools:
  for n: Nat
  for uv: Bool
  for python: Bool
  for env: Bool
  for ok: Bool
  {KL.answer(KL.Other{n}, KL.start(uv, python, env, ok)) == KL.Ran{} : KL.Answer}

# LAW kernel_missing_names_failed_step (R5): when a step of the setup failed (the uv, the CPython or the env
# was not there, and its fetch or making failed, e.g. offline), the python tool answers with the failed step
law kernel_missing_names_failed_step:
  for uv: Bool
  for python: Bool
  for env: Bool
  for absent: {Bool.and(uv, Bool.and(python, env)) == False{} : Bool}
  {KL.answer(KL.Python{}, KL.start(uv, python, env, False{})) == KL.NamesFailed{} : KL.Answer}
def start_spec.ok(ok: Bool) -> KL.Kernel:
  match ok:
    case True{}:
      KL.Up{}
    case False{}:
      KL.Missing{}

# the kernel after a setup: up when the uv, the CPython and the env were
# all there (no step ran, so none failed) or the steps it ran worked;
# missing otherwise
def start_spec(uv: Bool, python: Bool, env: Bool, ok: Bool) -> KL.Kernel:
  match uv:
    case True{}:
      match python:
        case True{}:
          match env:
            case True{}:
              KL.Up{}
            case False{}:
              start_spec.ok(ok)
        case False{}:
          start_spec.ok(ok)
    case False{}:
      start_spec.ok(ok)

# LAW kernel_start_exact (R5): the kernel is up after a setup that finds the uv, the CPython and the env all there, or whose steps worked, and missing only when a step of a setup that found one of them not there failed
law kernel_start_exact:
  for uv: Bool
  for python: Bool
  for env: Bool
  for ok: Bool
  {KL.start(uv, python, env, ok) == start_spec(uv, python, env, ok) : KL.Kernel}

# a tool's answer: only the python tool on a missing kernel names the
# failed step; every other call runs
def answer_spec(t: KL.Call, k: KL.Kernel) -> KL.Answer:
  match t:
    case KL.Python{}:
      match k:
        case KL.Up{}:
          KL.Ran{}
        case KL.Missing{}:
          KL.NamesFailed{}
    case KL.Other{n}:
      KL.Ran{}

# LAW kernel_answer_exact (R5): the python tool runs on an up kernel and names the failed step on a missing one; every other tool runs either way
law kernel_answer_exact:
  for t: KL.Call
  for k: KL.Kernel
  {KL.answer(t, k) == answer_spec(t, k) : KL.Answer}

# some action fetches: the uv fetch or the CPython fetch
def fetching_spec(xs: List<&2, KL.Act>) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case x <> t:
      match x:
        case KL.FetchUv{h}:
          True{}
        case KL.FetchPython{h}:
          True{}
        case KL.MakeEnv{}:
          fetching_spec(t)
        case KL.Run{}:
          fetching_spec(t)

# some action is the uv fetch
def fetches_uv_spec(xs: List<&2, KL.Act>) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case x <> t:
      match x:
        case KL.FetchUv{h}:
          True{}
        case KL.FetchPython{h}:
          fetches_uv_spec(t)
        case KL.MakeEnv{}:
          fetches_uv_spec(t)
        case KL.Run{}:
          fetches_uv_spec(t)

# some action is the CPython fetch
def fetches_python_spec(xs: List<&2, KL.Act>) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case x <> t:
      match x:
        case KL.FetchUv{h}:
          fetches_python_spec(t)
        case KL.FetchPython{h}:
          True{}
        case KL.MakeEnv{}:
          fetches_python_spec(t)
        case KL.Run{}:
          fetches_python_spec(t)

# some action is the env's making
def makes_env_spec(xs: List<&2, KL.Act>) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case x <> t:
      match x:
        case KL.FetchUv{h}:
          makes_env_spec(t)
        case KL.FetchPython{h}:
          makes_env_spec(t)
        case KL.MakeEnv{}:
          True{}
        case KL.Run{}:
          makes_env_spec(t)

# every fetch, of the uv or of the CPython, is hashed
def verified_spec(xs: List<&2, KL.Act>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case x <> t:
      match x:
        case KL.FetchUv{h}:
          match h:
            case True{}:
              verified_spec(t)
            case False{}:
              False{}
        case KL.FetchPython{h}:
          match h:
            case True{}:
              verified_spec(t)
            case False{}:
              False{}
        case KL.MakeEnv{}:
          verified_spec(t)
        case KL.Run{}:
          verified_spec(t)

# every action finds what it uses there, given what is there before the
# first one (uv, python, env): the uv fetch uses nothing and puts the uv
# there; the CPython fetch uses the uv and puts the CPython there; the
# env's making uses the uv and the CPython and puts the env there; the
# start uses the CPython and the env
def ready_spec(xs: List<&2, KL.Act>, +uv: Bool, +python: Bool, +env: Bool) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case x <> t:
      match x:
        case KL.FetchUv{h}:
          ready_spec(t, True{}, python, env)
        case KL.FetchPython{h}:
          match uv:
            case True{}:
              ready_spec(t, True{}, True{}, env)
            case False{}:
              False{}
        case KL.MakeEnv{}:
          match uv:
            case True{}:
              match python:
                case True{}:
                  ready_spec(t, True{}, True{}, True{})
                case False{}:
                  False{}
            case False{}:
              False{}
        case KL.Run{}:
          match python:
            case True{}:
              match env:
                case True{}:
                  ready_spec(t, uv, True{}, True{})
                case False{}:
                  False{}
            case False{}:
              False{}

# the list is not empty, its last action is the start, and no action
# before the last is
def ends_started_spec(xs: List<&2, KL.Act>) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case x <> t:
      match x:
        case KL.FetchUv{h}:
          ends_started_spec(t)
        case KL.FetchPython{h}:
          ends_started_spec(t)
        case KL.MakeEnv{}:
          ends_started_spec(t)
        case KL.Run{}:
          match t:
            case Nil{}:
              True{}
            case y <> u:
              False{}

# an attempt leaves a candidate of its own only when its process died in it
def own_left_spec(e: KL.End) -> Nat:
  match e:
    case KL.Got{}:
      0n
    case KL.Busy{}:
      0n
    case KL.Freed{}:
      0n
    case KL.Crash{}:
      1n

# LAW kernel_terms_exact: the model's predicates mean what the laws above read them as: a list fetches when some action is the uv fetch or the CPython fetch, fetches the uv, fetches the CPython or makes the env when some action is that one, is verified when every fetch is hashed, is ready when every action finds what it uses there, ends started when its last action is the start and no other is; an attempt leaves its own candidate only when its process died inside it
law kernel_terms_exact:
  for xs: List<&2, KL.Act>
  for uv: Bool
  for python: Bool
  for env: Bool
  for e: KL.End
  {KL.acts.fetching(xs) == fetching_spec(xs) : Bool} & {KL.acts.fetches_uv(xs) == fetches_uv_spec(xs) : Bool} & {KL.acts.fetches_python(xs) == fetches_python_spec(xs) : Bool} & {KL.acts.makes_env(xs) == makes_env_spec(xs) : Bool} & {KL.acts.verified(xs) == verified_spec(xs) : Bool} & {KL.acts.ready(xs, uv, python, env) == ready_spec(xs, uv, python, env) : Bool} & {KL.acts.ends_started(xs) == ends_started_spec(xs) : Bool} & {KL.own_left(e) == own_left_spec(e) : Nat}

# 1 for a leftover of a dead attempt: a candidate or a set-aside lock of a
# dead owner
def dead_one(l: KL.Left) -> Nat:
  match l:
    case KL.Left{k, o}:
      match k:
        case KL.Cand{}:
          match o:
            case KL.Alive{}:
              0n
            case KL.Dead{}:
              1n
        case KL.Aside{}:
          match o:
            case KL.Alive{}:
              0n
            case KL.Dead{}:
              1n
        case KL.Foreign{}:
          0n

# the leftovers of dead attempts
def dead_spec(ls: List<&2, KL.Left>) -> Nat:
  match ls:
    case Nil{}:
      0n
    case l <> t:
      Nat.add(dead_one(l), dead_spec(t))

# the files the sweep must keep
def live_spec(ls: List<&2, KL.Left>) -> Nat:
  match ls:
    case Nil{}:
      0n
    case l <> t:
      Nat.add(Nat.sub(1n, dead_one(l)), live_spec(t))

def keep_spec.owner(o: KL.Owner) -> Bool:
  match o:
    case KL.Alive{}:
      True{}
    case KL.Dead{}:
      False{}

# the sweep's verdict on a file: it removes an attempt's candidate or a
# stale lock renamed aside whose owner is dead; it keeps a live owner's
# and every other file
def keep_spec(l: KL.Left) -> Bool:
  match l:
    case KL.Left{k, o}:
      match k:
        case KL.Cand{}:
          keep_spec.owner(o)
        case KL.Aside{}:
          keep_spec.owner(o)
        case KL.Foreign{}:
          True{}

def sweep_spec.cons(b: Bool, l: KL.Left, t: List<&2, KL.Left>) -> List<&2, KL.Left>:
  match b:
    case True{}:
      l <> t
    case False{}:
      t

# the files the sweep keeps, in order
def sweep_spec(ls: List<&2, KL.Left>) -> List<&2, KL.Left>:
  match ls:
    case Nil{}:
      Nil{}
    case +l <> t:
      sweep_spec.cons(keep_spec(l), l, sweep_spec(t))

# LAW kernel_sweep_terms_exact: the model's sweep keeps exactly the files whose verdict is keep, in order, and its counts are the dead attempts' leftovers and the files to keep
law kernel_sweep_terms_exact:
  for ls: List<&2, KL.Left>
  {KL.sweep(ls) == sweep_spec(ls) : List<&2, KL.Left>} & {KL.lefts.dead(ls) == dead_spec(ls) : Nat} & {KL.lefts.live(ls) == live_spec(ls) : Nat}
