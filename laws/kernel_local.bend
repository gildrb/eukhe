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
# tools; a bootstrap lock candidate never outlives its attempt. Each law
# is an open claim about the model in bend/kernel_local.bend; PROOF.bend
# proves them (as KernelLocal.<law>) with the lemmas of
# proof/kernel_local/.

# (K1.1) The setup
# ----------------
# crates/eukhe-core/src/kernel/bootstrap/setup.rs `setup_steps`. Every
# input is free: the pinned uv, the pinned CPython and the kernel env are
# each there (True) or not.

# LAW kernel_offline_once_fetched: a setup that finds the pinned uv and the pinned CPython fetches nothing,
# whether the kernel env is there or not: once they are fetched, the kernel works offline
law kernel_offline_once_fetched:
  for env: Bool
  {KL.acts.fetching(KL.plan(True{}, True{}, env)) == False{} : Bool}

# LAW kernel_uv_fetched_iff_absent: the setup fetches the pinned uv exactly when it is not there: nothing
# is asked of the user, and a uv that is there is not fetched again
law kernel_uv_fetched_iff_absent:
  for uv: Bool
  for python: Bool
  for env: Bool
  {KL.acts.fetches_uv(KL.plan(uv, python, env)) == Bool.not(uv) : Bool}

# LAW kernel_python_fetched_iff_absent: the setup fetches the pinned CPython exactly when it is not there:
# nothing is asked of the user, and a CPython that is there is not fetched again
law kernel_python_fetched_iff_absent:
  for uv: Bool
  for python: Bool
  for env: Bool
  {KL.acts.fetches_python(KL.plan(uv, python, env)) == Bool.not(python) : Bool}

# LAW kernel_env_made_iff_absent: the setup makes the kernel env exactly when it is not there
law kernel_env_made_iff_absent:
  for uv: Bool
  for python: Bool
  for env: Bool
  {KL.acts.makes_env(KL.plan(uv, python, env)) == Bool.not(env) : Bool}

# LAW kernel_fetch_verified_before_use: every fetch of every setup is checked against its pinned sha256
# before what it fetched is unpacked or installed
law kernel_fetch_verified_before_use:
  for uv: Bool
  for python: Bool
  for env: Bool
  {KL.acts.verified(KL.plan(uv, python, env)) == True{} : Bool}

# LAW kernel_setup_uses_only_present: every action of a setup runs with what it uses already there: the
# CPython is fetched by a uv that is there, the env is made by a uv and from a CPython that are there,
# and the kernel starts on an env and a CPython that are there
law kernel_setup_uses_only_present:
  for uv: Bool
  for python: Bool
  for env: Bool
  {KL.acts.ready(KL.plan(uv, python, env), uv, python, env) == True{} : Bool}

# LAW kernel_setup_ends_started: every setup ends with the kernel start, once: no setup is a no-op, and
# none starts the kernel before its last action
law kernel_setup_ends_started:
  for uv: Bool
  for python: Bool
  for env: Bool
  {KL.acts.ends_started(KL.plan(uv, python, env)) == True{} : Bool}

# (K1.2) The session's tools
# --------------------------
# crates/eukhe-core/src/kernel/bootstrap/mod.rs `format_setup_failure`
# and the python tool (durable/rlm/tool.rs), which answers with the
# kernel's start error.

# LAW kernel_missing_spares_tools: a missing kernel never blocks another tool: it runs whatever the
# setup found and whether its steps worked
law kernel_missing_spares_tools:
  for n: Nat
  for uv: Bool
  for python: Bool
  for env: Bool
  for ok: Bool
  {KL.answer(KL.Other{n}, KL.start(uv, python, env, ok)) == KL.Ran{} : KL.Answer}

# LAW kernel_missing_names_failed_step: when a step of the setup failed (the uv, the CPython or the env
# was not there, and its fetch or making failed, e.g. offline), the python tool answers with the failed step
law kernel_missing_names_failed_step:
  for uv: Bool
  for python: Bool
  for env: Bool
  for absent: {Bool.and(uv, Bool.and(python, env)) == False{} : Bool}
  {KL.answer(KL.Python{}, KL.start(uv, python, env, False{})) == KL.NamesFailed{} : KL.Answer}

# (K1.3) The bootstrap lock
# -------------------------
# crates/eukhe-core/src/kernel/bootstrap/dir_lock.rs
# `try_acquire_dir_lock` and `sweep_leftovers`.

# LAW kernel_lock_attempt_leaves_none: an attempt on any lock leaves no candidate of its own
law kernel_lock_attempt_leaves_none:
  for l: KL.Lock
  {KL.own_left(KL.attempt(l)) == 0n : Nat}

# LAW kernel_lock_sweep_removes_dead: the sweep removes every leftover of a dead attempt (a process that
# died inside its attempt)
law kernel_lock_sweep_removes_dead:
  for ls: List<&2, KL.Left>
  {KL.lefts.dead(KL.sweep(ls)) == 0n : Nat}

# LAW kernel_lock_sweep_keeps_live: the sweep keeps every leftover of a live attempt and every other
# file
law kernel_lock_sweep_keeps_live:
  for ls: List<&2, KL.Left>
  {KL.lefts.live(KL.sweep(ls)) == KL.lefts.live(ls) : Nat}

# (K1.4) The rules exactly, and the entry Rust calls
# --------------------------------------------------
# The setup's plan (setup.rs `setup_steps`: which of the uv fetch, the
# CPython fetch and the env's making run), the sweep's verdict on each
# leftover (dir_lock.rs `sweep_leftovers`) and the attempt's verdict
# (dir_lock.rs `try_acquire_dir_lock`: what an attempt that did not link
# its candidate makes of the lock it finds) run as
# bend/kernel_local.bend through the
# entry bend/ffi_kernel_local.bend. The spellers and the reader below are
# the wire grammar of that entry written with the wire primitives alone
# (laws/wire.bend proves their round trips); they never call the entry's
# own codec.

# Terms
# -----

# the setup's actions, exactly: the pinned uv is fetched when it is not
# there, then the pinned CPython when it is not there, then the kernel
# env is made when it is not there, then the kernel starts; every fetch
# is hashed
def plan_spec(uv: Bool, python: Bool, env: Bool) -> List<&2, KL.Act>:
  match uv python env:
    case True{} True{} True{}:
      [KL.Run{}]
    case True{} True{} False{}:
      [KL.MakeEnv{}, KL.Run{}]
    case True{} False{} True{}:
      [KL.FetchPython{True{}}, KL.Run{}]
    case True{} False{} False{}:
      [KL.FetchPython{True{}}, KL.MakeEnv{}, KL.Run{}]
    case False{} True{} True{}:
      [KL.FetchUv{True{}}, KL.Run{}]
    case False{} True{} False{}:
      [KL.FetchUv{True{}}, KL.MakeEnv{}, KL.Run{}]
    case False{} False{} True{}:
      [KL.FetchUv{True{}}, KL.FetchPython{True{}}, KL.Run{}]
    case False{} False{} False{}:
      [KL.FetchUv{True{}}, KL.FetchPython{True{}}, KL.MakeEnv{}, KL.Run{}]

def judge_spec.old(old: Bool) -> KL.End:
  match old:
    case True{}:
      KL.Freed{}
    case False{}:
      KL.Busy{}

# how an attempt that did not link its candidate ends: an owner that
# lives keeps the lock (busy); a dead owner, a lock gone before it was
# read, or a lock that names no owner and is older than 30 s is stale
# (freed: renamed aside and removed); a lock that names no owner and is
# younger, or whose age is unknown, is busy (its writer may still be
# writing the pid)
def judge_spec(x: KL.Seen) -> KL.End:
  match x:
    case KL.Linked{}:
      KL.Got{}
    case KL.Vanished{}:
      KL.Freed{}
    case KL.Owner{alive}:
      match alive:
        case True{}:
          KL.Busy{}
        case False{}:
          KL.Freed{}
    case KL.NoOwner{age}:
      match age:
        case None{}:
          KL.Busy{}
        case Some{a}:
          judge_spec.old(Nat.is_lt(30000n, a))

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

# the sweep's verdict on each file, T: it stays
def spell_keeps(ls: List<&2, KL.Left>, rest: String) -> String:
  match ls:
    case Nil{}:
      rest
    case l <> t:
      Wr.put_bool(keep_spec(l), spell_keeps(t, rest))

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

# the reply to a: the plan, the sweep's verdicts, the attempt's end
def spell_answer(a: KL.Ask) -> String:
  match a:
    case KL.AskPlan{uv, python, env}:
      +xs = plan_spec(uv, python, env)
      Wr.put_nat(List.length(&2, KL.Act, xs), spell_acts(xs, ""))
    case KL.AskSweep{+ls}:
      Wr.put_nat(List.length(&2, KL.Left, ls), spell_keeps(ls, ""))
    case KL.AskLock{x}:
      spell_end(judge_spec(x), "")

# Reader: the requests the entry accepts, read with the wire primitives

def read_plan.env(uv: Bool, python: Bool, r: Wr.Dec<Bool>) -> Wr.Dec<KL.Ask>:
  match r:
    case Wr.Got{e, s}:
      Wr.Got{KL.AskPlan{uv, python, e}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def read_plan.python(uv: Bool, r: Wr.Dec<Bool>) -> Wr.Dec<KL.Ask>:
  match r:
    case Wr.Got{p, s}:
      read_plan.env(uv, p, Wr.get_bool(s))
    case Wr.Bad{}:
      Wr.Bad{}

def read_plan(r: Wr.Dec<Bool>) -> Wr.Dec<KL.Ask>:
  match r:
    case Wr.Got{u, s}:
      read_plan.python(u, Wr.get_bool(s))
    case Wr.Bad{}:
      Wr.Bad{}

def read_kind.tag(t: Nat, s: String) -> Wr.Dec<KL.FileKind>:
  match t:
    case 0n:
      Wr.Got{KL.Cand{}, s}
    case 1n:
      Wr.Got{KL.Aside{}, s}
    case 2n:
      Wr.Got{KL.Foreign{}, s}
    case 3n+p:
      Wr.Bad{}

def read_kind(r: Wr.Dec<Nat>) -> Wr.Dec<KL.FileKind>:
  match r:
    case Wr.Got{t, s}:
      read_kind.tag(t, s)
    case Wr.Bad{}:
      Wr.Bad{}

def read_left.owner(k: KL.FileKind, r: Wr.Dec<Bool>) -> Wr.Dec<KL.Left>:
  match r:
    case Wr.Got{b, s}:
      match b:
        case True{}:
          Wr.Got{KL.Left{k, KL.Alive{}}, s}
        case False{}:
          Wr.Got{KL.Left{k, KL.Dead{}}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def read_left.go(r: Wr.Dec<KL.FileKind>) -> Wr.Dec<KL.Left>:
  match r:
    case Wr.Got{k, s}:
      read_left.owner(k, Wr.get_bool(s))
    case Wr.Bad{}:
      Wr.Bad{}

def read_left(s: String) -> Wr.Dec<KL.Left>:
  read_left.go(read_kind(Wr.get_nat(s)))

def read_lefts.cons(l: KL.Left, r: Wr.Dec<List<&2, KL.Left>>) -> Wr.Dec<List<&2, KL.Left>>:
  match r:
    case Wr.Got{ls, s}:
      Wr.Got{l <> ls, s}
    case Wr.Bad{}:
      Wr.Bad{}

# n more files after the one cur answers
def read_lefts(n: Nat, cur: Wr.Dec<KL.Left>) -> Wr.Dec<List<&2, KL.Left>>:
  match n:
    case 0n:
      match cur:
        case Wr.Got{l, s}:
          Wr.Got{[l], s}
        case Wr.Bad{}:
          Wr.Bad{}
    case 1n+m:
      match cur:
        case Wr.Got{l, s}:
          read_lefts.cons(l, read_lefts(m, read_left(s)))
        case Wr.Bad{}:
          Wr.Bad{}

def read_sweep.files(r: Wr.Dec<List<&2, KL.Left>>) -> Wr.Dec<KL.Ask>:
  match r:
    case Wr.Got{ls, s}:
      Wr.Got{KL.AskSweep{ls}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def read_sweep(r: Wr.Dec<Nat>) -> Wr.Dec<KL.Ask>:
  match r:
    case Wr.Got{n, s}:
      match n:
        case 0n:
          Wr.Got{KL.AskSweep{Nil{}}, s}
        case 1n+m:
          read_sweep.files(read_lefts(m, read_left(s)))
    case Wr.Bad{}:
      Wr.Bad{}

def read_age.some(r: Wr.Dec<Nat>) -> Wr.Dec<KL.Seen>:
  match r:
    case Wr.Got{a, s}:
      Wr.Got{KL.NoOwner{Some{a}}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def read_age.tag(t: Nat, s: String) -> Wr.Dec<KL.Seen>:
  match t:
    case 0n:
      Wr.Got{KL.NoOwner{None{}}, s}
    case 1n:
      read_age.some(Wr.get_nat(s))
    case 2n+p:
      Wr.Bad{}

def read_age(r: Wr.Dec<Nat>) -> Wr.Dec<KL.Seen>:
  match r:
    case Wr.Got{t, s}:
      read_age.tag(t, s)
    case Wr.Bad{}:
      Wr.Bad{}

def read_owner(r: Wr.Dec<Bool>) -> Wr.Dec<KL.Seen>:
  match r:
    case Wr.Got{b, s}:
      Wr.Got{KL.Owner{b}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def read_seen.tag(t: Nat, s: String) -> Wr.Dec<KL.Seen>:
  match t:
    case 0n:
      Wr.Got{KL.Linked{}, s}
    case 1n:
      Wr.Got{KL.Vanished{}, s}
    case 2n:
      read_owner(Wr.get_bool(s))
    case 3n:
      read_age(Wr.get_nat(s))
    case 4n+p:
      Wr.Bad{}

def read_seen(r: Wr.Dec<Nat>) -> Wr.Dec<KL.Seen>:
  match r:
    case Wr.Got{t, s}:
      read_seen.tag(t, s)
    case Wr.Bad{}:
      Wr.Bad{}

def read_lock(r: Wr.Dec<KL.Seen>) -> Wr.Dec<KL.Ask>:
  match r:
    case Wr.Got{x, s}:
      Wr.Got{KL.AskLock{x}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def read_ask.tag(t: Nat, s: String) -> Wr.Dec<KL.Ask>:
  match t:
    case 0n:
      read_plan(Wr.get_bool(s))
    case 1n:
      read_sweep(Wr.get_nat(s))
    case 2n:
      read_lock(read_seen(Wr.get_nat(s)))
    case 3n+p:
      Wr.Bad{}

def read_ask.go(r: Wr.Dec<Nat>) -> Wr.Dec<KL.Ask>:
  match r:
    case Wr.Got{t, s}:
      read_ask.tag(t, s)
    case Wr.Bad{}:
      Wr.Bad{}

def read_ask.end(whole: Bool, a: KL.Ask) -> Maybe<&2, KL.Ask>:
  match whole:
    case True{}:
      Some{a}
    case False{}:
      None{}

def read_ask.whole(r: Wr.Dec<KL.Ask>) -> Maybe<&2, KL.Ask>:
  match r:
    case Wr.Got{a, s}:
      read_ask.end(Wr.end(s), a)
    case Wr.Bad{}:
      None{}

# the request s is, when s is exactly one request
def read_ask(s: String) -> Maybe<&2, KL.Ask>:
  read_ask.whole(read_ask.go(Wr.get_nat(s)))

# Laws
# ----

# LAW kernel_plan_exact: the setup's actions are exactly these, for each of the eight things it can find: the fetch of the pinned uv when it is not there, then the fetch of the pinned CPython when it is not there, then the making of the kernel env when it is not there, then the kernel start; every fetch checked against its pinned sha256
law kernel_plan_exact:
  for uv: Bool
  for python: Bool
  for env: Bool
  {KL.plan(uv, python, env) == plan_spec(uv, python, env) : List<&2, KL.Act>}

# LAW kernel_lock_judge: an attempt that did not link its candidate is busy while the lock's owner lives, or while a lock naming no owner is at most 30 s old or of unknown age; it frees a lock whose owner is dead, that vanished, or that names no owner and is older
law kernel_lock_judge:
  for x: KL.Seen
  {KL.attempt(KL.lock.of(x)) == judge_spec(x) : KL.End}

# LAW kernel_ffi_answers: on every request Rust writes, the entry answers the plan, the sweep's verdict on each file in order, or the attempt's end
law kernel_ffi_answers:
  for +a: KL.Ask
  for fits: {ask_fits(a) == True{} : Bool}
  {FKL.ffi(spell_ask(a)) == spell_answer(a) : String}

# LAW kernel_ffi_malformed: every input that is not exactly one request gets the error form
law kernel_ffi_malformed:
  for +s: String
  for no: {read_ask(s) == None{} : Maybe<&2, KL.Ask>}
  {LawsBase.wire_opens_err(FKL.ffi(s)) == True{} : Bool}

# LAW kernel_ffi_example: anchor: the strings Rust sends: the plan of a first kernel use (nothing there), the plan of a setup that finds everything, a sweep of three files, a lock naming no owner 30001 ms old, a lock of a live owner; a request with input left over is refused
law kernel_ffi_example:
  {FKL.ffi("0,FFF") == "4,0,T1,T2,3," : String} &
  {FKL.ffi("0,TTT") == "1,3," : String} &
  {FKL.ffi("1,3,0,T0,F2,F") == "3,TFT" : String} &
  {FKL.ffi("2,3,1,30001,") == "2," : String} &
  {FKL.ffi("2,2,T") == "1," : String} &
  {read_ask("2,2,Tx") == None{} : Maybe<&2, KL.Ask>} &
  {LawsBase.wire_opens_err(FKL.ffi("2,2,Tx")) == True{} : Bool}

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

# LAW kernel_start_exact: the kernel is up after a setup that finds the uv, the CPython and the env all there, or whose steps worked, and missing only when a step of a setup that found one of them not there failed
law kernel_start_exact:
  for uv: Bool
  for python: Bool
  for env: Bool
  for ok: Bool
  {KL.start(uv, python, env, ok) == start_spec(uv, python, env, ok) : KL.Kernel}

# LAW kernel_answer_exact: the python tool runs on an up kernel and names the failed step on a missing one; every other tool runs either way
law kernel_answer_exact:
  for t: KL.Call
  for k: KL.Kernel
  {KL.answer(t, k) == answer_spec(t, k) : KL.Answer}

# LAW kernel_ffi_malformed_exact: every input that is not exactly one request gets exactly the error form 'E ', then "kernel_local: malformed request" (the text Rust's Reader reports)
law kernel_ffi_malformed_exact:
  for +s: String
  for no: {read_ask(s) == None{} : Maybe<&2, KL.Ask>}
  {FKL.ffi(s) == SCon{'E', SCon{' ', "kernel_local: malformed request"}} : String}

# the reply to the input s: when s is exactly one request (read_ask), the
# spelled answer to it (spell_answer: plan_spec, keep_spec, judge_spec);
# else the error form 'E ', then "kernel_local: malformed request"
def ffi_spec.read(m: Maybe<&2, KL.Ask>) -> String:
  match m:
    case None{}:
      SCon{'E', SCon{' ', "kernel_local: malformed request"}}
    case Some{a}:
      spell_answer(a)

def ffi_spec(s: String) -> String:
  ffi_spec.read(read_ask(s))

# LAW kernel_ffi_exact: the entry's reply to every input string is the spec's: to exactly one request, the plan, the sweep's verdict on each file in order, or the attempt's end, spelled from the specs alone; to any other input, exactly the error form
# EXCLUDES: a reply that the specs do not determine for some input (a
#   request read by a reader the laws do not fix, a model function pinned
#   only through the entry, a value answered to malformed input, an error
#   form with another text)
law kernel_ffi_exact:
  for +s: String
  {FKL.ffi(s) == ffi_spec(s) : String}

# The model's own terms, pinned
# -----------------------------
# The laws of K1.1-K1.3 read the model's own predicates and counters
# (acts.fetching, acts.fetches_uv, acts.fetches_python, acts.makes_env,
# acts.verified, acts.ready, acts.ends_started, own_left, sweep,
# lefts.dead, lefts.live); these pin each of them to its meaning.

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

# LAW kernel_terms_exact: the model's predicates mean what the laws above read them as: a list fetches when some action is the uv fetch or the CPython fetch, fetches the uv, fetches the CPython or makes the env when some action is that one, is verified when every fetch is hashed, is ready when every action finds what it uses there, ends started when its last action is the start and no other is; an attempt leaves its own candidate only when its process died inside it
law kernel_terms_exact:
  for xs: List<&2, KL.Act>
  for uv: Bool
  for python: Bool
  for env: Bool
  for e: KL.End
  {KL.acts.fetching(xs) == fetching_spec(xs) : Bool} & {KL.acts.fetches_uv(xs) == fetches_uv_spec(xs) : Bool} & {KL.acts.fetches_python(xs) == fetches_python_spec(xs) : Bool} & {KL.acts.makes_env(xs) == makes_env_spec(xs) : Bool} & {KL.acts.verified(xs) == verified_spec(xs) : Bool} & {KL.acts.ready(xs, uv, python, env) == ready_spec(xs, uv, python, env) : Bool} & {KL.acts.ends_started(xs) == ends_started_spec(xs) : Bool} & {KL.own_left(e) == own_left_spec(e) : Nat}

# LAW kernel_sweep_terms_exact: the model's sweep keeps exactly the files whose verdict is keep, in order, and its counts are the dead attempts' leftovers and the files to keep
law kernel_sweep_terms_exact:
  for ls: List<&2, KL.Left>
  {KL.sweep(ls) == sweep_spec(ls) : List<&2, KL.Left>} & {KL.lefts.dead(ls) == dead_spec(ls) : Nat} & {KL.lefts.live(ls) == live_spec(ls) : Nat}
