# kernel_local: the kernel setup, the session's tools while the kernel is
# missing, and the bootstrap lock's leftovers
# (crates/eukhe-core/src/kernel/bootstrap: setup.rs, mod.rs, dir_lock.rs).
# The setup's plan, the sweep's verdict on each leftover and the lock
# attempt's verdict run as this code (entry bend/ffi_kernel_local.bend);
# laws/kernel_local.bend states the laws; proof/kernel_local/ proves them.

import Base

# Part 1: the setup
# -----------------
# The kernel runs on one pinned standalone CPython. Eukhe fetches it
# itself, with a pinned uv release that it also fetches itself, into its
# own directory, on the first kernel use. The setup looks at three things
# in that directory: the pinned uv, the pinned CPython and the kernel env,
# each there (True) or not. A session and `eukhe kernel install` run the
# same setup.

# one action of a setup, in order
type Act is Data:
  # the pinned uv release archive is downloaded; hashed: the archive is
  # checked against the pinned sha256 before it is unpacked
  FetchUv{hashed: Bool}
  # `uv python install` of the pinned version from the pinned download
  # list; hashed: uv checks the archive against the pinned sha256 before
  # it installs it
  FetchPython{hashed: Bool}
  # `uv venv --offline`: the kernel env from local files only, never the
  # network
  MakeEnv{}
  # the kernel starts
  Run{}

def plan.env(env: Bool) -> List<&2, Act>:
  match env:
    case True{}:
      [Run{}]
    case False{}:
      [MakeEnv{}, Run{}]

def plan.python(python: Bool, rest: List<&2, Act>) -> List<&2, Act>:
  match python:
    case True{}:
      rest
    case False{}:
      FetchPython{True{}} <> rest

def plan.uv(uv: Bool, rest: List<&2, Act>) -> List<&2, Act>:
  match uv:
    case True{}:
      rest
    case False{}:
      FetchUv{True{}} <> rest

# the actions of a setup that finds the pinned uv, the pinned CPython and
# the kernel env (True: it is there)
def plan(uv: Bool, python: Bool, env: Bool) -> List<&2, Act>:
  plan.uv(uv, plan.python(python, plan.env(env)))

# does an action of the list fetch (use the network)
def acts.fetching(xs: List<&2, Act>) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case FetchUv{h} <> rest:
      True{}
    case FetchPython{h} <> rest:
      True{}
    case MakeEnv{} <> rest:
      acts.fetching(rest)
    case Run{} <> rest:
      acts.fetching(rest)

# does an action of the list fetch the pinned uv
def acts.fetches_uv(xs: List<&2, Act>) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case FetchUv{h} <> rest:
      True{}
    case FetchPython{h} <> rest:
      acts.fetches_uv(rest)
    case MakeEnv{} <> rest:
      acts.fetches_uv(rest)
    case Run{} <> rest:
      acts.fetches_uv(rest)

# does an action of the list fetch the pinned CPython
def acts.fetches_python(xs: List<&2, Act>) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case FetchUv{h} <> rest:
      acts.fetches_python(rest)
    case FetchPython{h} <> rest:
      True{}
    case MakeEnv{} <> rest:
      acts.fetches_python(rest)
    case Run{} <> rest:
      acts.fetches_python(rest)

# does an action of the list make the kernel env
def acts.makes_env(xs: List<&2, Act>) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case FetchUv{h} <> rest:
      acts.makes_env(rest)
    case FetchPython{h} <> rest:
      acts.makes_env(rest)
    case MakeEnv{} <> rest:
      True{}
    case Run{} <> rest:
      acts.makes_env(rest)

# every fetch is hashed: what it fetched is checked against its pinned
# sha256 before it is unpacked or installed
def acts.verified(xs: List<&2, Act>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case FetchUv{h} <> rest:
      Bool.and(h, acts.verified(rest))
    case FetchPython{h} <> rest:
      Bool.and(h, acts.verified(rest))
    case MakeEnv{} <> rest:
      acts.verified(rest)
    case Run{} <> rest:
      acts.verified(rest)

# every action runs with what it uses there: uv fetches the CPython, uv
# makes the env from the CPython, the kernel starts on the env and its
# CPython (uv, python, env: what is there before the first action; a
# fetch or the env's making puts its thing there)
def acts.ready(xs: List<&2, Act>, +uv: Bool, +python: Bool, +env: Bool) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case FetchUv{h} <> rest:
      acts.ready(rest, True{}, python, env)
    case FetchPython{h} <> rest:
      Bool.and(uv, acts.ready(rest, uv, True{}, env))
    case MakeEnv{} <> rest:
      Bool.and(Bool.and(uv, python), acts.ready(rest, uv, python, True{}))
    case Run{} <> rest:
      Bool.and(Bool.and(python, env), acts.ready(rest, uv, python, env))

# is the list empty
def acts.none(xs: List<&2, Act>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case x <> rest:
      False{}

# the kernel starts as the last action and at no other
def acts.ends_started(xs: List<&2, Act>) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case FetchUv{h} <> rest:
      acts.ends_started(rest)
    case FetchPython{h} <> rest:
      acts.ends_started(rest)
    case MakeEnv{} <> rest:
      acts.ends_started(rest)
    case Run{} <> rest:
      acts.none(rest)

# Part 2: the session's tools
# ---------------------------

type Kernel is Data:
  Up{}
  # a step of the setup failed (a fetch, e.g. offline): the error names it
  Missing{}

def start.ran(ok: Bool) -> Kernel:
  match ok:
    case True{}:
      Up{}
    case False{}:
      Missing{}

def start.all(all: Bool, ok: Bool) -> Kernel:
  match all:
    case True{}:
      Up{}
    case False{}:
      start.ran(ok)

# the kernel after a setup that finds uv, python and env (True: it is
# there); ok: every step the setup ran worked. With all three there no
# step runs, so none fails
def start(uv: Bool, python: Bool, env: Bool, ok: Bool) -> Kernel:
  start.all(Bool.and(uv, Bool.and(python, env)), ok)

# a tool call: the python tool, or any other tool (by its number)
type Call is Data:
  Python{}
  Other{n: Nat}

type Answer is Data:
  # the tool ran
  Ran{}
  # the tool answered with the setup step that failed (the failed fetch)
  NamesFailed{}

def answer(t: Call, k: Kernel) -> Answer:
  match t:
    case Python{}:
      match k:
        case Up{}:
          Ran{}
        case Missing{}:
          NamesFailed{}
    case Other{n}:
      Ran{}

# Part 3: the bootstrap lock's leftovers
# --------------------------------------

type Owner is Data:
  Alive{}
  Dead{}

# a file beside the lock: an attempt's candidate, a stale lock renamed
# aside, or another file
type FileKind is Data:
  Cand{}
  Aside{}
  Foreign{}

type Left is Data:
  Left{kind: FileKind, owner: Owner}

# the lock an attempt finds: none, held by a live owner, or by a dead one
type Lock is Data:
  Free{}
  Live{}
  Gone{}

# how an attempt ends; Crash: its process died inside it
type End is Data:
  Got{}
  Busy{}
  Freed{}
  Crash{}

def attempt(l: Lock) -> End:
  match l:
    case Free{}:
      Got{}
    case Live{}:
      Busy{}
    case Gone{}:
      Freed{}

# what an attempt sees once its candidate is written: the candidate was
# linked to the lock path (the lock is its own), the lock vanished before
# it was read, the lock names an owner (alive or not), or the lock names
# none (a lock left half written, or a legacy dir lock without a pid
# file): then its age in ms, None when its mtime cannot be read or lies in
# the future
type Seen is Data:
  Linked{}
  Vanished{}
  Owner{alive: Bool}
  NoOwner{age: Maybe<&2, Nat>}

# a lock that names no owner is stale only past this age (ms): its writer
# had that long to finish writing the pid
def stale_ms() -> Nat:
  30000n

def lock.past(old: Bool) -> Lock:
  match old:
    case True{}:
      Gone{}
    case False{}:
      Live{}

def lock.age(m: Maybe<&2, Nat>) -> Lock:
  match m:
    case None{}:
      Live{}
    case Some{a}:
      lock.past(Nat.is_lt(stale_ms(), a))

# the lock an attempt finds, from what it sees
def lock.of(s: Seen) -> Lock:
  match s:
    case Linked{}:
      Free{}
    case Vanished{}:
      Gone{}
    case Owner{alive}:
      match alive:
        case True{}:
          Live{}
        case False{}:
          Gone{}
    case NoOwner{age}:
      lock.age(age)

# the attempt's own candidates left after it ends
def own_left(e: End) -> Nat:
  match e:
    case Got{}:
      0n
    case Busy{}:
      0n
    case Freed{}:
      0n
    case Crash{}:
      1n

# does the sweep keep the file: a live attempt's leftover or another file
def keep(l: Left) -> Bool:
  match l:
    case Left{Cand{}, Alive{}}:
      True{}
    case Left{Cand{}, Dead{}}:
      False{}
    case Left{Aside{}, Alive{}}:
      True{}
    case Left{Aside{}, Dead{}}:
      False{}
    case Left{Foreign{}, o}:
      True{}

def keep.cons(b: Bool, l: Left, xs: List<&2, Left>) -> List<&2, Left>:
  match b:
    case True{}:
      l <> xs
    case False{}:
      xs

def sweep(ls: List<&2, Left>) -> List<&2, Left>:
  match ls:
    case Nil{}:
      Nil{}
    case +l <> rest:
      keep.cons(keep(l), l, sweep(rest))

# 1 for a leftover of a dead attempt
def dead(l: Left) -> Nat:
  match l:
    case Left{Cand{}, Alive{}}:
      0n
    case Left{Cand{}, Dead{}}:
      1n
    case Left{Aside{}, Alive{}}:
      0n
    case Left{Aside{}, Dead{}}:
      1n
    case Left{Foreign{}, o}:
      0n

# the leftovers of dead attempts
def lefts.dead(ls: List<&2, Left>) -> Nat:
  match ls:
    case Nil{}:
      0n
    case +l <> rest:
      Nat.add(dead(l), lefts.dead(rest))

# 1 for a file the sweep must keep
def live(l: Left) -> Nat:
  match l:
    case Left{Cand{}, Alive{}}:
      1n
    case Left{Cand{}, Dead{}}:
      0n
    case Left{Aside{}, Alive{}}:
      1n
    case Left{Aside{}, Dead{}}:
      0n
    case Left{Foreign{}, o}:
      1n

# the files the sweep must keep
def lefts.live(ls: List<&2, Left>) -> Nat:
  match ls:
    case Nil{}:
      0n
    case +l <> rest:
      Nat.add(live(l), lefts.live(rest))

# Requests
# --------

# what Rust asks: the plan of a setup that finds the pinned uv, the pinned
# CPython and the kernel env (True: it is there), the sweep's verdict on
# each leftover beside the lock, the verdict of a lock attempt
type Ask is Data:
  AskPlan{uv: Bool, python: Bool, env: Bool}
  AskSweep{files: List<&2, Left>}
  AskLock{seen: Seen}

# the sweep's verdict on each file, in order (True: it stays)
def keeps(ls: List<&2, Left>) -> List<&2, Bool>:
  match ls:
    case Nil{}:
      Nil{}
    case +l <> rest:
      keep(l) <> keeps(rest)
