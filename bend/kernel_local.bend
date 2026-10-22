# kernel_local: the model of the kernel setup, the session's tools while
# the kernel is missing, and the bootstrap lock's leftovers
# (crates/eukhe-core/src/kernel/bootstrap: setup.rs, venv.rs, mod.rs,
# dir_lock.rs). LAWS.bend section kernel_local states the laws;
# PROOF.bend section kernel_local proves them; bend/bridge_kernel_local.bend
# runs this model against the Rust code.

import Base

# Part 1: the setup
# -----------------

# what the setup may fetch: a session (Local) or `eukhe kernel install`
type Setup is Data:
  Local{}
  Install{}

# the kernel venv the setup finds
type Found is Data:
  Current{}
  Skills{}
  Stale{}

# one action of a setup, in order
type Act is Data:
  # a uv command that may download; hashed: uv checks each file it gets
  # against a pinned hash before it installs the file
  Fetch{hashed: Bool}
  # a uv command that uses local files only (--offline)
  Offline{}
  # uv pip check of the built venv
  Check{}
  # the kernel starts
  Run{}

# a build: the Python install, the venv, the hash-locked requirements, the
# runtime from its local directory, then the check
def build(s: Setup) -> List<&2, Act>:
  match s:
    case Local{}:
      [Offline{}, Offline{}, Offline{}, Offline{}, Check{}, Run{}]
    case Install{}:
      [Fetch{True{}}, Offline{}, Fetch{True{}}, Offline{}, Check{}, Run{}]

# the actions of a setup that finds f
def plan(f: Found, s: Setup) -> List<&2, Act>:
  match f:
    case Current{}:
      [Run{}]
    case Skills{}:
      [Offline{}, Run{}]
    case Stale{}:
      build(s)

# does an action of the list fetch
def acts.fetching(xs: List<&2, Act>) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case Fetch{h} <> rest:
      True{}
    case Offline{} <> rest:
      acts.fetching(rest)
    case Check{} <> rest:
      acts.fetching(rest)
    case Run{} <> rest:
      acts.fetching(rest)

# does the kernel start
def acts.runs(xs: List<&2, Act>) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case Fetch{h} <> rest:
      acts.runs(rest)
    case Offline{} <> rest:
      acts.runs(rest)
    case Check{} <> rest:
      acts.runs(rest)
    case Run{} <> rest:
      True{}

# every fetch is hashed, and the kernel starts only when a check came
# after the last fetch (clean: no fetch since the last check)
def acts.verified(xs: List<&2, Act>, +clean: Bool) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Fetch{h} <> rest:
      Bool.and(h, acts.verified(rest, False{}))
    case Offline{} <> rest:
      acts.verified(rest, clean)
    case Check{} <> rest:
      acts.verified(rest, True{})
    case Run{} <> rest:
      Bool.and(clean, acts.verified(rest, clean))

# Part 2: the session's tools
# ---------------------------

type Kernel is Data:
  Up{}
  # the setup failed: the error names `eukhe kernel install`
  Missing{}

# the kernel after a setup that finds f; ok: the sync or the build worked
def start(f: Found, ok: Bool) -> Kernel:
  match f:
    case Current{}:
      Up{}
    case Skills{}:
      match ok:
        case True{}:
          Up{}
        case False{}:
          Missing{}
    case Stale{}:
      match ok:
        case True{}:
          Up{}
        case False{}:
          Missing{}

# a tool call: the ipython tool, or any other tool (by its number)
type Tool is Data:
  Python{}
  Other{n: Nat}

type Answer is Data:
  # the tool ran
  Ran{}
  # the tool answered with the install command
  NamesInstall{}

def answer(t: Tool, k: Kernel) -> Answer:
  match t:
    case Python{}:
      match k:
        case Up{}:
          Ran{}
        case Missing{}:
          NamesInstall{}
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

def End.crashed(e: End) -> Bool:
  match e:
    case Got{}:
      False{}
    case Busy{}:
      False{}
    case Freed{}:
      False{}
    case Crash{}:
      True{}

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
