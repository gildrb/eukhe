# undo: the per-prompt workspace snapshots of a top-level session and what
# /undo and /diff do with them (Rust: crates/eukhe-core/src/undo). A
# snapshot is taken at the start of every turn (a prompt's run); /undo
# restores the newest snapshot not undone and drops it, refused when none
# is left; a turn after undos takes its snapshot on top of what is left,
# so the undone ones are gone; /diff compares the workspace with the
# newest snapshot (the turn) or with the session's first (all). Restoring
# and diffing work on rows: one per path whose content differs between the
# snapshot and the workspace, or that is held (ignored by the workspace's
# .gitignore, over the size cap, a nested repository) on either side.
# Pure: no IO, no @unsafe. laws/undo.bend states its laws.

import Base

# Snapshots
# ---------

# what /diff compares the workspace with
type Scope is Data:
  # the newest snapshot not undone
  Turn{}
  # the session's first snapshot
  All{}

# what happens to the snapshots
type Ev is Data:
  # a turn starts: its snapshot, numbered `turn`, is taken
  TurnStart{turn: Nat}
  # /undo
  Undo{}
  # /diff
  Diff{scope: Scope}

# the snapshots: the turns not undone, newest first, and the session's
# first turn (kept after it is undone: /diff all compares with it)
type St is Data:
  St{live: List<&2, Nat>, base: Maybe<&2, Nat>}

# the answer to an event
type Act is Data:
  # the turn's snapshot is kept
  Took{}
  # restore the snapshot of `turn`
  Restore{turn: Nat}
  # nothing to undo: nothing changes
  Refused{}
  # compare the workspace with the snapshot of `turn`
  Compare{turn: Nat}
  # no snapshot to compare with
  NoSnapshot{}

def compare(m: Maybe<&2, Nat>) -> Act:
  match m:
    case None{}:
      NoSnapshot{}
    case Some{t}:
      Compare{t}

def newest(live: List<&2, Nat>) -> Maybe<&2, Nat>:
  match live:
    case Nil{}:
      None{}
    case Con{t, rest}:
      Some{t}

def keep_base(base: Maybe<&2, Nat>, t: Nat) -> Maybe<&2, Nat>:
  match base:
    case None{}:
      Some{t}
    case Some{b}:
      Some{b}

def step.undo(live: List<&2, Nat>, base: Maybe<&2, Nat>) -> St & Act:
  match live:
    case Nil{}:
      (St{Nil{}, base}, Refused{})
    case Con{t, rest}:
      (St{rest, base}, Restore{t})

def step.diff(+live: List<&2, Nat>, +base: Maybe<&2, Nat>, s: Scope) -> St & Act:
  match s:
    case Turn{}:
      (St{live, base}, compare(newest(live)))
    case All{}:
      (St{live, base}, compare(base))

# the snapshots after `ev`, and its answer
def step(st: St, ev: Ev) -> St & Act:
  match st:
    case St{live, base}:
      match ev:
        case TurnStart{+t}:
          (St{t <> live, keep_base(base, t)}, Took{})
        case Undo{}:
          step.undo(live, base)
        case Diff{s}:
          step.diff(live, base, s)

# Rows
# ----

# one path: its content in the snapshot and in the workspace (a blob
# number, None when the path is absent), and whether it is held
type Row is Data:
  Row{before: Maybe<&2, Nat>, now: Maybe<&2, Nat>, held: Bool}

# what /undo does to a row's path
type Fix is Data:
  # leave it as it is
  Keep{}
  # delete it (added since the snapshot)
  Remove{}
  # write the snapshot's content (changed or removed since)
  Write{}

# what /diff says of a row's path
type Seen is Data:
  Same{}
  Differs{}
  # held: not compared
  Skipped{}

def same(a: Maybe<&2, Nat>, b: Maybe<&2, Nat>) -> Bool:
  match a b:
    case None{} None{}:
      True{}
    case None{} Some{y}:
      False{}
    case Some{x} None{}:
      False{}
    case Some{x} Some{y}:
      Nat.is_eq(x, y)

def fix.changed(before: Maybe<&2, Nat>, changed: Bool) -> Fix:
  match before:
    case None{}:
      match changed:
        case False{}:
          Keep{}
        case True{}:
          Remove{}
    case Some{b}:
      match changed:
        case False{}:
          Keep{}
        case True{}:
          Write{}

# what /undo does to one row
def fix(r: Row) -> Fix:
  match r:
    case Row{+b, n, h}:
      match h:
        case True{}:
          Keep{}
        case False{}:
          fix.changed(b, Bool.not(same(b, n)))

# what /undo does to each row, in order
def fixes(rows: List<&2, Row>) -> List<&2, Fix>:
  match rows:
    case Nil{}:
      Nil{}
    case Con{r, t}:
      fix(r) <> fixes(t)

def seen.of(f: Fix) -> Seen:
  match f:
    case Keep{}:
      Same{}
    case Remove{}:
      Differs{}
    case Write{}:
      Differs{}

# what /diff says of one row: a row /undo would change differs
def seen(r: Row) -> Seen:
  match r:
    case Row{b, n, h}:
      match h:
        case True{}:
          Skipped{}
        case False{}:
          seen.of(fix(Row{b, n, False{}}))

# what /diff says of each row, in order
def seens(rows: List<&2, Row>) -> List<&2, Seen>:
  match rows:
    case Nil{}:
      Nil{}
    case Con{r, t}:
      seen(r) <> seens(t)
