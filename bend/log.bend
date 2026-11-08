# log: the rules of the commit log of a durable storage, `main.jsonl`
# (crates/eukhe-durable/src/storage/jsonl/storage.rs, `JsonlStorage`),
# that JsonlStorage runs through the compiled core (entry
# bend/ffi_log.bend; Rust storage/jsonl/plan.rs). The laws (laws/log.bend)
# state they refine the model of the log under power loss (spec/durable/log.bend).
#
# `tail`: what an open does with a file (main.jsonl or a sidecar) from the
# facts Rust reads of it: its length and where its last newline is. Rust
# keeps the file whole, or cuts it to the bytes of its complete lines,
# and reads the complete lines.
#
# `Store`, `Store.open`, `Store.commit`: the plan of the storage, the steps
# (`Act`) JsonlStorage does, in order: at open, and per commit, from the
# durability of the directory entries of the commit's sidecar files (Rust
# keeps which entries it made durable) and of main.jsonl (the Store keeps
# it). A commit is acknowledged at its plan's Ack; a step that fails
# poisons the storage, so no later plan runs.

import Base

# The open of a file
# ------------------

# what an open does with a file: keep it whole (every byte is in a
# complete line), cut it to its first `to` bytes (the bytes after its last
# newline are a torn tail), or refuse facts no file has (a newline at or
# past its end)
type Tail is Data:
  Whole{}
  Torn{to: Nat}
  Odd{}

# the complete lines end at `to`: the whole file when that is its length
def tail.at(same: Bool, to: Nat) -> Tail:
  match same:
    case True{}:
      Whole{}
    case False{}:
      Torn{to}

def tail.in(inside: Bool, +len: Nat, +to: Nat) -> Tail:
  match inside:
    case True{}:
      tail.at(Nat.is_eq(to, len), to)
    case False{}:
      Odd{}

# the open of a file of len bytes whose last newline is at the index last
# (None: it has none)
def tail(+len: Nat, last: Maybe<&2, Nat>) -> Tail:
  match last:
    case None{}:
      tail.at(Nat.is_eq(0n, len), 0n)
    case Some{i}:
      +to = {1n+i : Nat}
      tail.in(Nat.is_le(to, len), len, to)

# The plan
# --------

# a step of JsonlStorage
type Act is Data:
  FlushParent{}         # flush the storage directory's parent (its entry)
  AppendSide{i: Nat}    # append the records of the commit's sidecar i
  FlushSide{i: Nat}     # flush the commit's sidecar i
  FlushDir{}            # flush the storage directory (its files' entries)
  AppendMain{}          # append the commit's marker to main.jsonl
  FlushMain{}           # flush main.jsonl
  Ack{}                 # acknowledge the commit

# the storage: fsync on, and main.jsonl's directory entry durable
type Store is Data:
  Store{fsync: Bool, main: Bool}

# a plan: the storage after it, and its steps in order
type Plan is Data:
  Plan{st: Store, acts: List<&2, Act>}

# a flush of the storage directory before rest, when an entry needs it
def plan.dir(need: Bool, rest: List<&2, Act>) -> List<&2, Act>:
  match need:
    case True{}:
      FlushDir{} <> rest
    case False{}:
      rest

# the appends of the sidecars from the i-th, then rest
def plan.appends(ds: List<&2, Bool>, +i: Nat, rest: List<&2, Act>) -> List<&2, Act>:
  match ds:
    case Nil{}:
      rest
    case d <> more:
      AppendSide{i} <> plan.appends(more, 1n+i, rest)

# the flushes of the sidecars from the i-th, then rest
def plan.flushes(ds: List<&2, Bool>, +i: Nat, rest: List<&2, Act>) -> List<&2, Act>:
  match ds:
    case Nil{}:
      rest
    case d <> more:
      FlushSide{i} <> plan.flushes(more, 1n+i, rest)

# some sidecar's directory entry is not durable
def plan.fresh(ds: List<&2, Bool>) -> Bool:
  match ds:
    case Nil{}:
      False{}
    case d <> more:
      match d:
        case True{}:
          plan.fresh(more)
        case False{}:
          True{}

# the open of a storage: with fsync, its directory's entry is made durable
def Store.open(fsync: Bool) -> Plan:
  match fsync:
    case True{}:
      Plan{Store{True{}, False{}}, [FlushParent{}]}
    case False{}:
      Plan{Store{False{}, False{}}, Nil{}}

# a commit whose sidecar files have the durable directory entries ds (in
# the commit's order): its records, then its marker, then the ack. With
# fsync, every file is flushed, and the storage directory too while an
# entry is not durable, before the marker that depends on it and before
# the ack; main.jsonl's entry is durable after it
def Store.commit(s: Store, +ds: List<&2, Bool>) -> Plan:
  match s:
    case Store{fsync, main}:
      match fsync:
        case False{}:
          Plan{Store{False{}, main}, plan.appends(ds, 0n, [AppendMain{}, Ack{}])}
        case True{}:
          Plan{Store{True{}, True{}}, plan.appends(ds, 0n, plan.flushes(ds, 0n, plan.dir(plan.fresh(ds), AppendMain{} <> FlushMain{} <> plan.dir(Bool.not(main), [Ack{}]))))}
