# irreversible: the model of which effects are irreversible and of the
# ledger of the irreversible effects that ran (spec/README.md I1, I4, I6;
# laws/irreversible.bend states it). Rust:
# crates/eukhe-bend/src/rules/irreversible.rs through
# bend/ffi_irreversible.bend, asked when an effect runs (a `bash` step, a
# document tool's access, a `python` cell, an MCP call) and by the
# session's `eukhe.effects` ledger.
#
# 1. The classes. An effect is its class codes: 0 read, 1 write, 2 exec
#    (each inside the workspace), 3 net, 4 outside, 5 protected, 6
#    secret, 7 unknown; a code past 7 is unknown too. An effect is
#    irreversible exactly when one of its codes is none of read, write and
#    exec. Nothing else moves an effect across.
# 2. The ledger. Every irreversible effect that ran is one entry, in the
#    order they were recorded: its key (the place it ran, interned by
#    Rust) and the run it ran in. An entry's id is its place, from 1 (e1,
#    e2, ...): the ledger only grows at its end, so no id is reused.
#    Recording a key the ledger holds changes nothing and answers that
#    entry's id; a new key is appended last with the next id.
# 3. The end of a run: the ids of the entries recorded in that run, in
#    order.

import Base

# 1. The classes
# --------------

# the code is read, write or exec
def reversible.at(c: Nat) -> Bool:
  Nat.is_lt(c, 3n)

# some code of cs is not read, write or exec
def irreversible(cs: List<&2, Nat>) -> Bool:
  match cs:
    case Nil{}:
      False{}
    case c <> rest:
      Bool.or(Bool.not(reversible.at(c)), irreversible(rest))

# 2. The ledger
# -------------

# One entry: the effect's key and the run it ran in
type Entry is Data:
  Entry{key: Nat, run: Nat}

# What recording answers: the id of the new entry, or of the entry the
# key already has
type Recorded is Data:
  New{n: Nat}
  Known{n: Nat}

# the first entry of es has key k
def key.at(+es: List<&2, Entry>, +k: Nat) -> Bool:
  match es:
    case Nil{}:
      False{}
    case e <> rest:
      match e:
        case Entry{j, r}:
          Nat.is_eq(j, k)

# the id of the first entry of es with key k, counting the entries before
# es from `at`; None when no entry has k; hit is key.at(es, k)
def find.go(es: List<&2, Entry>, +k: Nat, at: Nat, hit: Bool) -> Maybe<&2, Nat>:
  match es:
    case Nil{}:
      None{}
    case e <> +rest:
      match hit:
        case True{}:
          Some{1n+at}
        case False{}:
          find.go(rest, k, 1n+at, key.at(rest, k))

def find(+es: List<&2, Entry>, +k: Nat, at: Nat) -> Maybe<&2, Nat>:
  find.go(es, k, at, key.at(es, k))

def record.of(m: Maybe<&2, Nat>, +es: List<&2, Entry>) -> Recorded:
  match m:
    case None{}:
      New{1n+List.length(&2, Entry, es)}
    case Some{n}:
      Known{n}

# what recording key k answers on the ledger es
def record(+es: List<&2, Entry>, +k: Nat) -> Recorded:
  record.of(find(es, k, 0n), es)

def keep.of(m: Maybe<&2, Nat>, es: List<&2, Entry>, +k: Nat, +r: Nat) -> List<&2, Entry>:
  match m:
    case None{}:
      List.append(&2, Entry, es, [Entry{k, r}])
    case Some{n}:
      es

# the ledger after recording key k in run r
def keep(+es: List<&2, Entry>, +k: Nat, +r: Nat) -> List<&2, Entry>:
  keep.of(find(es, k, 0n), es, k, r)

# 3. The end of a run
# -------------------

def report.add(hit: Bool, n: Nat, rest: List<&2, Nat>) -> List<&2, Nat>:
  match hit:
    case True{}:
      n <> rest
    case False{}:
      rest

# the ids of the entries of es recorded in run r, in order; the first
# entry of es has id 1+at
def report.go(es: List<&2, Entry>, +r: Nat, +at: Nat) -> List<&2, Nat>:
  match es:
    case Nil{}:
      Nil{}
    case e <> rest:
      match e:
        case Entry{k, q}:
          report.add(Nat.is_eq(q, r), 1n+at, report.go(rest, r, 1n+at))

# the end-of-run list of run r: the ids of its entries, in order
def report(es: List<&2, Entry>, +r: Nat) -> List<&2, Nat>:
  report.go(es, r, 0n)

# A history of the ledger: the effects recorded, in order (key, run)
def history(ops: List<&2, Entry>, es: List<&2, Entry>) -> List<&2, Entry>:
  match ops:
    case Nil{}:
      es
    case op <> rest:
      match op:
        case Entry{+k, +r}:
          history(rest, keep(es, k, r))