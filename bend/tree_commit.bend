# tree_commit: the order in which the state tree records the changes of
# one commit (the Rust host is crates/eukhe-durable/src/tree/state.rs
# `StateTree::apply_commit`; the tree itself is bend/tree.bend). The
# changes of a commit come in no order: a Put waits until its parent is
# in the tree, and the Dels come last.
#
# The host interns the commit's keys to commit-local Nats and gives each
# change in commit order: a Put whose parent is the root or a node of the
# tree now (Here, its key), a Put whose parent is a key absent from the
# tree now (Under, its key and the parent's key), or a Del (Gone). A Put
# that applies makes its key present (the state tree's parents are
# conversations and tasks: never deleted, and the tree takes every Put of
# a new key, whose id is above every id); no Put removes a node.
#
# The answer is the order of the results, by change index: the Puts go in
# rounds over the waiting ones, in commit order: a Put applies when its
# parent is present now or is the key of a Put applied earlier in the
# commit (in this round or an earlier one); a round that applies nothing
# ends the rounds; each Put still waiting is an unknown parent; then each
# Del, in commit order (the host checks then whether its node is still in
# the tree: a Del removes the node's subtree, and the tree may refuse a
# Put). A waiting Put always has a parent key: a Put under the root is
# Here and applies in the first round.
#
# The rounds walk the changes in place: a mark per change says whether
# its Put applied. Pure: no IO, no @unsafe. laws/tree_commit.bend states
# its laws.

import Base

# Types
# -----

# a change of the commit
type Ch is Data:
  # a Put whose parent is the root or a node of the tree now
  Here{key: Nat}
  # a Put whose parent is the commit-local key up, absent from the tree now
  Under{key: Nat, up: Nat}
  # a Del
  Gone{}

# a result, by the index of its change in the commit
type Res is Data:
  # apply the Put
  Apply{i: Nat}
  # the Put's parent is not in the tree
  Orphan{i: Nat}
  # the Del
  Retire{i: Nat}

# a round: the Puts it applied, the marks after it, the keys present
# (the parents of Wait Puts that applied so far), whether it applied any
type Round is Data:
  Round{out: List<&2, Res>, ms: List<&2, Bool>, ready: List<&2, Nat>, hit: Bool}

# The rounds
# ----------

# the key u is among xs
def has(xs: List<&2, Nat>, +u: Nat) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case x <> t:
      Bool.or(Nat.is_eq(x, u), has(t, u))

# the change is a Put whose parent is present
def free(ready: List<&2, Nat>, c: Ch) -> Bool:
  match c:
    case Here{k}:
      True{}
    case Under{k, u}:
      has(ready, u)
    case Gone{}:
      False{}

def key(c: Ch) -> Nat:
  match c:
    case Here{k}:
      k
    case Under{k, u}:
      k
    case Gone{}:
      0n

# the keys present after change c: its key once its Put applied
def grow(b: Bool, k: Nat, ready: List<&2, Nat>) -> List<&2, Nat>:
  match b:
    case True{}:
      k <> ready
    case False{}:
      ready

# change i, after the round of the changes after it answered r: applied
# now (b), or as marked before (m)
def round.one(b: Bool, m: Bool, i: Nat, r: Round) -> Round:
  match b:
    case True{}:
      match r:
        case Round{out, ms, rd, hit}:
          Round{Apply{i} <> out, True{} <> ms, rd, True{}}
    case False{}:
      match r:
        case Round{out, ms, rd, hit}:
          Round{out, m <> ms, rd, hit}

# one round over the changes cs from index i, with the marks ms (a
# missing mark: not applied) and the keys present: each unmarked Put
# whose parent is present applies, and its key is present for the Puts
# after it
def round(cs: List<&2, Ch>, ms: List<&2, Bool>, +i: Nat, +ready: List<&2, Nat>) -> Round:
  match cs:
    case Nil{}:
      Round{[], [], ready, False{}}
    case +c <> t:
      match ms:
        case Nil{}:
          +b = free(ready, c)
          round.one(b, False{}, i, round(t, [], 1n+i, grow(b, key(c), ready)))
        case +m <> u:
          +b = Bool.and(Bool.not(m), free(ready, c))
          round.one(b, m, i, round(t, u, 1n+i, grow(b, key(c), ready)))

def orphans.mark(m: Bool, i: Nat, rest: List<&2, Res>) -> List<&2, Res>:
  match m:
    case True{}:
      rest
    case False{}:
      Orphan{i} <> rest

def orphans.one(c: Ch, m: Bool, i: Nat, rest: List<&2, Res>) -> List<&2, Res>:
  match c:
    case Here{k}:
      orphans.mark(m, i, rest)
    case Under{k, u}:
      orphans.mark(m, i, rest)
    case Gone{}:
      rest

# the Puts not applied, as unknown parents, in commit order
def orphans(cs: List<&2, Ch>, ms: List<&2, Bool>, +i: Nat) -> List<&2, Res>:
  match cs:
    case Nil{}:
      []
    case c <> t:
      match ms:
        case Nil{}:
          orphans.one(c, False{}, i, orphans(t, [], 1n+i))
        case m <> u:
          orphans.one(c, m, i, orphans(t, u, 1n+i))

# the Dels, in commit order
def retires(cs: List<&2, Ch>, +i: Nat) -> List<&2, Res>:
  match cs:
    case Nil{}:
      []
    case c <> t:
      match c:
        case Here{k}:
          retires(t, 1n+i)
        case Under{k, u}:
          retires(t, 1n+i)
        case Gone{}:
          Retire{i} <> retires(t, 1n+i)

# the rounds: r is the round over the marks ms; after a round that
# applies nothing (or after f rounds: never short, every round but the
# last applies a Put), the unknown parents, then the Dels
def rounds(f: Nat, +cs: List<&2, Ch>, ms: List<&2, Bool>, r: Round) -> List<&2, Res>:
  match f:
    case 0n:
      List.append(&2, Res, orphans(cs, ms, 0n), retires(cs, 0n))
    case 1n+g:
      match r:
        case Round{out, +ms2, rd, hit}:
          match hit:
            case True{}:
              List.append(&2, Res, out, rounds(g, cs, ms2, round(cs, ms2, 0n, rd)))
            case False{}:
              List.append(&2, Res, orphans(cs, ms2, 0n), retires(cs, 0n))

# the results of a commit's changes, in order
def order(+cs: List<&2, Ch>) -> List<&2, Res>:
  rounds(List.length(&2, Ch, cs), cs, [], round(cs, [], 0n, []))
