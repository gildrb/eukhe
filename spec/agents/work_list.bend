# work_list (spec): what the laws of area work_list (laws/work_list.bend)
# speak of, over the types of bend/work_list.bend: the hand-back of a child
# given a list of items (an `rlm.split` half, an `rlm.spawn` help leaf or a
# worker's task, `worker_assign`). A spec: the shipped code never calls it.
#
# S1: an item is open when the child did not account it done (left with a
#     reason, or never accounted for).
# S2: the hand-back is finished exactly when no item is open.
# S3: a stopped hand-back names every open item and no other, each once,
#     in the parent's order.

import Base
import ../../bend/work_list.bend as Wl

# Numbers
# -------

def same(a: Nat, b: Nat) -> Bool:
  match a b:
    case 0n 0n:
      True{}
    case 0n 1n+y:
      False{}
    case 1n+x 0n:
      False{}
    case 1n+x 1n+y:
      same(x, y)

def le(a: Nat, b: Nat) -> Bool:
  match a b:
    case 0n b:
      True{}
    case 1n+x 0n:
      False{}
    case 1n+x 1n+y:
      le(x, y)

# Lists
# -----

# k is one of xs
def member(+k: Nat, xs: List<&2, Nat>) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case x <> t:
      Bool.or(same(k, x), member(k, t))

# every x of xs is at least lo and above the one before it
def rising(xs: List<&2, Nat>, lo: Nat) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case x <> t:
      +y = x
      Bool.and(le(lo, y), rising(t, 1n+y))

# the positions are in the parent's order, each once (S3)
def ascending(xs: List<&2, Nat>) -> Bool:
  rising(xs, 0n)

# The items
# ---------

# every item is done (S2)
def all_done(done: List<&2, Bool>) -> Bool:
  match done:
    case Nil{}:
      True{}
    case d <> t:
      Bool.and(d, all_done(t))

# the item at position k is open (S1)
def open_at(done: List<&2, Bool>, k: Nat) -> Bool:
  match done k:
    case Nil{} k:
      False{}
    case d <> t 0n:
      Bool.not(d)
    case d <> t 1n+j:
      open_at(t, j)

# The hand-back
# -------------

def finished(o: Wl.Outcome) -> Bool:
  match o:
    case Wl.Finished{}:
      True{}
    case Wl.Stopped{xs}:
      False{}

# the items a hand-back names left: none when finished
def left(o: Wl.Outcome) -> List<&2, Nat>:
  match o:
    case Wl.Finished{}:
      []
    case Wl.Stopped{xs}:
      xs
