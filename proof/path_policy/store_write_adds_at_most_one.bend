# eukhe: the proof of LAW store_write_adds_at_most_one
#
# PROOF: one write is the store's step: refused, the store is as it was
# (n <= n + 1); run, a write replaces the first cell at its path or adds
# one cell at the end (psa.set, by induction on the cells).

import Base
import ../../bend/path_policy.bend as Pp
import ../../bend/tools.bend as Tl
import ../../laws/path_policy/gate.bend as PathPolicyGate

def psa.le_succ(n: Nat) -> {Nat.is_le(n, 1n+n) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+k:
      psa.le_succ(k)

# one cell of a write, by the head test b
def psa.set_pick(b: Bool, +c: Pp.Cell, +rest: List<&2, Pp.Cell>, +k: List<&2, Nat>, +v: Nat, ih: {Nat.is_le(List.length(&2, Pp.Cell, Pp.set(rest, k, v)), 1n+List.length(&2, Pp.Cell, rest)) == True{} : Bool}) -> {Nat.is_le(List.length(&2, Pp.Cell, Pp.set.pick(b, c, k, v, rest, Pp.set(rest, k, v))), 1n+List.length(&2, Pp.Cell, c <> rest)) == True{} : Bool}:
  match b:
    case True{}:
      psa.le_succ(1n+List.length(&2, Pp.Cell, rest))
    case False{}:
      ih

# a write adds at most one cell
def psa.set(cs: List<&2, Pp.Cell>, +k: List<&2, Nat>, +v: Nat) -> {Nat.is_le(List.length(&2, Pp.Cell, Pp.set(cs, k, v)), 1n+List.length(&2, Pp.Cell, cs)) == True{} : Bool}:
  match cs:
    case Nil{}:
      {==}
    case +c <> +rest:
      psa.set_pick(Tl.ids.eq(Pp.Cell.at(c), k), c, rest, k, v, psa.set(rest, k, v))

# one write, by the gate's verdict b
def psa.pick(b: Bool, +cs: List<&2, Pp.Cell>, +k: List<&2, Nat>, +v: Nat) -> {Nat.is_le(List.length(&2, Pp.Cell, Pp.put.pick(b, cs, k, v)), 1n+List.length(&2, Pp.Cell, cs)) == True{} : Bool}:
  match b:
    case True{}:
      psa.set(cs, k, v)
    case False{}:
      psa.le_succ(List.length(&2, Pp.Cell, cs))

def PathPolicyGate.store_write_adds_at_most_one(pol, ls, auto, cs, segs, v, ans):
  psa.pick(Pp.runs(Pp.class(pol, ls, segs), Pp.Wr{}, auto, ans), cs, Pp.Res.at(Pp.real(ls, segs)), v)
