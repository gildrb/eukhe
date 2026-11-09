# eukhe: the proof of LAW store_write_lands
#
# PROOF: one write is the store's step; run by the gate, it is the write
# at its real path k, and the first cell at k after a write at k holds the
# written value (psl.set, by induction on the cells: the first cell at k
# takes the value, else a new cell goes at the end).

import Base
import ../../bend/path_policy.bend as Pp
import ../../bend/tools.bend as Tl
import ../../laws/path_policy/policy.bend as PathPolicy
import ../../laws/path_policy/gate.bend as PathPolicyGate
import ./base.bend as LA
import ./base/root.bend as LAR

# a path is the same path as itself
def psl.same_refl(+xs: List<&2, Nat>) -> {PathPolicy.pp_same(xs, xs) == True{} : Bool}:
  Equal.trans(Bool, PathPolicy.pp_same(xs, xs), Tl.ids.eq(xs, xs), True{}, Equal.sym(Bool, Tl.ids.eq(xs, xs), PathPolicy.pp_same(xs, xs), LA.pp.ids_same(xs, xs)), LAR.pc.ids_refl(xs))

def psl.set_pick(b: Bool, +a: List<&2, Nat>, +w: Nat, +rest: List<&2, Pp.Cell>, +k: List<&2, Nat>, +v: Nat, e: {Tl.ids.eq(a, k) == b : Bool}, ih: {PathPolicy.pp_cell(Pp.set(rest, k, v), k) == Some{v} : Maybe<&2, Nat>}) -> {PathPolicy.pp_cell(Pp.set.pick(b, Pp.Cell{a, w}, k, v, rest, Pp.set(rest, k, v)), k) == Some{v} : Maybe<&2, Nat>}:
  match b:
    case True{}:
      %Equal.sym(Bool, PathPolicy.pp_same(k, k), True{}, psl.same_refl(k)) : {PathPolicy.pp_cell_pick(_, v, PathPolicy.pp_cell(rest, k)) == Some{v} : Maybe<&2, Nat>}
      {==}
    case False{}:
      +ns = Equal.trans(Bool, PathPolicy.pp_same(a, k), Tl.ids.eq(a, k), False{}, Equal.sym(Bool, Tl.ids.eq(a, k), PathPolicy.pp_same(a, k), LA.pp.ids_same(a, k)), e)
      %Equal.sym(Bool, PathPolicy.pp_same(a, k), False{}, ns) : {PathPolicy.pp_cell_pick(_, w, PathPolicy.pp_cell(Pp.set(rest, k, v), k)) == Some{v} : Maybe<&2, Nat>}
      ih

# after a write of v at k, the first cell at k holds v
def psl.set(cs: List<&2, Pp.Cell>, +k: List<&2, Nat>, +v: Nat) -> {PathPolicy.pp_cell(Pp.set(cs, k, v), k) == Some{v} : Maybe<&2, Nat>}:
  match cs:
    case Nil{}:
      %Equal.sym(Bool, PathPolicy.pp_same(k, k), True{}, psl.same_refl(k)) : {PathPolicy.pp_cell_pick(_, v, None{}) == Some{v} : Maybe<&2, Nat>}
      {==}
    case c <> +rest:
      match c:
        case Pp.Cell{+a, +w}:
          psl.set_pick(Tl.ids.eq(a, k), a, w, rest, k, v, {==}, psl.set(rest, k, v))

def PathPolicyGate.store_write_lands(pol, ls, auto, cs, segs, v, ans, ran):
  %Equal.sym(Bool, Pp.runs(Pp.class(pol, ls, segs), Pp.Wr{}, auto, ans), True{}, ran) : {PathPolicy.pp_cell(Pp.put.pick(_, cs, Pp.Res.at(Pp.real(ls, segs)), v), Pp.Res.at(Pp.real(ls, segs))) == Some{v} : Maybe<&2, Nat>}
  psl.set(cs, Pp.Res.at(Pp.real(ls, segs)), v)
