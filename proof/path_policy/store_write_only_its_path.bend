# eukhe: the proof of LAW store_write_only_its_path
#
# PROOF: one write is the store's step: refused, the store is as it was;
# run, it is a write at the real path k, which keeps the content at every
# other location x (pso.cell_set), as x is not k
# (pso.not_same: the same path test of k and x would make them equal).

import Base
import ../../bend/path_policy.bend as Pp
import ../../bend/tools.bend as Tl
import ../../laws/path_policy/policy.bend as PathPolicy
import ../../laws/path_policy/gate.bend as PathPolicyGate
import ./base.bend as LA
import ./base/lemmas.bend as LAE
import ./gate_unasked_only_granted.bend as PGateUnaskedOnlyGranted

# one cell of a set at k, by the head test b
def pso.cell_set_pick(b: Bool, +a: List<&2, Nat>, +w: Nat, +rest: List<&2, Pp.Cell>, +k: List<&2, Nat>, +v: Nat, +at: List<&2, Nat>, e: {Tl.ids.eq(a, k) == b : Bool}, +hk: {PathPolicy.pp_same(k, at) == False{} : Bool}, ih: {PathPolicy.pp_cell(Pp.set(rest, k, v), at) == PathPolicy.pp_cell(rest, at) : Maybe<&2, Nat>}) -> {PathPolicy.pp_cell(Pp.set.pick(b, Pp.Cell{a, w}, k, v, rest, Pp.set(rest, k, v)), at) == PathPolicy.pp_cell(Pp.Cell{a, w} <> rest, at) : Maybe<&2, Nat>}:
  match b:
    case True{}:
      +same = LAE.pp.ids_sound(a, k, e)
      %Equal.sym(List<&2, Nat>, a, k, same) : {PathPolicy.pp_cell_pick(PathPolicy.pp_same(k, at), v, PathPolicy.pp_cell(rest, at)) == PathPolicy.pp_cell_pick(PathPolicy.pp_same(_, at), w, PathPolicy.pp_cell(rest, at)) : Maybe<&2, Nat>}
      %Equal.sym(Bool, PathPolicy.pp_same(k, at), False{}, hk) : {PathPolicy.pp_cell_pick(_, v, PathPolicy.pp_cell(rest, at)) == PathPolicy.pp_cell_pick(PathPolicy.pp_same(k, at), w, PathPolicy.pp_cell(rest, at)) : Maybe<&2, Nat>}
      %Equal.sym(Bool, PathPolicy.pp_same(k, at), False{}, hk) : {PathPolicy.pp_cell(rest, at) == PathPolicy.pp_cell_pick(_, w, PathPolicy.pp_cell(rest, at)) : Maybe<&2, Nat>}
      {==}
    case False{}:
      %ih : {PathPolicy.pp_cell_pick(PathPolicy.pp_same(a, at), w, PathPolicy.pp_cell(Pp.set(rest, k, v), at)) == PathPolicy.pp_cell_pick(PathPolicy.pp_same(a, at), w, _) : Maybe<&2, Nat>}
      {==}

# a write at a location that is not at keeps the content at at
def pso.cell_set(cs: List<&2, Pp.Cell>, +k: List<&2, Nat>, +v: Nat, +at: List<&2, Nat>, +hk: {PathPolicy.pp_same(k, at) == False{} : Bool}) -> {PathPolicy.pp_cell(Pp.set(cs, k, v), at) == PathPolicy.pp_cell(cs, at) : Maybe<&2, Nat>}:
  match cs:
    case Nil{}:
      %Equal.sym(Bool, PathPolicy.pp_same(k, at), False{}, hk) : {PathPolicy.pp_cell_pick(_, v, None{}) == None{} : Maybe<&2, Nat>}
      {==}
    case c <> +rest:
      match c:
        case Pp.Cell{+a, +w}:
          pso.cell_set_pick(Tl.ids.eq(a, k), a, w, rest, k, v, at, {==}, hk, pso.cell_set(rest, k, v, at, hk))

# k and x are not the same path, by the same path test b
def pso.not_same(b: Bool, +k: List<&2, Nat>, +x: List<&2, Nat>, e: {PathPolicy.pp_same(k, x) == b : Bool}, other: {x != k : List<&2, Nat>}) -> {PathPolicy.pp_same(k, x) == False{} : Bool}:
  match b:
    case True{}:
      +same = LAE.pp.ids_sound(k, x, Equal.trans(Bool, Tl.ids.eq(k, x), PathPolicy.pp_same(k, x), True{}, LA.pp.ids_same(k, x), e))
      PGateUnaskedOnlyGranted.pg.never({PathPolicy.pp_same(k, x) == False{} : Bool}, other(Equal.sym(List<&2, Nat>, k, x, same)))
    case False{}:
      e

# one write, by the gate's verdict b
def pso.pick(b: Bool, cs: List<&2, Pp.Cell>, +k: List<&2, Nat>, +v: Nat, +x: List<&2, Nat>, hk: {PathPolicy.pp_same(k, x) == False{} : Bool}) -> {PathPolicy.pp_cell(Pp.put.pick(b, cs, k, v), x) == PathPolicy.pp_cell(cs, x) : Maybe<&2, Nat>}:
  match b:
    case True{}:
      pso.cell_set(cs, k, v, x, hk)
    case False{}:
      {==}

def PathPolicyGate.store_write_only_its_path(pol, ls, auto, cs, segs, v, ans, x, other):
  +k = Pp.Res.at(Pp.real(ls, segs))
  pso.pick(Pp.runs(Pp.class(pol, ls, segs), Pp.Wr{}, auto, ans), cs, k, v, x, pso.not_same(PathPolicy.pp_same(k, x), k, x, {==}, other))
