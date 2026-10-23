# eukhe: the proof of LAW rmw_keeps_others

import Base
import ../../bend/config.bend as Cf
import ../../LAWS.bend as Laws
import ../base.bend as L
import ./base.bend as LA

# one entry of key i before rest, b saying whether i is k
def pcf.del_step(b: Bool, +i: Nat, v: Nat, +rest: List<&2, Cf.Entry>, +k: Nat, +j: Nat, eb: {Nat.is_eq(i, k) == b : Bool}, h: {Nat.is_eq(k, j) == False{} : Bool}, ih: {Cf.lookup(Cf.del(rest, k), j) == Cf.lookup(rest, j) : Maybe<&2, Nat>}) -> {Cf.lookup(Cf.keep(b, Cf.Entry{i, v}, Cf.del(rest, k)), j) == Cf.pick(Nat.is_eq(i, j), v, Cf.lookup(rest, j)) : Maybe<&2, Nat>}:
  match b:
    case True{}:
      %Equal.sym(Nat, i, k, L.ppr.nat_eq_true(i, k, eb)) : {Cf.lookup(Cf.del(rest, k), j) == Cf.pick(Nat.is_eq(_, j), v, Cf.lookup(rest, j)) : Maybe<&2, Nat>}
      %Equal.sym(Bool, Nat.is_eq(k, j), False{}, h) : {Cf.lookup(Cf.del(rest, k), j) == Cf.pick(_, v, Cf.lookup(rest, j)) : Maybe<&2, Nat>}
      ih
    case False{}:
      %ih : {Cf.pick(Nat.is_eq(i, j), v, Cf.lookup(Cf.del(rest, k), j)) == Cf.pick(Nat.is_eq(i, j), v, _) : Maybe<&2, Nat>}
      {==}

# a delete of key k keeps the first entry of every other key j
def pcf.del_keeps(d: List<&2, Cf.Entry>, +k: Nat, +j: Nat, +h: {Nat.is_eq(k, j) == False{} : Bool}) -> {Cf.lookup(Cf.del(d, k), j) == Cf.lookup(d, j) : Maybe<&2, Nat>}:
  match d:
    case Nil{}:
      {==}
    case x <> +rest:
      match x:
        case Cf.Entry{+i, v}:
          pcf.del_step(Nat.is_eq(i, k), i, v, rest, k, j, {==}, h, pcf.del_keeps(rest, k, j, h))

# LAW rmw_keeps_others: an edit of key k keeps every other key j
def pcf.rmw_keeps_others(+d: List<&2, Cf.Entry>, +e: Cf.Edit, +j: Nat, +h: {Cf.touches(e, j) == False{} : Bool}) -> {Cf.kept(Cf.rmw(Cf.Parsed{d}, e), j) == Cf.lookup(d, j) : Maybe<&2, Nat>}:
  match e:
    case Cf.Set{+k, v}:
      %Equal.sym(Maybe<&2, Nat>, Cf.pick(Nat.is_eq(k, j), v, Cf.lookup(Cf.del(d, k), j)), Cf.lookup(Cf.del(d, k), j), LA.pcf.pick_false(Nat.is_eq(k, j), v, Cf.lookup(Cf.del(d, k), j), h)) : {_ == Cf.lookup(d, j) : Maybe<&2, Nat>}
      pcf.del_keeps(d, k, j, h)
    case Cf.Del{+k}:
      pcf.del_keeps(d, k, j, h)

def Laws.rmw_keeps_others(d, e, j, h):
  pcf.rmw_keeps_others(d, e, j, h)
