# eukhe: the proof of LAW rmw_values_kept
# A set replaces values in place (an entry of j is never one of k) or
# puts its entry last (of key k, not j); a delete drops only entries of
# k. Inductions on the document.

import Base
import ../../bend/config.bend as Cf
import ../../laws/config.bend as Config
import ../base/logic/logic.bend as LLogicLogic
import ./base/config.bend as LA

def pvk.rep.step(bj: Bool, bk: Bool, v: Nat, w: Nat, r1: List<&2, Nat>, r2: List<&2, Nat>, ih: {r1 == r2 : List<&2, Nat>}, no: {Bool.and(bk, bj) == False{} : Bool}) -> {Config.cf_vals.put(bj, Cf.pick_v(bk, v, w), r1) == Config.cf_vals.put(bj, w, r2) : List<&2, Nat>}:
  match bj:
    case True{}:
      match bk:
        case True{}:
          LLogicLogic.ppr.absurd({Config.cf_vals.put(True{}, Cf.pick_v(True{}, v, w), r1) == Config.cf_vals.put(True{}, w, r2) : List<&2, Nat>}, no)
        case False{}:
          %ih : {w <> r1 == w <> _ : List<&2, Nat>}
          {==}
    case False{}:
      ih

# a replace of key k keeps the values of every other key j
def pvk.rep(d: List<&2, Cf.Entry>, +k: Nat, +v: Nat, +j: Nat, +h: {Nat.is_eq(k, j) == False{} : Bool}) -> {Config.cf_vals(Cf.replace(d, k, v), j) == Config.cf_vals(d, j) : List<&2, Nat>}:
  match d:
    case Nil{}:
      {==}
    case e <> +t:
      match e:
        case Cf.Entry{+i, w}:
          pvk.rep.step(Nat.is_eq(i, j), Nat.is_eq(i, k), v, w, Config.cf_vals(Cf.replace(t, k, v), j), Config.cf_vals(t, j), pvk.rep(t, k, v, j, h), LA.pcf.not_both.go(Nat.is_eq(i, k), i, j, k, {==}, h))

# an entry of key k put last keeps the values of every other key j
def pvk.app(d: List<&2, Cf.Entry>, +k: Nat, +v: Nat, +j: Nat, +h: {Nat.is_eq(k, j) == False{} : Bool}) -> {Config.cf_vals(List.append(&2, Cf.Entry, d, [Cf.Entry{k, v}]), j) == Config.cf_vals(d, j) : List<&2, Nat>}:
  match d:
    case Nil{}:
      %Equal.sym(Bool, Nat.is_eq(k, j), False{}, h) : {Config.cf_vals.put(_, v, Nil{}) == Nil{} : List<&2, Nat>}
      {==}
    case e <> +t:
      match e:
        case Cf.Entry{+i, w}:
          %pvk.app(t, k, v, j, h) : {Config.cf_vals.put(Nat.is_eq(i, j), w, Config.cf_vals(List.append(&2, Cf.Entry, t, [Cf.Entry{k, v}]), j)) == Config.cf_vals.put(Nat.is_eq(i, j), w, _) : List<&2, Nat>}
          {==}

def pvk.set(b: Bool, +d: List<&2, Cf.Entry>, +k: Nat, +v: Nat, +j: Nat, +h: {Nat.is_eq(k, j) == False{} : Bool}) -> {Config.cf_vals(Cf.set.go(b, d, k, v), j) == Config.cf_vals(d, j) : List<&2, Nat>}:
  match b:
    case True{}:
      pvk.rep(d, k, v, j, h)
    case False{}:
      pvk.app(d, k, v, j, h)

def pvk.del.step(bk: Bool, +i: Nat, w: Nat, r1: List<&2, Cf.Entry>, r2: List<&2, Nat>, +j: Nat, ih: {Config.cf_vals(r1, j) == r2 : List<&2, Nat>}, no: {Bool.and(bk, Nat.is_eq(i, j)) == False{} : Bool}) -> {Config.cf_vals(Cf.keep(bk, Cf.Entry{i, w}, r1), j) == Config.cf_vals.put(Nat.is_eq(i, j), w, r2) : List<&2, Nat>}:
  match bk:
    case True{}:
      %Equal.sym(Bool, Nat.is_eq(i, j), False{}, no) : {Config.cf_vals(r1, j) == Config.cf_vals.put(_, w, r2) : List<&2, Nat>}
      ih
    case False{}:
      %ih : {Config.cf_vals.put(Nat.is_eq(i, j), w, Config.cf_vals(r1, j)) == Config.cf_vals.put(Nat.is_eq(i, j), w, _) : List<&2, Nat>}
      {==}

# a delete of key k keeps the values of every other key j
def pvk.del(d: List<&2, Cf.Entry>, +k: Nat, +j: Nat, +h: {Nat.is_eq(k, j) == False{} : Bool}) -> {Config.cf_vals(Cf.del(d, k), j) == Config.cf_vals(d, j) : List<&2, Nat>}:
  match d:
    case Nil{}:
      {==}
    case e <> +t:
      match e:
        case Cf.Entry{+i, w}:
          pvk.del.step(Nat.is_eq(i, k), i, w, Cf.del(t, k), Config.cf_vals(t, j), j, pvk.del(t, k, j, h), LA.pcf.not_both.go(Nat.is_eq(i, k), i, j, k, {==}, h))

def Config.rmw_values_kept(d, e, j, other):
  match e:
    case Cf.Set{+k, +v}:
      %pvk.set(Cf.has_key(d, k), d, k, v, j, other) : {Some{Config.cf_vals(Cf.set.go(Cf.has_key(d, k), d, k, v), j)} == Some{_} : Maybe<&2, List<&2, Nat>>}
      {==}
    case Cf.Del{+k}:
      %pvk.del(d, k, j, other) : {Some{Config.cf_vals(Cf.del(d, k), j)} == Some{_} : Maybe<&2, List<&2, Nat>>}
      {==}
