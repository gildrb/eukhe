# eukhe: the proof of LAW rmw_set_every_entry
# A set of a key the document has gives each entry of the key the value;
# a set of a new key puts the one entry of the key last.

import Base
import ../../bend/config.bend as Cf
import ../../laws/config.bend as Config
import ../base/logic/logic.bend as LLogicLogic
import ../base/nat.bend as LNat

def pse.rep.step(b: Bool, +v: Nat, w: Nat, r: List<&2, Nat>, ih: {Config.cf_all_v(r, v) == True{} : Bool}) -> {Config.cf_all_v(Config.cf_vals.put(b, Cf.pick_v(b, v, w), r), v) == True{} : Bool}:
  match b:
    case True{}:
      %Equal.sym(Bool, Nat.is_eq(v, v), True{}, LNat.ppr.nat_eq_refl(v)) : {Bool.and(_, Config.cf_all_v(r, v)) == True{} : Bool}
      ih
    case False{}:
      ih

# a replace of key k gives every entry of k the value v
def pse.rep(d: List<&2, Cf.Entry>, +k: Nat, +v: Nat) -> {Config.cf_all_v(Config.cf_vals(Cf.replace(d, k, v), k), v) == True{} : Bool}:
  match d:
    case Nil{}:
      {==}
    case e <> +t:
      match e:
        case Cf.Entry{+i, w}:
          pse.rep.step(Nat.is_eq(i, k), v, w, Config.cf_vals(Cf.replace(t, k, v), k), pse.rep(t, k, v))

def pse.or_l(a: Bool, -b: Bool, h: {Bool.or(a, b) == False{} : Bool}) -> {a == False{} : Bool}:
  match a:
    case True{}:
      LLogicLogic.ppr.absurd({True{} == False{} : Bool}, h)
    case False{}:
      {==}

def pse.or_r(a: Bool, -b: Bool, h: {Bool.or(a, b) == False{} : Bool}) -> {b == False{} : Bool}:
  match a:
    case True{}:
      LLogicLogic.ppr.absurd({b == False{} : Bool}, h)
    case False{}:
      h

# a document without key k, its entry put last: the one entry of k holds v
def pse.app(d: List<&2, Cf.Entry>, +k: Nat, +v: Nat, +h: {Cf.has_key(d, k) == False{} : Bool}) -> {Config.cf_all_v(Config.cf_vals(List.append(&2, Cf.Entry, d, [Cf.Entry{k, v}]), k), v) == True{} : Bool}:
  match d:
    case Nil{}:
      %Equal.sym(Bool, Nat.is_eq(k, k), True{}, LNat.ppr.nat_eq_refl(k)) : {Config.cf_all_v(Config.cf_vals.put(_, v, Nil{}), v) == True{} : Bool}
      %Equal.sym(Bool, Nat.is_eq(v, v), True{}, LNat.ppr.nat_eq_refl(v)) : {Bool.and(_, True{}) == True{} : Bool}
      {==}
    case e <> +t:
      match e:
        case Cf.Entry{+i, w}:
          %Equal.sym(Bool, Nat.is_eq(i, k), False{}, pse.or_l(Nat.is_eq(i, k), Cf.has_key(t, k), h)) : {Config.cf_all_v(Config.cf_vals.put(_, w, Config.cf_vals(List.append(&2, Cf.Entry, t, [Cf.Entry{k, v}]), k)), v) == True{} : Bool}
          pse.app(t, k, v, pse.or_r(Nat.is_eq(i, k), Cf.has_key(t, k), h))

def pse.set(b: Bool, +d: List<&2, Cf.Entry>, +k: Nat, +v: Nat, eb: {Cf.has_key(d, k) == b : Bool}) -> {Config.cf_all_v(Config.cf_vals(Cf.set.go(b, d, k, v), k), v) == True{} : Bool}:
  match b:
    case True{}:
      pse.rep(d, k, v)
    case False{}:
      pse.app(d, k, v, eb)

def Config.rmw_set_every_entry(d, k, v):
  pse.set(Cf.has_key(d, k), d, k, v, {==})
