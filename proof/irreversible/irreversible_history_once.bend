# eukhe: the proof of LAW irreversible_history_once
#
# PROOF: a record of a known key leaves the ledger (LA.irb.keep_known); a
# new key is appended to a ledger that lacks it, and a ledger where each
# key appears once still has each key once with a key it lacks appended
# (iho.last: LA.irb.has_app, LA.irb.eq_comm). By induction on the
# records.

import Base
import ../../bend/irreversible.bend as Ir
import ../../laws/irreversible.bend as Irreversible
import ../base/staging.bend as LStg
import ./base.bend as LA

def iho.and_l(+a: Bool, -b: Bool, h: {Bool.and(a, b) == True{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      LStg.stg.absurdF({False{} == True{} : Bool}, h)

def iho.and_r(+a: Bool, -b: Bool, h: {Bool.and(a, b) == True{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case True{}:
      h
    case False{}:
      LStg.stg.absurdF({b == True{} : Bool}, h)

def iho.not_true(+a: Bool, h: {Bool.not(a) == True{} : Bool}) -> {a == False{} : Bool}:
  match a:
    case True{}:
      LStg.stg.absurdF({True{} == False{} : Bool}, h)
    case False{}:
      {==}

# each key once, and k not among them: each key still once with k last
def iho.last(es: List<&2, Ir.Entry>, +k: Nat, +r: Nat, +ho: {Irreversible.ir_once(es) == True{} : Bool}, +hn: {Irreversible.ir_has(es, k) == False{} : Bool}) -> {Irreversible.ir_once(List.append(&2, Ir.Entry, es, [Ir.Entry{k, r}])) == True{} : Bool}:
  match es:
    case Nil{}:
      {==}
    case e <> +t:
      match e:
        case Ir.Entry{+j, +q}:
          +x = {[Ir.Entry{k, r}] : List<&2, Ir.Entry>}
          +htj = iho.not_true(Irreversible.ir_has(t, j), iho.and_l(Bool.not(Irreversible.ir_has(t, j)), Irreversible.ir_once(t), ho))
          +hot = iho.and_r(Bool.not(Irreversible.ir_has(t, j)), Irreversible.ir_once(t), ho)
          +hjk = LA.irb.or_false_l(Nat.is_eq(j, k), Irreversible.ir_has(t, k), hn)
          +htk = LA.irb.or_false_r(Nat.is_eq(j, k), Irreversible.ir_has(t, k), hn)
          +hkj = Equal.trans(Bool, Nat.is_eq(k, j), Nat.is_eq(j, k), False{}, LA.irb.eq_comm(k, j), hjk)
          +e1 = LA.irb.has_app(t, x, j)
          +e2 = Equal.cong(Bool, Bool, z => Bool.or(z, Bool.or(Nat.is_eq(k, j), False{})), Irreversible.ir_has(t, j), False{}, htj)
          +e3 = Equal.cong(Bool, Bool, z => Bool.or(z, False{}), Nat.is_eq(k, j), False{}, hkj)
          +hx = Equal.trans(Bool, Irreversible.ir_has(List.append(&2, Ir.Entry, t, x), j), Bool.or(Irreversible.ir_has(t, j), Bool.or(Nat.is_eq(k, j), False{})), False{}, e1, Equal.trans(Bool, Bool.or(Irreversible.ir_has(t, j), Bool.or(Nat.is_eq(k, j), False{})), Bool.or(Nat.is_eq(k, j), False{}), False{}, e2, e3))
          %Equal.sym(Bool, Irreversible.ir_has(List.append(&2, Ir.Entry, t, x), j), False{}, hx) : {Bool.and(Bool.not(_), Irreversible.ir_once(List.append(&2, Ir.Entry, t, x))) == True{} : Bool}
          iho.last(t, k, r, hot, htk)

# one record keeps each key once (b: whether the ledger held k)
def iho.keep(+es: List<&2, Ir.Entry>, +k: Nat, +r: Nat, ho: {Irreversible.ir_once(es) == True{} : Bool}, b: Bool, +eb: {Irreversible.ir_has(es, k) == b : Bool}) -> {Irreversible.ir_once(Ir.keep(es, k, r)) == True{} : Bool}:
  match b:
    case True{}:
      %Equal.sym(List<&2, Ir.Entry>, Ir.keep(es, k, r), es, LA.irb.keep_known(es, k, r, eb)) : {Irreversible.ir_once(_) == True{} : Bool}
      ho
    case False{}:
      %Equal.sym(List<&2, Ir.Entry>, Ir.keep(es, k, r), List.append(&2, Ir.Entry, es, [Ir.Entry{k, r}]), LA.irb.keep_new(es, k, r, eb)) : {Irreversible.ir_once(_) == True{} : Bool}
      iho.last(es, k, r, ho, eb)

def iho.go(ops: List<&2, Ir.Entry>, +es: List<&2, Ir.Entry>, ho: {Irreversible.ir_once(es) == True{} : Bool}) -> {Irreversible.ir_once(Ir.history(ops, es)) == True{} : Bool}:
  match ops:
    case Nil{}:
      ho
    case op <> rest:
      match op:
        case Ir.Entry{+k, +r}:
          iho.go(rest, Ir.keep(es, k, r), iho.keep(es, k, r, ho, Irreversible.ir_has(es, k), {==}))

def Irreversible.irreversible_history_once(ops, es, once):
  iho.go(ops, es, once)
