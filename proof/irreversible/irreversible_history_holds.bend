# eukhe: the proof of LAW irreversible_history_holds
#
# PROOF: after one record of key j, the ledger holds k exactly when it did
# or j is k: a new key is appended (LA.irb.keep_new, LA.irb.has_app), a
# known one leaves the ledger, which then holds j (LA.irb.keep_known,
# LA.irb.eq_true). By induction on the records (LA.irb.or_assoc).

import Base
import ../../bend/irreversible.bend as Ir
import ../../laws/irreversible.bend as Irreversible
import ./base.bend as LA

# a ledger holding j holds k when j is k (c: whether j is k)
def ihh.known(+es: List<&2, Ir.Entry>, +j: Nat, +k: Nat, hj: {Irreversible.ir_has(es, j) == True{} : Bool}, c: Bool, ec: {Nat.is_eq(j, k) == c : Bool}) -> {Irreversible.ir_has(es, k) == Bool.or(Irreversible.ir_has(es, k), c) : Bool}:
  match c:
    case False{}:
      Equal.sym(Bool, Bool.or(Irreversible.ir_has(es, k), False{}), Irreversible.ir_has(es, k), LA.irb.or_false(Irreversible.ir_has(es, k)))
    case True{}:
      +jk = LA.irb.eq_true(j, k, ec)
      +hk = Equal.trans(Bool, Irreversible.ir_has(es, k), Irreversible.ir_has(es, j), True{}, Equal.cong(Nat, Bool, z => Irreversible.ir_has(es, z), k, j, Equal.sym(Nat, j, k, jk)), hj)
      Equal.trans(Bool, Irreversible.ir_has(es, k), True{}, Bool.or(Irreversible.ir_has(es, k), True{}), hk, Equal.sym(Bool, Bool.or(Irreversible.ir_has(es, k), True{}), True{}, LA.irb.or_true_r(Irreversible.ir_has(es, k))))

# after recording j (b: whether the ledger held j), the ledger holds k
# exactly when it did or j is k
def ihh.keep(+es: List<&2, Ir.Entry>, +j: Nat, +r: Nat, +k: Nat, b: Bool, +eb: {Irreversible.ir_has(es, j) == b : Bool}) -> {Irreversible.ir_has(Ir.keep(es, j, r), k) == Bool.or(Irreversible.ir_has(es, k), Nat.is_eq(j, k)) : Bool}:
  match b:
    case False{}:
      +app = List.append(&2, Ir.Entry, es, [Ir.Entry{j, r}])
      %Equal.sym(List<&2, Ir.Entry>, Ir.keep(es, j, r), app, LA.irb.keep_new(es, j, r, eb)) : {Irreversible.ir_has(_, k) == Bool.or(Irreversible.ir_has(es, k), Nat.is_eq(j, k)) : Bool}
      %Equal.sym(Bool, Irreversible.ir_has(app, k), Bool.or(Irreversible.ir_has(es, k), Irreversible.ir_has([Ir.Entry{j, r}], k)), LA.irb.has_app(es, [Ir.Entry{j, r}], k)) : {_ == Bool.or(Irreversible.ir_has(es, k), Nat.is_eq(j, k)) : Bool}
      %Equal.sym(Bool, Bool.or(Nat.is_eq(j, k), False{}), Nat.is_eq(j, k), LA.irb.or_false(Nat.is_eq(j, k))) : {Bool.or(Irreversible.ir_has(es, k), _) == Bool.or(Irreversible.ir_has(es, k), Nat.is_eq(j, k)) : Bool}
      {==}
    case True{}:
      %Equal.sym(List<&2, Ir.Entry>, Ir.keep(es, j, r), es, LA.irb.keep_known(es, j, r, eb)) : {Irreversible.ir_has(_, k) == Bool.or(Irreversible.ir_has(es, k), Nat.is_eq(j, k)) : Bool}
      ihh.known(es, j, k, eb, Nat.is_eq(j, k), {==})

def ihh.go(ops: List<&2, Ir.Entry>, +es: List<&2, Ir.Entry>, +k: Nat) -> {Irreversible.ir_has(Ir.history(ops, es), k) == Bool.or(Irreversible.ir_has(es, k), Irreversible.ir_has(ops, k)) : Bool}:
  match ops:
    case Nil{}:
      Equal.sym(Bool, Bool.or(Irreversible.ir_has(es, k), False{}), Irreversible.ir_has(es, k), LA.irb.or_false(Irreversible.ir_has(es, k)))
    case op <> +rest:
      match op:
        case Ir.Entry{+j, +r}:
          +kp = Ir.keep(es, j, r)
          +hr = Irreversible.ir_has(rest, k)
          +he = Irreversible.ir_has(es, k)
          +hk = ihh.keep(es, j, r, k, Irreversible.ir_has(es, j), {==})
          +ih = ihh.go(rest, kp, k)
          Equal.trans(Bool, Irreversible.ir_has(Ir.history(rest, kp), k), Bool.or(Irreversible.ir_has(kp, k), hr), Bool.or(he, Bool.or(Nat.is_eq(j, k), hr)), ih, Equal.trans(Bool, Bool.or(Irreversible.ir_has(kp, k), hr), Bool.or(Bool.or(he, Nat.is_eq(j, k)), hr), Bool.or(he, Bool.or(Nat.is_eq(j, k), hr)), Equal.cong(Bool, Bool, z => Bool.or(z, hr), Irreversible.ir_has(kp, k), Bool.or(he, Nat.is_eq(j, k)), hk), Equal.sym(Bool, Bool.or(he, Bool.or(Nat.is_eq(j, k), hr)), Bool.or(Bool.or(he, Nat.is_eq(j, k)), hr), LA.irb.or_assoc(he, Nat.is_eq(j, k), hr))))

def Irreversible.irreversible_history_holds(ops, es, k):
  ihh.go(ops, es, k)
