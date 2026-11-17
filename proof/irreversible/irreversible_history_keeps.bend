# eukhe: the proof of LAW irreversible_history_keeps
#
# PROOF: one record leaves the ledger with nothing or its entry appended
# (LA.irb.keep_known, LA.irb.keep_new); by induction on the records, the
# appended pieces join (LA.irb.app_assoc).

import Base
import ../../bend/irreversible.bend as Ir
import ../../laws/irreversible.bend as Irreversible
import ./base.bend as LA

# the ledger after one record: es with u appended
def ihk.keep(+es: List<&2, Ir.Entry>, +k: Nat, +r: Nat, b: Bool, eb: {Irreversible.ir_has(es, k) == b : Bool}) -> Sigma<&1, &1, List<&2, Ir.Entry>, u => {Ir.keep(es, k, r) == List.append(&2, Ir.Entry, es, u) : List<&2, Ir.Entry>}>:
  match b:
    case True{}:
      (Nil{}, Equal.trans(List<&2, Ir.Entry>, Ir.keep(es, k, r), es, List.append(&2, Ir.Entry, es, Nil{}), LA.irb.keep_known(es, k, r, eb), Equal.sym(List<&2, Ir.Entry>, List.append(&2, Ir.Entry, es, Nil{}), es, LA.irb.app_nil(Ir.Entry, es))))
    case False{}:
      ([Ir.Entry{k, r}], LA.irb.keep_new(es, k, r, eb))

def ihk.step(+es: List<&2, Ir.Entry>, +k: Nat, +r: Nat, +rest: List<&2, Ir.Entry>, s: Sigma<&1, &1, List<&2, Ir.Entry>, u => {Ir.keep(es, k, r) == List.append(&2, Ir.Entry, es, u) : List<&2, Ir.Entry>}>, ih: Sigma<&1, &1, List<&2, Ir.Entry>, t => {Ir.history(rest, Ir.keep(es, k, r)) == List.append(&2, Ir.Entry, Ir.keep(es, k, r), t) : List<&2, Ir.Entry>}>) -> Sigma<&1, &1, List<&2, Ir.Entry>, t => {Ir.history(rest, Ir.keep(es, k, r)) == List.append(&2, Ir.Entry, es, t) : List<&2, Ir.Entry>}>:
  match s:
    case (+u, eu):
      match ih:
        case (+t, et):
          +kp = Ir.keep(es, k, r)
          (List.append(&2, Ir.Entry, u, t), Equal.trans(List<&2, Ir.Entry>, Ir.history(rest, kp), List.append(&2, Ir.Entry, kp, t), List.append(&2, Ir.Entry, es, List.append(&2, Ir.Entry, u, t)), et, Equal.trans(List<&2, Ir.Entry>, List.append(&2, Ir.Entry, kp, t), List.append(&2, Ir.Entry, List.append(&2, Ir.Entry, es, u), t), List.append(&2, Ir.Entry, es, List.append(&2, Ir.Entry, u, t)), Equal.cong(List<&2, Ir.Entry>, List<&2, Ir.Entry>, z => List.append(&2, Ir.Entry, z, t), kp, List.append(&2, Ir.Entry, es, u), eu), LA.irb.app_assoc(Ir.Entry, es, u, t))))

def ihk.go(ops: List<&2, Ir.Entry>, +es: List<&2, Ir.Entry>) -> Sigma<&1, &1, List<&2, Ir.Entry>, t => {Ir.history(ops, es) == List.append(&2, Ir.Entry, es, t) : List<&2, Ir.Entry>}>:
  match ops:
    case Nil{}:
      (Nil{}, Equal.sym(List<&2, Ir.Entry>, List.append(&2, Ir.Entry, es, Nil{}), es, LA.irb.app_nil(Ir.Entry, es)))
    case op <> +rest:
      match op:
        case Ir.Entry{+k, +r}:
          ihk.step(es, k, r, rest, ihk.keep(es, k, r, Irreversible.ir_has(es, k), {==}), ihk.go(rest, Ir.keep(es, k, r)))

def Irreversible.irreversible_history_keeps(ops, es):
  ihk.go(ops, es)
