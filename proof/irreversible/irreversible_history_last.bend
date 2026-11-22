# eukhe: the proof of LAW irreversible_history_last
#
# PROOF: by induction on ops, the ledger generalized. No ops left: the
# last record is one keep on es, which appends k in run r when es lacks k
# (LA.irb.keep_new) and leaves es when it holds k (LA.irb.keep_known,
# LA.irb.app_nil). One op first: both sides go on from the ledger that op
# leaves, which is the induction hypothesis.

import Base
import ../../bend/irreversible.bend as Ir
import ../../laws/irreversible.bend as Irreversible
import ./base.bend as LA

# one record on es adds what ir_added says, b being whether es holds k
def ihl.keep(+es: List<&2, Ir.Entry>, +k: Nat, +r: Nat, b: Bool, eb: {Irreversible.ir_has(es, k) == b : Bool}) -> {Ir.keep(es, k, r) == List.append(&2, Ir.Entry, es, Irreversible.ir_added(b, k, r)) : List<&2, Ir.Entry>}:
  match b:
    case True{}:
      Equal.trans(List<&2, Ir.Entry>, Ir.keep(es, k, r), es, List.append(&2, Ir.Entry, es, Nil{}), LA.irb.keep_known(es, k, r, eb), Equal.sym(List<&2, Ir.Entry>, List.append(&2, Ir.Entry, es, Nil{}), es, LA.irb.app_nil(Ir.Entry, es)))
    case False{}:
      LA.irb.keep_new(es, k, r, eb)

def ihl.go(ops: List<&2, Ir.Entry>, +es: List<&2, Ir.Entry>, +k: Nat, +r: Nat) -> {Ir.history(List.append(&2, Ir.Entry, ops, [Ir.Entry{k, r}]), es) == List.append(&2, Ir.Entry, Ir.history(ops, es), Irreversible.ir_added(Irreversible.ir_has(Ir.history(ops, es), k), k, r)) : List<&2, Ir.Entry>}:
  match ops:
    case Nil{}:
      ihl.keep(es, k, r, Irreversible.ir_has(es, k), {==})
    case op <> rest:
      match op:
        case Ir.Entry{+j, +q}:
          ihl.go(rest, Ir.keep(es, j, q), k, r)

def Irreversible.irreversible_history_last(ops, es, k, r):
  ihl.go(ops, es, k, r)
