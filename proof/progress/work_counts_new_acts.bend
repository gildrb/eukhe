# eukhe: the proof of LAW work_counts_new_acts
# PROOF: the ledger of xs ++ [x] reads x after the ledger of xs, which does
# not hold x (x is not an act of xs), so it adds x: one act more.

import Base
import ../../bend/ffi_progress.bend as FPr
import ../../bend/progress.bend as Pr
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/progress.bend as Progress
import ../base/nat.bend as LNat
import ./base.bend as LA

def wn.snoc(+xs: List<&2, Nat>, +x: Nat, fresh: {Pr.mem(x, xs) == False{} : Bool}) -> {List.length(&2, Nat, Pr.ledger(List.append(&2, Nat, xs, [x]), Nil{})) == 1n+List.length(&2, Nat, Pr.ledger(xs, Nil{})) : Nat}:
  +l = Pr.ledger(xs, Nil{})
  %Equal.sym(List<&2, Nat>, Pr.ledger(List.append(&2, Nat, xs, [x]), Nil{}), Pr.ledger([x], l), LA.pp.app_ledger(xs, [x], Nil{})) : {List.length(&2, Nat, _) == 1n+List.length(&2, Nat, l) : Nat}
  %Equal.sym(Bool, Pr.mem(x, l), False{}, LA.pp.nmem_ledger(xs, Nil{}, x, fresh, {==})) : {List.length(&2, Nat, Pr.add.put(_, x, l)) == 1n+List.length(&2, Nat, l) : Nat}
  {==}

def Progress.work_counts_new_acts(xs, x, fresh):
  ({==}, wn.snoc(xs, x, fresh))
