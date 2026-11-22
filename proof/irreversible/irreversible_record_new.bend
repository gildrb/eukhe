# eukhe: the proof of LAW irreversible_record_new
#
# PROOF: a ledger that lacks the key finds no entry for it
# (LA.irb.fresh), so recording answers the next id and appends the entry
# last (LA.irb.rec_new, LA.irb.keep_new).

import Base
import ../../bend/irreversible.bend as Ir
import ../../laws/irreversible.bend as Irreversible
import ./base.bend as LA

def irn.go(+es: List<&2, Ir.Entry>, +k: Nat, +r: Nat, +fresh: {Irreversible.ir_has(es, k) == False{} : Bool}) -> {Ir.record(es, k) == Ir.New{1n+List.length(&2, Ir.Entry, es)} : Ir.Recorded} & {Ir.keep(es, k, r) == List.append(&2, Ir.Entry, es, [Ir.Entry{k, r}]) : List<&2, Ir.Entry>}:
  (LA.irb.rec_new(es, k, fresh), LA.irb.keep_new(es, k, r, fresh))

def Irreversible.irreversible_record_new(es, k, r, fresh):
  irn.go(es, k, r, fresh)
