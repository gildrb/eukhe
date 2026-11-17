# eukhe: the proof of LAW irreversible_record_known
#
# PROOF: finding the key passes the entries of pre, which lack it, and
# stops at its entry, id |pre| + 1 (LA.irb.known); a found key answers
# Known with that id and keeps the ledger.

import Base
import ../../bend/irreversible.bend as Ir
import ../../laws/irreversible.bend as Irreversible
import ./base.bend as LA

def irk.go(+pre: List<&2, Ir.Entry>, +k: Nat, +q: Nat, +post: List<&2, Ir.Entry>, +r: Nat, first: {Irreversible.ir_has(pre, k) == False{} : Bool}) -> {Ir.record(List.append(&2, Ir.Entry, pre, Ir.Entry{k, q} <> post), k) == Ir.Known{1n+List.length(&2, Ir.Entry, pre)} : Ir.Recorded} & {Ir.keep(List.append(&2, Ir.Entry, pre, Ir.Entry{k, q} <> post), k, r) == List.append(&2, Ir.Entry, pre, Ir.Entry{k, q} <> post) : List<&2, Ir.Entry>}:
  +es = List.append(&2, Ir.Entry, pre, Ir.Entry{k, q} <> post)
  +n = List.length(&2, Ir.Entry, pre)
  +f = LA.irb.known(pre, k, q, post, 0n, first)
  +rec = Equal.trans(Ir.Recorded, Ir.record(es, k), Ir.Known{Nat.add(n, 1n)}, Ir.Known{1n+n}, Equal.cong(Maybe<&2, Nat>, Ir.Recorded, z => Ir.record.of(z, es), Ir.find(es, k, 0n), Some{Nat.add(n, 1n)}, f), Equal.cong(Nat, Ir.Recorded, z => Ir.Known{z}, Nat.add(n, 1n), 1n+n, LA.irb.add_one(n)))
  +kept = Equal.cong(Maybe<&2, Nat>, List<&2, Ir.Entry>, z => Ir.keep.of(z, es, k, r), Ir.find(es, k, 0n), Some{Nat.add(n, 1n)}, f)
  (rec, kept)

def Irreversible.irreversible_record_known(pre, k, q, post, r, first):
  irk.go(pre, k, q, post, r, first)
