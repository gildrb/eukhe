# eukhe: the proof of LAW quirks_verdict_clash
# Induction on the rules and the index (QV.qv.clash): at rule i, the clash
# scan's hit is a rule p places in, p > i, that clashes (QV.qv.cg_some);
# from index 0 the hit is p itself.

import Base
import ../../bend/infer.bend as If
import ../../laws/quirks.bend as Quirks
import ./base/verdicts.bend as QV

def vcl.law(-rs: List<&2, If.Rule>, -r: If.Rule, -i: Nat, -j: Nat, h: QV.qv.CL(rs, r, 0n, i, j)) -> {Nat.is_lt(i, j) == True{} : Bool} & {Quirks.qs_clash_at(r, List.get(&2, If.Rule, rs, j)) == True{} : Bool}:
  (p, q) = h
  (ej, lc) = q
  %Equal.sym(Nat, j, p, ej) : {Nat.is_lt(i, _) == True{} : Bool} & {Quirks.qs_clash_at(r, List.get(&2, If.Rule, rs, _)) == True{} : Bool}
  lc

def Quirks.quirks_verdict_clash(known, rs, i, j, r, at, clash):
  vcl.law(rs, r, i, j, QV.qv.clash(rs, known, 0n, i, r, j, at, clash))
