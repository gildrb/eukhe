# eukhe: the proof of LAW temp_sweep_only_own

import Base
import ../../bend/doc_commit.bend as Cm
import ../../laws/doc_commit.bend as DocCommit
import ./base.bend as LA

def pc.no_other(+i: Nat, +k: Cm.Sort, +h: Bool, other: {Cm.Sort.own(k) == False{} : Bool}) -> {False{} == Cm.removes(Cm.Temp{i, k, h}) : Bool}:
  %Equal.sym(Bool, Cm.Sort.own(k), False{}, other) : {False{} == Bool.and(_, Bool.not(h)) : Bool}
  {==}

# the law temp_sweep_only_own
def pc.sweep_only_own(+pre: List<&2, Cm.Temp>, +i: Nat, +k: Cm.Sort, +h: Bool, +post: List<&2, Cm.Temp>, other: {Cm.Sort.own(k) == False{} : Bool}) -> {Cm.sweep(List.append(&2, Cm.Temp, pre, Cm.Temp{i, k, h} <> post)) == List.append(&2, Cm.Temp, Cm.sweep(pre), Cm.sweep(post)) : List<&2, Cm.Temp>}:
  LA.pc.kept(pre, Cm.Temp{i, k, h}, post, pc.no_other(i, k, h, other))

def DocCommit.temp_sweep_only_own(pre, i, k, h, post, other):
  pc.sweep_only_own(pre, i, k, h, post, other)
