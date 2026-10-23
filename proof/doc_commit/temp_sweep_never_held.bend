# eukhe: the proof of LAW temp_sweep_never_held

import Base
import ../../bend/doc_commit.bend as Cm
import ../../laws/doc_commit.bend as DocCommit
import ./base.bend as LA

def pc.no_held(+i: Nat, k: Cm.Sort) -> {False{} == Cm.removes(Cm.Temp{i, k, True{}}) : Bool}:
  match k:
    case Cm.Own{}:
      {==}
    case Cm.Foreign{}:
      {==}
    case Cm.Plain{}:
      {==}

# the law temp_sweep_never_held
def pc.sweep_never_held(+pre: List<&2, Cm.Temp>, +i: Nat, +k: Cm.Sort, +post: List<&2, Cm.Temp>) -> {Cm.sweep(List.append(&2, Cm.Temp, pre, Cm.Temp{i, k, True{}} <> post)) == List.append(&2, Cm.Temp, Cm.sweep(pre), Cm.sweep(post)) : List<&2, Cm.Temp>}:
  LA.pc.kept(pre, Cm.Temp{i, k, True{}}, post, pc.no_held(i, k))

# (F10) Temporary files

def DocCommit.temp_sweep_never_held(pre, i, k, post):
  pc.sweep_never_held(pre, i, k, post)
