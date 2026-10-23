# eukhe: the proof of LAW temp_sweep_removes_free

import Base
import ../../bend/doc_commit.bend as Cm
import ../../laws/doc_commit.bend as DocCommit
import ./base.bend as LA

# the law temp_sweep_removes_free
def pc.sweep_removes_free(+pre: List<&2, Cm.Temp>, +i: Nat, +post: List<&2, Cm.Temp>) -> {Cm.sweep(List.append(&2, Cm.Temp, pre, Cm.Temp{i, Cm.Own{}, False{}} <> post)) == List.append(&2, Cm.Temp, Cm.sweep(pre), Cm.Temp{i, Cm.Own{}, False{}} <> Cm.sweep(post)) : List<&2, Cm.Temp>}:
  +n = {Cm.Temp{i, Cm.Own{}, False{}} : Cm.Temp}
  %LA.pc.sweep_app(pre, n <> post) : {_ == List.append(&2, Cm.Temp, Cm.sweep(pre), n <> Cm.sweep(post)) : List<&2, Cm.Temp>}
  {==}

def DocCommit.temp_sweep_removes_free(pre, i, post):
  pc.sweep_removes_free(pre, i, post)
