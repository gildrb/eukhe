# eukhe: the proof of LAW sweep_reaches_every_depth

import Base
import ../../bend/staging.bend as Sg
import ../../laws/staging.bend as Staging
import ./base.bend as LA

def pg.sweep_reaches(+pre: List<&2, Sg.Node>, +i: Nat, +k: Sg.Sort, +post: List<&2, Sg.Node>, sw: {Sg.Sort.swept(k) == True{} : Bool}) -> {Sg.sweep(List.append(&2, Sg.Node, pre, Sg.Node{i, k, False{}, True{}, True{}} <> post)) == List.append(&2, Sg.Node, Sg.sweep(pre), Sg.Node{i, k, False{}, True{}, True{}} <> Sg.sweep(post)) : List<&2, Sg.Node>}:
  +n = {Sg.Node{i, k, False{}, True{}, True{}} : Sg.Node}
  %LA.pg.sweep_app(pre, n <> post) : {_ == List.append(&2, Sg.Node, Sg.sweep(pre), n <> Sg.sweep(post)) : List<&2, Sg.Node>}
  %Equal.sym(Bool, Sg.Sort.swept(k), True{}, sw) : {List.append(&2, Sg.Node, Sg.sweep(pre), Sg.sweep.put(n, Sg.sweep(post), _)) == List.append(&2, Sg.Node, Sg.sweep(pre), n <> Sg.sweep(post)) : List<&2, Sg.Node>}
  {==}

def Staging.sweep_reaches_every_depth(pre, i, k, post, sw):
  pg.sweep_reaches(pre, i, k, post, sw)
