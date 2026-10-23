# eukhe: the proof of LAW sweep_never_young

import Base
import ../../bend/staging.bend as Sg
import ../../laws/staging.bend as Staging
import ./base.bend as LA

def pg.no_young(+i: Nat, +k: Sg.Sort, h: Bool, o: Bool) -> {False{} == Sg.removes(Sg.Node{i, k, h, False{}, o}) : Bool}:
  match h o:
    case True{} True{}:
      {==}
    case True{} False{}:
      {==}
    case False{} True{}:
      {==}
    case False{} False{}:
      {==}

def pg.sweep_never_young(+pre: List<&2, Sg.Node>, +i: Nat, +k: Sg.Sort, +h: Bool, +o: Bool, +post: List<&2, Sg.Node>) -> {Sg.sweep(List.append(&2, Sg.Node, pre, Sg.Node{i, k, h, False{}, o} <> post)) == List.append(&2, Sg.Node, Sg.sweep(pre), Sg.sweep(post)) : List<&2, Sg.Node>}:
  LA.pg.kept(pre, Sg.Node{i, k, h, False{}, o}, post, pg.no_young(i, k, h, o))

def Staging.sweep_never_young(pre, i, k, h, o, post):
  pg.sweep_never_young(pre, i, k, h, o, post)
