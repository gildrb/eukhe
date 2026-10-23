# eukhe: the proof of LAW sweep_never_live

import Base
import ../../bend/staging.bend as Sg
import ../../laws/staging.bend as Staging
import ./base.bend as LA

def pg.no_held(+i: Nat, +k: Sg.Sort, +s: Bool, o: Bool) -> {False{} == Sg.removes(Sg.Node{i, k, True{}, s, o}) : Bool}:
  match o:
    case True{}:
      {==}
    case False{}:
      {==}

def pg.sweep_never_live(+pre: List<&2, Sg.Node>, +i: Nat, +k: Sg.Sort, +s: Bool, +o: Bool, +post: List<&2, Sg.Node>) -> {Sg.sweep(List.append(&2, Sg.Node, pre, Sg.Node{i, k, True{}, s, o} <> post)) == List.append(&2, Sg.Node, Sg.sweep(pre), Sg.sweep(post)) : List<&2, Sg.Node>}:
  LA.pg.kept(pre, Sg.Node{i, k, True{}, s, o}, post, pg.no_held(i, k, s, o))

def Staging.sweep_never_live(pre, i, k, s, o, post):
  pg.sweep_never_live(pre, i, k, s, o, post)
