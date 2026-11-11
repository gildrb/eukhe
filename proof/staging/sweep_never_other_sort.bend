# eukhe: the proof of LAW sweep_never_other_sort

import Base
import ../../bend/staging.bend as Sg
import ../../laws/staging.bend as Staging
import ./base.bend as LA

# a node whose sort the sweep never takes is never removed, whatever its
# reach, lock and age
def ns.zero(o: Bool, h: Bool, s: Bool) -> {False{} == Bool.and(o, Bool.and(Bool.not(h), Bool.and(s, False{}))) : Bool}:
  match o:
    case True{}:
      match h:
        case True{}:
          {==}
        case False{}:
          match s:
            case True{}:
              {==}
            case False{}:
              {==}
    case False{}:
      {==}

def Staging.sweep_never_other_sort(pre, i, h, s, o, post):
  (LA.pg.kept(pre, Sg.Node{i, Sg.Store{}, h, s, o}, post, ns.zero(o, h, s)), (LA.pg.kept(pre, Sg.Node{i, Sg.Plain{}, h, s, o}, post, ns.zero(o, h, s)), (LA.pg.kept(pre, Sg.Node{i, Sg.Other{}, h, s, o}, post, ns.zero(o, h, s)), LA.pg.kept(pre, Sg.Node{i, Sg.Lock{True{}}, h, s, o}, post, ns.zero(o, h, s)))))
