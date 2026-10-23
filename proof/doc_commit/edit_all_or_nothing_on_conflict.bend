# eukhe: the proof of LAW edit_all_or_nothing_on_conflict

import Base
import ../../bend/doc_commit.bend as Cm
import ../../LAWS.bend as Laws

def pc.or_t(a: Bool) -> {Bool.or(a, True{}) == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

# a changed file anywhere is a conflict
def pc.conflict_at(pre: List<&2, Cm.Doc>, +k: Cm.Op, +x: Cm.Fault, +post: List<&2, Cm.Doc>) -> {Cm.conflict(List.append(&2, Cm.Doc, pre, Cm.Doc{k, True{}, x} <> post)) == True{} : Bool}:
  match pre:
    case Nil{}:
      {==}
    case g <> rest:
      match g:
        case Cm.Doc{gk, gc, gx}:
          %Equal.sym(Bool, Cm.conflict(List.append(&2, Cm.Doc, rest, Cm.Doc{k, True{}, x} <> post)), True{}, pc.conflict_at(rest, k, x, post)) : {Bool.or(gc, _) == True{} : Bool}
          pc.or_t(gc)

# the law edit_all_or_nothing_on_conflict
def pc.all_or_nothing(+pre: List<&2, Cm.Doc>, +k: Cm.Op, +x: Cm.Fault, +post: List<&2, Cm.Doc>) -> {Cm.landed(List.append(&2, Cm.Doc, pre, Cm.Doc{k, True{}, x} <> post)) == Nil{} : List<&2, Nat>}:
  +fs = {List.append(&2, Cm.Doc, pre, Cm.Doc{k, True{}, x} <> post) : List<&2, Cm.Doc>}
  %Equal.sym(Bool, Cm.conflict(fs), True{}, pc.conflict_at(pre, k, x, post)) : {Cm.landed.pick(_, fs) == Nil{} : List<&2, Nat>}
  {==}

def Laws.edit_all_or_nothing_on_conflict(pre, k, x, post):
  pc.all_or_nothing(pre, k, x, post)
