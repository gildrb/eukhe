# eukhe: the proof of LAW edit_reply_conflict
#
# PROOF: by induction on the files before the changed one, the edit holds
# a conflict (dc.hit: a changed file before it already does, an unchanged
# one passes the question on); an edit with a conflict is rejected.

import Base
import ../../bend/doc_commit.bend as Cm
import ../../laws/doc_commit/exact.bend as DocCommitExact

# an edit with a changed file, anywhere, holds a conflict
def dc.hit(pre: List<&2, Cm.Doc>, +k: Cm.Op, +x: Cm.Fault, +post: List<&2, Cm.Doc>) -> {Cm.conflict(List.append(&2, Cm.Doc, pre, Cm.Doc{k, True{}, x} <> post)) == True{} : Bool}:
  match pre:
    case Nil{}:
      {==}
    case f <> rest:
      match f:
        case Cm.Doc{j, c, y}:
          match c:
            case True{}:
              {==}
            case False{}:
              dc.hit(rest, k, x, post)

def DocCommitExact.edit_reply_conflict(pre, k, x, post):
  +fs = List.append(&2, Cm.Doc, pre, Cm.Doc{k, True{}, x} <> post)
  %Equal.sym(Bool, Cm.conflict(fs), True{}, dc.hit(pre, k, x, post)) : {Cm.reply.pick(_, fs) == Cm.Rejected{} : Cm.Reply}
  {==}
