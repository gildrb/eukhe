# eukhe: the proof of LAW goal_text_escape_plain
#
# PROOF: the char is none of the three marks, so it is kept.

import Base
import ../../bend/goal_text.bend as Gt
import ../../laws/goal_text.bend as GoalText
import ./base/text.bend as LT

def GoalText.goal_text_escape_plain(c, na, nl, ng):
  %Equal.sym(Bool, Char.is_eq(c, '&'), False{}, na) : {Gt.escape.lt(_, Char.is_eq(c, '<'), Char.is_eq(c, '>'), c, "") == SCon{c, ""} : String}
  %Equal.sym(Bool, Char.is_eq(c, '<'), False{}, nl) : {Gt.escape.lt(False{}, _, Char.is_eq(c, '>'), c, "") == SCon{c, ""} : String}
  %Equal.sym(Bool, Char.is_eq(c, '>'), False{}, ng) : {Gt.escape.lt(False{}, False{}, _, c, "") == SCon{c, ""} : String}
  {==}
