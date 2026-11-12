# eukhe: the proof of LAW skill_template_long

import Base
import ../../bend/skill_load.bend as Sk
import ../../laws/skill_load.bend as SkillLoad
import ./base.bend as LSk

# a line of more than 60 chars is cut to 60, then "..."
def stl.cut(+l: List<&2, String>, s: {Nat.is_lt(60n, String.length(SkillLoad.sl_line(l))) == True{} : Bool}) -> {Sk.cut(Sk.first(l)) == String.append(String.take(SkillLoad.sl_line(l), 60n), "...") : String}:
  %Equal.sym(String, Sk.first(l), SkillLoad.sl_line(l), LSk.sl.line(l)) : {Sk.cut(_) == String.append(String.take(SkillLoad.sl_line(l), 60n), "...") : String}
  %Equal.sym(Bool, Nat.is_lt(60n, String.length(SkillLoad.sl_line(l))), True{}, s) : {Sk.cut.if(_, SkillLoad.sl_line(l)) == String.append(String.take(SkillLoad.sl_line(l), 60n), "...") : String}
  {==}

def SkillLoad.skill_template_long(body, s):
  (stl.cut(String.lines(body), s), stl.cut(String.lines(body), s))
