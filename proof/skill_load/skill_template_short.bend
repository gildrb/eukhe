# eukhe: the proof of LAW skill_template_short

import Base
import ../../bend/skill_load.bend as Sk
import ../../laws/skill_load.bend as SkillLoad
import ./base.bend as LSk

# a line of at most 60 chars is kept whole
def sts.cut(+l: List<&2, String>, s: {Nat.is_lt(60n, String.length(SkillLoad.sl_line(l))) == False{} : Bool}) -> {Sk.cut(Sk.first(l)) == SkillLoad.sl_line(l) : String}:
  %Equal.sym(String, Sk.first(l), SkillLoad.sl_line(l), LSk.sl.line(l)) : {Sk.cut(_) == SkillLoad.sl_line(l) : String}
  %Equal.sym(Bool, Nat.is_lt(60n, String.length(SkillLoad.sl_line(l))), False{}, s) : {Sk.cut.if(_, SkillLoad.sl_line(l)) == SkillLoad.sl_line(l) : String}
  {==}

def SkillLoad.skill_template_short(body, s):
  (sts.cut(String.lines(body), s), sts.cut(String.lines(body), s))
