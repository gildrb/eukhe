# eukhe: the proof of LAW skill_loads_iff_described

import Base
import ../../bend/skill_load.bend as Sk
import ../../laws/skill_load.bend as SkillLoad
import ./base.bend as LSk

# the check's verdict is the description's: a missing one is blank
def sld.loads(dm: Maybe<&2, String>, +n: String, +p: String) -> {SkillLoad.sl_loaded(Sk.check.go(n, p, Sk.text.of(dm))) == Bool.not(SkillLoad.sl_blank(SkillLoad.sl_desc(dm))) : Bool}:
  match dm:
    case None{}:
      {==}
    case Some{+d}:
      %LSk.sl.blank(d) : {Bool.not(Sk.blank(d)) == Bool.not(_) : Bool}
      {==}

def SkillLoad.skill_loads_iff_described(m, parent, dm):
  sld.loads(dm, Sk.name.of(m, parent), parent)
