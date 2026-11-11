# eukhe: the proof of LAW skill_template_given

import Base
import ../../bend/skill_load.bend as Sk
import ../../laws/skill_load.bend as SkillLoad

def SkillLoad.skill_template_given(d, e, body):
  %Equal.sym(Bool, String.is_empty(d), False{}, e) : {Sk.summary.pick(_, d, body) == d : String}
  {==}
