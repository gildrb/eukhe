# eukhe: the proof of LAW skill_in_exact
# Both ways by induction on the list (proof/skill_load/base.bend): a head
# equal to c makes same_cand true, and a true same_cand gives the equal
# path and outcome.

import Base
import ../../bend/skill_load.bend as Sk
import ../../laws/skill_load.bend as SkillLoad
import ./base.bend as LA

def SkillLoad.skill_in_exact(c, cs):
  (i => LA.sl.in_sound(c, cs, i), h => LA.sl.in_complete(c, cs, h))
