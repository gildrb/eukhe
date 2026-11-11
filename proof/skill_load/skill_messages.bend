# eukhe: the proof of LAW skill_messages

import Base
import ../../bend/skill_load.bend as Sk
import ../../laws/skill_load.bend as SkillLoad
import ./base.bend as LSk

# the description the check reads is the laws' (a missing one is empty)
def smg.at(dm: Maybe<&2, String>, +n: String, +p: String) -> {List.append(&2, String, Sk.desc.msgs(Sk.text.of(dm)), Sk.name.msgs(n, p)) == SkillLoad.sl_messages(n, p, SkillLoad.sl_desc(dm)) : List<&2, String>}:
  match dm:
    case None{}:
      LSk.sl.messages(n, p, "")
    case Some{+d}:
      LSk.sl.messages(n, p, d)

def SkillLoad.skill_messages(m, parent, dm):
  smg.at(dm, Sk.name.of(m, parent), parent)
