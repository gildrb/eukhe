# eukhe: the proof of LAW attack_exit_none_is_strength
#
# PROOF: by cases on whether every check holds; with no outcome, certified is
# bend/strength.bend's (LA.am.exit_none).

import Base
import ../../bend/verify.bend as V
import ../../bend/strength.bend as St
import ../../bend/attack.bend as At
import ../../bend/headless_task.bend as Ht
import ../../spec/verified/verify.bend as SV
import ../../spec/verified/strength.bend as S
import ../../spec/verified/attack.bend as SA
import ../../laws/attack.bend as Attack
import ../strength/base/model.bend as LS
import ./base/model.bend as LA

def Attack.attack_exit_none_is_strength(base, now, slots, gs):
  LA.am.exit_none(V.holds(now, slots), base, now, slots, gs)
