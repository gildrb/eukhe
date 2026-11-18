# eukhe: the proof of LAW attack_exit_is_spec
#
# PROOF: by cases on whether every check holds (LS.sv.holds), certified as the
# spec's (LA.am.exit).

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

def Attack.attack_exit_is_spec(base, now, slots, gs, os):
  LA.am.exit(base, now, slots, gs, os)
