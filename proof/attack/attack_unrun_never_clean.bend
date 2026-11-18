# eukhe: the proof of LAW attack_unrun_never_clean
#
# PROOF: closed in the inputs: an attack that did not run computes to unrun.

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

def Attack.attack_unrun_never_clean(passes, differs, agrees):
  {==}
