# eukhe: the proof of LAW attack_exit_survivor_never_zero
#
# PROOF: a survivor keeps done from being certified (LA.am.cert_survivor); a run
# with a check whose done is not certified never exits 0
# (LA.am.exit_uncertified).

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

def Attack.attack_exit_survivor_never_zero(base, now, slots, gs, pre, post, checked):
  LA.am.exit_uncertified(V.holds(now, slots), base, now, slots, gs, List.append(&2, At.Outcome, pre, At.Survived{} <> post), checked, LA.am.cert_survivor(now, gs, pre, post))
