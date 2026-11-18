# eukhe: the proof of LAW attack_label_survivor_uncertified
#
# PROOF: a survivor keeps done from being certified (LA.am.cert_survivor), and a
# passing label is then not certified (LA.am.label_unc).

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

def Attack.attack_label_survivor_uncertified(l, now, gs, pre, post, passing):
  LA.am.label_unc(St.passes(l), At.certified(now, gs, List.append(&2, At.Outcome, pre, At.Survived{} <> post)), l, passing, LA.am.cert_survivor(now, gs, pre, post))
