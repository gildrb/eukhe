# eukhe: the proof of LAW attack_unrun_changes_nothing
#
# PROOF: an unrun outcome anywhere changes neither whether one survived
# (LA.am.survived_unrun) nor the clean count (LA.am.cleans_unrun), and
# certified reads only those (LA.am.cert_eq).

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

def Attack.attack_unrun_changes_nothing(now, gs, pre, post):
  LA.am.cert_eq(now, gs, List.append(&2, At.Outcome, pre, At.Unrun{} <> post), List.append(&2, At.Outcome, pre, post), LA.am.survived_unrun(pre, post), LA.am.cleans_unrun(pre, post))
