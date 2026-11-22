# eukhe: the proof of LAW attack_certified_is_spec
#
# PROOF: the model's folds are the spec's counts (LA.am.unsurvived, LA.am.cleans),
# the checks' folds bend/strength.bend's (LS.sg.shown, LS.sg.clear), and
# the two shapes agree on every Bool (LA.am.cert_bool).

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

def Attack.attack_certified_is_spec(now, gs, os):
  LA.am.certified(now, gs, os)
