# eukhe: the proof of LAW attack_label_none_is_strength
#
# PROOF: with no outcome, certified is bend/strength.bend's (LA.am.cert_none),
# and the labels read it alike.

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

def Attack.attack_label_none_is_strength(l, now, gs):
  %LA.am.cert_none(now, gs) : {At.label(l, now, gs, Nil{}) == St.label.pass(St.passes(l), _, l) : St.Label}
  {==}
