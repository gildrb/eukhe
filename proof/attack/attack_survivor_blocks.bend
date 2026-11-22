# eukhe: the proof of LAW attack_survivor_blocks
#
# PROOF: a survivor anywhere among the outcomes is seen (LA.am.survived_around), so
# done is not certified (LA.am.cert_survivor).

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

def Attack.attack_survivor_blocks(now, gs, pre, post):
  LA.am.cert_survivor(now, gs, pre, post)
