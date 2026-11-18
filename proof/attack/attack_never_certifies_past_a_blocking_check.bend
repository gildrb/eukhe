# eukhe: the proof of LAW attack_never_certifies_past_a_blocking_check
#
# PROOF: both ways to certify need the checks clear (LA.am.blocked).

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

def Attack.attack_never_certifies_past_a_blocking_check(now, gs, os, blocked):
  LA.am.blocked(St.clear(now, gs), Bool.not(At.survived(os)), St.shown(now, gs), Nat.is_le(At.needed(), At.cleans(os)), blocked)
