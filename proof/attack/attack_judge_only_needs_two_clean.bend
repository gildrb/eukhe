# eukhe: the proof of LAW attack_judge_only_needs_two_clean
#
# PROOF: no strong check: none is shown (LA.am.shown_false); with the checks
# clear, certified is no survivor and enough clean attacks (LA.am.judge).

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

def Attack.attack_judge_only_needs_two_clean(now, gs, os, none, clear):
  LA.am.judge(St.shown(now, gs), St.clear(now, gs), Bool.not(At.survived(os)), Nat.is_le(2n, At.cleans(os)), LA.am.shown_false(now, gs, none), clear)
