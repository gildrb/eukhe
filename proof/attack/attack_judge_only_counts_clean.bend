# eukhe: the proof of LAW attack_judge_only_counts_clean
#
# PROOF: no strong check: none is shown (LA.am.shown_false); with the checks
# clear, certified is no survivor and enough clean attacks (LA.am.judge);
# the model's fold over the outcomes is the law's count, outcome by outcome
# (ajc.none, ajc.cleans, by induction on the outcomes).

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

# no attack survived exactly when no outcome is a survivor
def ajc.none(os: List<&2, At.Outcome>) -> {Bool.not(At.survived(os)) == Attack.ap_none_survived(os) : Bool}:
  match os:
    case Nil{}:
      {==}
    case Con{o, t}:
      match o:
        case At.Survived{}:
          {==}
        case At.Clean{}:
          ajc.none(t)
        case At.Unrun{}:
          ajc.none(t)

# the model's clean attacks are the clean outcomes counted
def ajc.cleans(os: List<&2, At.Outcome>) -> {At.cleans(os) == Attack.ap_clean_count(os) : Nat}:
  match os:
    case Nil{}:
      {==}
    case Con{o, t}:
      match o:
        case At.Survived{}:
          ajc.cleans(t)
        case At.Clean{}:
          %ajc.cleans(t) : {1n+At.cleans(t) == 1n+_ : Nat}
          {==}
        case At.Unrun{}:
          ajc.cleans(t)

def Attack.attack_judge_only_counts_clean(now, gs, os, none, clear):
  %ajc.none(os) : {At.certified(now, gs, os) == Bool.and(_, Nat.is_le(2n, Attack.ap_clean_count(os))) : Bool}
  %ajc.cleans(os) : {At.certified(now, gs, os) == Bool.and(Bool.not(At.survived(os)), Nat.is_le(2n, _)) : Bool}
  LA.am.judge(St.shown(now, gs), St.clear(now, gs), Bool.not(At.survived(os)), Nat.is_le(2n, At.cleans(os)), LA.am.shown_false(now, gs, none), clear)
