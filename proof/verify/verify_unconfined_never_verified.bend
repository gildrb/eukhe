# eukhe: the proof of LAW verify_unconfined_never_verified
#
# PROOF: no confinement is in force (V.confined computes to false); a
# label of programs run unconfined is never verified (LL.vl.unconfined);
# a step rests, runs a check, or settles on such a label, and no settling
# on a label that is not verified ends verified (LA.va.go_unconf).

import Base
import ../../bend/verify.bend as V
import ../../spec/verified/verify.bend as S
import ../../laws/verify.bend as Verify
import ./base/label.bend as LL
import ./base/act.bend as LA

# a step of the verifier of programs run unconfined does not end verified
def puv.step(+now: Nat, cap: Nat, a: V.Acc) -> {Verify.sp_ends_verified(S.action(V.advance(False{}, now, cap, a))) == False{} : Bool}:
  match a:
    case V.Acc{rev, +slots, claimed, tries}:
      match claimed:
        case True{}:
          LA.va.go_unconf(V.due(now, slots, 0n), now, cap, rev, slots, tries, LL.vl.unconfined(V.refuted(now, slots), Bool.and(V.some(slots), V.holds(now, slots))))
        case False{}:
          {==}

def Verify.verify_unconfined_never_verified(now, slots, cap, a):
  (LL.vl.unconfined(V.refuted(now, slots), Bool.and(V.some(slots), V.holds(now, slots))), puv.step(now, cap, a))
