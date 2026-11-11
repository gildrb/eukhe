# eukhe: the proof of LAW verify_advance_keeps_verdicts
#
# PROOF: case on the claim, on what is due and on the label
# (LA.va.go_keeps): every step answers the revision it was given, and
# either the slots it was given or, on a return for a broken check, those
# slots with some opened (LA.va.reopen_keeps).

import Base
import ../../bend/verify.bend as V
import ../../spec/verified/verify.bend as S
import ../../laws/verify.bend as Verify
import ./base/act.bend as LA

def Verify.verify_advance_keeps_verdicts(now, cap, a, j):
  match a:
    case V.Acc{rev, +slots, claimed, tries}:
      match claimed:
        case True{}:
          LA.va.go_keeps(V.due(now, slots, 0n), now, cap, rev, slots, tries, j)
        case False{}:
          (LA.va.undo_refl(S.nth(j, slots)), {==})
