# eukhe: the proof of LAW loop_uncounted_stays
#
# PROOF: the count after a history with no Enter is the count before it
# less the iterations started, and no count stays no count (lh.left_hist,
# by induction on the history from lh.left_step); the premise says the
# loop had none.

import Base
import ../../bend/loop.bend as Lp
import ../../spec/loop/loop.bend as S
import ../../laws/loop/history.bend as LoopHistory
import ./base/history.bend as LALoopHistory

def LoopHistory.loop_uncounted_stays(s, h, hl, ne):
  %hl : {S.left(S.after(h, s)) == LALoopHistory.lh.spend(S.submits(S.acts(h, s)), _) : Maybe<&2, Nat>}
  LALoopHistory.lh.left_hist(h, s, ne)
