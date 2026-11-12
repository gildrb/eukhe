# eukhe: the proof of LAW loop_count_bounds
#
# PROOF: by induction on the history, for every state (lh.cnt_hist): the
# count after an unattended event, plus one if it started an iteration,
# is the count before it (lh.view_step; `halt` forbids an iteration from
# a spent count, lh.halt_spent); the premise names that count n.

import Base
import ../../bend/loop.bend as Lp
import ../../spec/loop/loop.bend as S
import ../../laws/loop/history.bend as LoopHistory
import ./base/history.bend as LALoopHistory

def LoopHistory.loop_count_bounds(s, h, n, hl, u):
  %hl : {LALoopHistory.lh.fits(S.submits(S.acts(h, s)), _) == True{} : Bool}
  LALoopHistory.lh.cnt_hist(h, s, u)
