# eukhe: the proof of LAW loop_count_conserved
#
# PROOF: at every event but Enter the count after it, plus one if it
# started an iteration, is the count before it (lh.left_step, from
# lh.view_step and by cases for a prompt); by induction on the history
# (lh.left_hist) the count is the first one less the iterations started.

import Base
import ../../bend/loop.bend as Lp
import ../../spec/loop/loop.bend as S
import ../../laws/loop/history.bend as LoopHistory
import ./base/history.bend as LALoopHistory

def LoopHistory.loop_count_conserved(s, h, n, hl, ne):
  %hl : {S.left(S.after(h, s)) == LALoopHistory.lh.spend(S.submits(S.acts(h, s)), _) : Maybe<&2, Nat>}
  LALoopHistory.lh.left_hist(h, s, ne)
