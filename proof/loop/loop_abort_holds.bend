# eukhe: the proof of LAW loop_abort_holds
#
# PROOF: the interrupt starts nothing and leaves the loop paused or off
# (lh.abort_first, by cases on the phase); from such a state an unattended
# event starts nothing and leaves such a state (lh.quiet_step), so by
# induction on the history nothing is started (lh.quiet_hist).

import Base
import ../../bend/loop.bend as Lp
import ../../spec/loop/loop.bend as S
import ../../laws/loop/history.bend as LoopHistory
import ./base/history.bend as LALoopHistory

def LoopHistory.loop_abort_holds(s, h, u):
  LALoopHistory.lh.abort_hist(s, h, u)
