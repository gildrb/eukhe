# eukhe: the proof of LAW loop_unattended_resends_same
#
# PROOF: by induction on the history, for every state (lh.same_hist): an
# unattended event sends no text but the prompt and keeps the prompt
# (lh.view_step, by cases on the phase and the event), unless it leaves
# the loop off or paused: from there nothing is started (lh.quiet_hist).

import Base
import ../../bend/loop.bend as Lp
import ../../spec/loop/loop.bend as S
import ../../laws/loop/history.bend as LoopHistory
import ./base/history.bend as LALoopHistory

def LoopHistory.loop_unattended_resends_same(s, h, u):
  LALoopHistory.lh.same_hist(h, s, u)
