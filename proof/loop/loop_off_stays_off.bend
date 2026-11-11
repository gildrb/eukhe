# eukhe: the proof of LAW loop_off_stays_off
#
# PROOF: an off state (Off or Ended) is fixed by every event but Enter,
# with the answer Rest (lh.off_step, by cases on the phase and the event);
# by induction on the history (lh.off_hist).

import Base
import ../../bend/loop.bend as Lp
import ../../spec/loop/loop.bend as S
import ../../laws/loop/history.bend as LoopHistory
import ./base/history.bend as LALoopHistory

def LoopHistory.loop_off_stays_off(s, h, off, ne):
  LALoopHistory.lh.off_hist(h, s, off, ne)
