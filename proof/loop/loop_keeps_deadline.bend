# eukhe: the proof of LAW loop_keeps_deadline
#
# PROOF: every event but Enter keeps the deadline (lh.dl_step, from
# lh.view_step and by cases for a prompt); by induction on the history,
# for every state (lh.dl_hist).

import Base
import ../../bend/loop.bend as Lp
import ../../spec/loop/loop.bend as S
import ../../laws/loop/history.bend as LoopHistory
import ./base/history.bend as LALoopHistory

def LoopHistory.loop_keeps_deadline(s, h, ne):
  LALoopHistory.lh.dl_hist(h, s, ne)
