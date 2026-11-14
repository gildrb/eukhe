# eukhe: the proof of LAW loop_paused_waits
#
# PROOF: a paused loop is neither in a turn nor judging, so a settled turn
# and a judged check are not its own and the step computes to the same
# state with Rest; a prompt computes to the adopted turn.

import Base
import ../../bend/loop.bend as Lp
import ../../laws/loop/model.bend as Loop

def Loop.loop_paused_waits(i, l, d, c, b, f, x, k, o, ev, bl, now, fu, t):
  ({==}, {==}, {==})
