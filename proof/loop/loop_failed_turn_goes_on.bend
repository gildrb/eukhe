# eukhe: the proof of LAW loop_failed_turn_goes_on
#
# PROOF: each step is rewritten to the advance past the failure cap with
# 1 + f failed turns (lb.errored_fresh: the failed turn of a loop with no
# condition counts one more, and f < 2 makes Lp.tired(1 + f) False, by
# lb.fresh_next); with a deadline its test is replaced by False, from
# now < dl (lb.lt_not_le, in lb.errored_time). Funded, not spent and not
# late, the halt is None and the advance computes to the next turn, one
# iteration fewer, the same deadline.

import Base
import ../../bend/loop.bend as Lp
import ../../spec/loop/loop.bend as S
import ../../laws/loop/model.bend as Loop
import ./base/bounds.bend as LALoopBounds

def Loop.loop_failed_turn_goes_on(i, n, dl, b, f, x, now, hf, hl):
  +j = i
  +q = hf
  +t = LALoopBounds.lb.lt_not_le(now, dl, hl)
  (%LALoopBounds.lb.errored_time(False{}, j, f, Some{1n+n}, dl, b, x, now, True{}, q, t) : {_ == (Lp.St{Lp.Turn{}, 1n+i, Some{n}, Some{dl}, Lp.NoCond{}, b, 1n+f, x}, Lp.Submit{1n+i, b}) : Lp.St & Lp.Act}; {==},
   %LALoopBounds.lb.errored_fresh(j, f, Some{1n+n}, None{}, b, x, now, True{}, q) : {_ == (Lp.St{Lp.Turn{}, 1n+i, Some{n}, None{}, Lp.NoCond{}, b, 1n+f, x}, Lp.Submit{1n+i, b}) : Lp.St & Lp.Act}; {==},
   %LALoopBounds.lb.errored_time(False{}, j, f, None{}, dl, b, x, now, True{}, q, t) : {_ == (Lp.St{Lp.Turn{}, 1n+i, None{}, Some{dl}, Lp.NoCond{}, b, 1n+f, x}, Lp.Submit{1n+i, b}) : Lp.St & Lp.Act}; {==},
   %LALoopBounds.lb.errored_fresh(j, f, None{}, None{}, b, x, now, True{}, q) : {_ == (Lp.St{Lp.Turn{}, 1n+i, None{}, None{}, Lp.NoCond{}, b, 1n+f, x}, Lp.Submit{1n+i, b}) : Lp.St & Lp.Act}; {==})
