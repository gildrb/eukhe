# eukhe: the proof of LAW loop_inside_continues
#
# PROOF: each step is rewritten to the advance past the failure cap; with a
# deadline its test is replaced by False, from now < dl (lb.lt_not_le, in
# lb.go_time and lb.ran_time); with none lb.go_fresh and lb.ran. Funded, not
# spent and not late, the halt is None and the advance computes to the next
# turn, one iteration fewer, the same deadline.

import Base
import ../../bend/loop.bend as Lp
import ../../spec/loop/loop.bend as S
import ../../laws/loop/model.bend as Loop
import ./base/bounds.bend as LALoopBounds

def Loop.loop_inside_continues(i, n, dl, c, b, f, x, ev, now, hg, hf, hl):
  +j = i
  +g = hg
  +q = hf
  +t = LALoopBounds.lb.lt_not_le(now, dl, hl)
  (%LALoopBounds.lb.go_time(False{}, c, ev, j, f, Some{1n+n}, dl, b, x, now, True{}, g, q, t) : {_ == (Lp.St{Lp.Turn{}, 1n+i, Some{n}, Some{dl}, c, b, f, Lp.Check{i, ev}}, Lp.Submit{1n+i, b}) : Lp.St & Lp.Act}; {==},
   %LALoopBounds.lb.go_fresh(c, ev, j, f, Some{1n+n}, None{}, b, x, now, True{}, g, q) : {_ == (Lp.St{Lp.Turn{}, 1n+i, Some{n}, None{}, c, b, f, Lp.Check{i, ev}}, Lp.Submit{1n+i, b}) : Lp.St & Lp.Act}; {==},
   %LALoopBounds.lb.go_time(False{}, c, ev, j, f, None{}, dl, b, x, now, True{}, g, q, t) : {_ == (Lp.St{Lp.Turn{}, 1n+i, None{}, Some{dl}, c, b, f, Lp.Check{i, ev}}, Lp.Submit{1n+i, b}) : Lp.St & Lp.Act}; {==},
   %LALoopBounds.lb.go_fresh(c, ev, j, f, None{}, None{}, b, x, now, True{}, g, q) : {_ == (Lp.St{Lp.Turn{}, 1n+i, None{}, None{}, c, b, f, Lp.Check{i, ev}}, Lp.Submit{1n+i, b}) : Lp.St & Lp.Act}; {==},
   %LALoopBounds.lb.ran_time(False{}, j, Some{1n+n}, dl, b, f, x, now, True{}, t) : {_ == (Lp.St{Lp.Turn{}, 1n+i, Some{n}, Some{dl}, Lp.NoCond{}, b, 0n, x}, Lp.Submit{1n+i, b}) : Lp.St & Lp.Act}; {==},
   %LALoopBounds.lb.ran(j, Some{1n+n}, None{}, b, f, x, now, True{}) : {_ == (Lp.St{Lp.Turn{}, 1n+i, Some{n}, None{}, Lp.NoCond{}, b, 0n, x}, Lp.Submit{1n+i, b}) : Lp.St & Lp.Act}; {==},
   %LALoopBounds.lb.ran_time(False{}, j, None{}, dl, b, f, x, now, True{}, t) : {_ == (Lp.St{Lp.Turn{}, 1n+i, None{}, Some{dl}, Lp.NoCond{}, b, 0n, x}, Lp.Submit{1n+i, b}) : Lp.St & Lp.Act}; {==},
   %LALoopBounds.lb.ran(j, None{}, None{}, b, f, x, now, True{}) : {_ == (Lp.St{Lp.Turn{}, 1n+i, None{}, None{}, Lp.NoCond{}, b, 0n, x}, Lp.Submit{1n+i, b}) : Lp.St & Lp.Act}; {==})
