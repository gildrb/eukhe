# eukhe: the proof of LAW dir_tick_goes_on

import Base
import ../../bend/director.bend as Dr
import ../../LAWS.bend as Laws

def Laws.dir_tick_goes_on(cap, n, s, vs, t, go):
  %Equal.sym(Dr.Dec, Dr.decide(s, vs, cap), Dr.Dec{Dr.Cont{}, t}, go) : {Dr.settle(_, 1n+n, s, vs, cap) == Dr.Loop{n, t, None{}} : Dr.Loop}
  {==}
