# eukhe: the proof of LAW dir_step_push

import Base
import ../../bend/director.bend as Dr
import ../../laws/director.bend as Director
import ./base.bend as LA

def Director.dir_step_push(m, a, k, c, b, p, va, vr, cap, one, pass, room):
  +St = Director.dir_stayers(a, va)
  +s = List.append(&2, Dr.Layer, a, Dr.Layer{k, 1n+c} <> b)
  +vs = List.append(&2, Dr.Verdict, va, Dr.Stack{p} <> vr)
  +R = Nat.is_lt(List.length(&2, Dr.Layer, s), cap)
  Equal.trans(Dr.Loop, Dr.tick(cap, Dr.Loop{1n+m, s, None{}}, vs), Dr.settle(LA.pd.over(St, Dr.push.at(R, Dr.Layer{k, c}, p, b)), 1n+m, s, vs, cap), Dr.Loop{m, List.append(&2, Dr.Layer, St, p <> Dr.Layer{k, c} <> b), None{}}, LA.pd.step_at(1n+m, a, Dr.Layer{k, 1n+c}, b, va, Dr.Stack{p}, vr, cap, one, pass), Equal.cong(Bool, Dr.Loop, r => Dr.settle(LA.pd.over(St, Dr.push.at(r, Dr.Layer{k, c}, p, b)), 1n+m, s, vs, cap), R, True{}, room))
