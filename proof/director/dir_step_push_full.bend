# eukhe: the proof of LAW dir_step_push_full

import Base
import ../../bend/director.bend as Dr
import ../../laws/director.bend as Director
import ./base.bend as LA

def Director.dir_step_push_full(n, a, k, c, b, p, va, vr, cap, one, pass, full):
  +o = one
  +q = pass
  +f = full
  +St = Director.dir_stayers(a, va)
  +s = List.append(&2, Dr.Layer, a, Dr.Layer{k, 1n+c} <> b)
  +vs = List.append(&2, Dr.Verdict, va, Dr.Stack{p} <> vr)
  +R = Nat.is_lt(List.length(&2, Dr.Layer, s), cap)
  +e1 = LA.pd.step_at(n, a, Dr.Layer{k, 1n+c}, b, va, Dr.Stack{p}, vr, cap, o, q)
  +e2 = Equal.cong(Bool, Dr.Loop, r => Dr.settle(LA.pd.over(St, Dr.push.at(r, Dr.Layer{k, c}, p, b)), n, s, vs, cap), R, False{}, f)
  +e3 = Equal.cong(List<&2, Dr.Layer>, Dr.Loop, x => Dr.Loop{n, x, Some{Dr.Failed{}}}, Dr.kept(s, vs, cap), Dr.Dec.stack(LA.pd.over(St, Dr.push.at(R, Dr.Layer{k, c}, p, b))), LA.pd.kept_at(a, Dr.Layer{k, 1n+c}, b, va, Dr.Stack{p}, vr, cap, o, q))
  +e4 = Equal.cong(Bool, Dr.Loop, r => Dr.Loop{n, Dr.Dec.stack(LA.pd.over(St, Dr.push.at(r, Dr.Layer{k, c}, p, b))), Some{Dr.Failed{}}}, R, False{}, f)
  +X = Dr.tick(cap, Dr.Loop{n, s, None{}}, vs)
  +Y = Dr.settle(LA.pd.over(St, Dr.push.at(R, Dr.Layer{k, c}, p, b)), n, s, vs, cap)
  +K = {Dr.Loop{n, Dr.kept(s, vs, cap), Some{Dr.Failed{}}} : Dr.Loop}
  +W = {Dr.Loop{n, Dr.Dec.stack(LA.pd.over(St, Dr.push.at(R, Dr.Layer{k, c}, p, b))), Some{Dr.Failed{}}} : Dr.Loop}
  +Z = {Dr.Loop{n, List.append(&2, Dr.Layer, St, Dr.Layer{k, c} <> b), Some{Dr.Failed{}}} : Dr.Loop}
  Equal.trans(Dr.Loop, X, Y, Z, e1, Equal.trans(Dr.Loop, Y, K, Z, e2, Equal.trans(Dr.Loop, K, W, Z, e3, e4)))
