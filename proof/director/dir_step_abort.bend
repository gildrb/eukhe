# eukhe: the proof of LAW dir_step_abort

import Base
import ../../bend/director.bend as Dr
import ../../laws/director.bend as Director
import ./base.bend as LA

def Director.dir_step_abort(n, a, d, b, va, vr, cap, one, pass):
  +o = one
  +q = pass
  +St = Director.dir_stayers(a, va)
  +s = List.append(&2, Dr.Layer, a, d <> b)
  +vs = List.append(&2, Dr.Verdict, va, Dr.Abort{} <> vr)
  Equal.trans(Dr.Loop, Dr.tick(cap, Dr.Loop{n, s, None{}}, vs), Dr.Loop{n, Dr.kept(s, vs, cap), Some{Dr.Failed{}}}, Dr.Loop{n, List.append(&2, Dr.Layer, St, d <> b), Some{Dr.Failed{}}}, LA.pd.step_at(n, a, d, b, va, Dr.Abort{}, vr, cap, o, q), Equal.cong(List<&2, Dr.Layer>, Dr.Loop, k => Dr.Loop{n, k, Some{Dr.Failed{}}}, Dr.kept(s, vs, cap), List.append(&2, Dr.Layer, St, d <> b), LA.pd.kept_at(a, d, b, va, Dr.Abort{}, vr, cap, o, q)))
