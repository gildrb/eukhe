# eukhe: the proof of LAW dir_step_undecided

import Base
import ../../bend/director.bend as Dr
import ../../laws/director.bend as Director
import ../base/list.bend as LList
import ./base.bend as LA

# no layer decides: the decision hands back with the layers that stay
def pu.none(+s: List<&2, Dr.Layer>, +va: List<&2, Dr.Verdict>, +vr: List<&2, Dr.Verdict>, +r: Bool, +st: Bool, one: {Nat.is_eq(List.length(&2, Dr.Layer, s), List.length(&2, Dr.Verdict, va)) == True{} : Bool}, pass: {Director.dir_all_pass(va) == True{} : Bool}) -> {Dr.decide.go(s, List.append(&2, Dr.Verdict, va, vr), r, st) == Dr.Dec{Dr.Hand{}, Director.dir_stayers(s, va)} : Dr.Dec}:
  +St = Director.dir_stayers(s, va)
  +vs = List.append(&2, Dr.Verdict, va, vr)
  %LList.pd.app_nil(Dr.Layer, s) : {Dr.decide.go(_, vs, r, st) == Dr.Dec{Dr.Hand{}, St} : Dr.Dec}
  %LList.pd.app_nil(Dr.Layer, St) : {Dr.decide.go(List.append(&2, Dr.Layer, s, Nil{}), vs, r, st) == Dr.Dec{Dr.Hand{}, _} : Dr.Dec}
  LA.pd.go_split(s, va, Nil{}, vr, r, st, one, pass)

def pu.step(+n: Nat, +s: List<&2, Dr.Layer>, +va: List<&2, Dr.Verdict>, +vr: List<&2, Dr.Verdict>, +cap: Nat, +one: {Nat.is_eq(List.length(&2, Dr.Layer, s), List.length(&2, Dr.Verdict, va)) == True{} : Bool}, +pass: {Director.dir_all_pass(va) == True{} : Bool}) -> {Dr.tick(cap, Dr.Loop{n, s, None{}}, List.append(&2, Dr.Verdict, va, vr)) == Dr.Loop{n, Director.dir_stayers(s, va), Some{Dr.Hand{}}} : Dr.Loop}:
  +vs = List.append(&2, Dr.Verdict, va, vr)
  +R = Nat.is_lt(List.length(&2, Dr.Layer, s), cap)
  +St = Director.dir_stayers(s, va)
  Equal.trans(Dr.Loop, Dr.tick(cap, Dr.Loop{n, s, None{}}, vs), Dr.Loop{n, Dr.kept(s, vs, cap), Some{Dr.Hand{}}}, Dr.Loop{n, St, Some{Dr.Hand{}}}, Equal.cong(Dr.Dec, Dr.Loop, x => Dr.settle(x, n, s, vs, cap), Dr.decide.go(s, vs, R, False{}), Dr.Dec{Dr.Hand{}, St}, pu.none(s, va, vr, R, False{}, one, pass)), Equal.cong(List<&2, Dr.Layer>, Dr.Loop, x => Dr.Loop{n, x, Some{Dr.Hand{}}}, Dr.kept(s, vs, cap), St, Equal.cong(Dr.Dec, List<&2, Dr.Layer>, x => Dr.Dec.stack(x), Dr.decide.go(s, vs, R, True{}), Dr.Dec{Dr.Hand{}, St}, pu.none(s, va, vr, R, True{}, one, pass))))

def Director.dir_step_undecided(n, s, va, vr, cap, one, pass):
  pu.step(n, s, va, vr, cap, one, pass)
