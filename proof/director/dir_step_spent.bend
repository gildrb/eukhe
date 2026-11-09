# eukhe: the proof of LAW dir_step_spent

import Base
import ../../bend/director.bend as Dr
import ../../laws/director.bend as Director
import ../base/logic/logic.bend as LLogicLogic
import ./base.bend as LA

# the step, by the deciding layer's verdict
def ps.spent(v: Dr.Verdict, +n: Nat, +a: List<&2, Dr.Layer>, +k: Nat, +b: List<&2, Dr.Layer>, +va: List<&2, Dr.Verdict>, +vr: List<&2, Dr.Verdict>, +cap: Nat, +one: {Nat.is_eq(List.length(&2, Dr.Layer, a), List.length(&2, Dr.Verdict, va)) == True{} : Bool}, +pass: {Director.dir_all_pass(va) == True{} : Bool}, asks: {Director.dir_asks_a_step(v) == True{} : Bool}) -> {Dr.tick(cap, Dr.Loop{n, List.append(&2, Dr.Layer, a, Dr.Layer{k, 0n} <> b), None{}}, List.append(&2, Dr.Verdict, va, v <> vr)) == Dr.Loop{n, List.append(&2, Dr.Layer, Director.dir_stayers(a, va), Dr.Layer{k, 0n} <> b), Some{Dr.Hand{}}} : Dr.Loop}:
  match v:
    case Dr.Defer{}:
      LLogicLogic.tree.pt.absurdF({Dr.tick(cap, Dr.Loop{n, List.append(&2, Dr.Layer, a, Dr.Layer{k, 0n} <> b), None{}}, List.append(&2, Dr.Verdict, va, Dr.Defer{} <> vr)) == Dr.Loop{n, List.append(&2, Dr.Layer, Director.dir_stayers(a, va), Dr.Layer{k, 0n} <> b), Some{Dr.Hand{}}} : Dr.Loop}, asks)
    case Dr.Again{}:
      +s = List.append(&2, Dr.Layer, a, Dr.Layer{k, 0n} <> b)
      +vs = List.append(&2, Dr.Verdict, va, Dr.Again{} <> vr)
      +St = Director.dir_stayers(a, va)
      Equal.trans(Dr.Loop, Dr.tick(cap, Dr.Loop{n, s, None{}}, vs), Dr.Loop{n, Dr.kept(s, vs, cap), Some{Dr.Hand{}}}, Dr.Loop{n, List.append(&2, Dr.Layer, St, Dr.Layer{k, 0n} <> b), Some{Dr.Hand{}}}, LA.pd.step_at(n, a, Dr.Layer{k, 0n}, b, va, Dr.Again{}, vr, cap, one, pass), Equal.cong(List<&2, Dr.Layer>, Dr.Loop, x => Dr.Loop{n, x, Some{Dr.Hand{}}}, Dr.kept(s, vs, cap), List.append(&2, Dr.Layer, St, Dr.Layer{k, 0n} <> b), LA.pd.kept_at(a, Dr.Layer{k, 0n}, b, va, Dr.Again{}, vr, cap, one, pass)))
    case Dr.Yield{}:
      LLogicLogic.tree.pt.absurdF({Dr.tick(cap, Dr.Loop{n, List.append(&2, Dr.Layer, a, Dr.Layer{k, 0n} <> b), None{}}, List.append(&2, Dr.Verdict, va, Dr.Yield{} <> vr)) == Dr.Loop{n, List.append(&2, Dr.Layer, Director.dir_stayers(a, va), Dr.Layer{k, 0n} <> b), Some{Dr.Hand{}}} : Dr.Loop}, asks)
    case Dr.Stack{+p}:
      +s = List.append(&2, Dr.Layer, a, Dr.Layer{k, 0n} <> b)
      +vs = List.append(&2, Dr.Verdict, va, Dr.Stack{p} <> vr)
      +St = Director.dir_stayers(a, va)
      Equal.trans(Dr.Loop, Dr.tick(cap, Dr.Loop{n, s, None{}}, vs), Dr.Loop{n, Dr.kept(s, vs, cap), Some{Dr.Hand{}}}, Dr.Loop{n, List.append(&2, Dr.Layer, St, Dr.Layer{k, 0n} <> b), Some{Dr.Hand{}}}, LA.pd.step_at(n, a, Dr.Layer{k, 0n}, b, va, Dr.Stack{p}, vr, cap, one, pass), Equal.cong(List<&2, Dr.Layer>, Dr.Loop, x => Dr.Loop{n, x, Some{Dr.Hand{}}}, Dr.kept(s, vs, cap), List.append(&2, Dr.Layer, St, Dr.Layer{k, 0n} <> b), LA.pd.kept_at(a, Dr.Layer{k, 0n}, b, va, Dr.Stack{p}, vr, cap, one, pass)))
    case Dr.Unstack{}:
      LLogicLogic.tree.pt.absurdF({Dr.tick(cap, Dr.Loop{n, List.append(&2, Dr.Layer, a, Dr.Layer{k, 0n} <> b), None{}}, List.append(&2, Dr.Verdict, va, Dr.Unstack{} <> vr)) == Dr.Loop{n, List.append(&2, Dr.Layer, Director.dir_stayers(a, va), Dr.Layer{k, 0n} <> b), Some{Dr.Hand{}}} : Dr.Loop}, asks)
    case Dr.Abort{}:
      LLogicLogic.tree.pt.absurdF({Dr.tick(cap, Dr.Loop{n, List.append(&2, Dr.Layer, a, Dr.Layer{k, 0n} <> b), None{}}, List.append(&2, Dr.Verdict, va, Dr.Abort{} <> vr)) == Dr.Loop{n, List.append(&2, Dr.Layer, Director.dir_stayers(a, va), Dr.Layer{k, 0n} <> b), Some{Dr.Hand{}}} : Dr.Loop}, asks)
    case Dr.Lead{}:
      LLogicLogic.tree.pt.absurdF({Dr.tick(cap, Dr.Loop{n, List.append(&2, Dr.Layer, a, Dr.Layer{k, 0n} <> b), None{}}, List.append(&2, Dr.Verdict, va, Dr.Lead{} <> vr)) == Dr.Loop{n, List.append(&2, Dr.Layer, Director.dir_stayers(a, va), Dr.Layer{k, 0n} <> b), Some{Dr.Hand{}}} : Dr.Loop}, asks)

def Director.dir_step_spent(n, a, k, b, va, v, vr, cap, one, pass, asks):
  ps.spent(v, n, a, k, b, va, vr, cap, one, pass, asks)
