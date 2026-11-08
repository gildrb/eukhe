# eukhe: the proof of LAW dir_step_out_of_steps

import Base
import ../../bend/director.bend as Dr
import ../../laws/director.bend as Director
import ../base/logic/logic.bend as LLogicLogic
import ./dir_lead_stays_when_the_loop_ends.bend as PL
import ./base.bend as LA

# a settle with one step left that keeps the loop running is a continue
def po.cont1(d: Dr.Dec, +s: List<&2, Dr.Layer>, +vs: List<&2, Dr.Verdict>, +cap: Nat, +t: List<&2, Dr.Layer>, h: {Dr.settle(d, 1n, s, vs, cap) == Dr.Loop{0n, t, None{}} : Dr.Loop}) -> {d == Dr.Dec{Dr.Cont{}, t} : Dr.Dec}:
  match d:
    case Dr.Dec{o, +t2}:
      match o:
        case Dr.Cont{}:
          Equal.cong(Dr.Loop, Dr.Dec, x => Dr.Dec{Dr.Cont{}, Dr.Loop.stack(x)}, Dr.Loop{0n, t2, None{}}, Dr.Loop{0n, t, None{}}, h)
        case Dr.Hand{}:
          LLogicLogic.tree.pt.absurdF({Dr.Dec{Dr.Hand{}, t2} == Dr.Dec{Dr.Cont{}, t} : Dr.Dec}, Equal.sym(Bool, True{}, False{}, Equal.cong(Dr.Loop, Bool, x => Dr.ended(x), Dr.Loop{1n, Dr.kept(s, vs, cap), Some{Dr.Hand{}}}, Dr.Loop{0n, t, None{}}, h)))
        case Dr.Failed{}:
          LLogicLogic.tree.pt.absurdF({Dr.Dec{Dr.Failed{}, t2} == Dr.Dec{Dr.Cont{}, t} : Dr.Dec}, Equal.sym(Bool, True{}, False{}, Equal.cong(Dr.Loop, Bool, x => Dr.ended(x), Dr.Loop{1n, Dr.kept(s, vs, cap), Some{Dr.Failed{}}}, Dr.Loop{0n, t, None{}}, h)))

# a continue with no step left yields with the kept stack
def po.settle0(d: Dr.Dec, +s: List<&2, Dr.Layer>, +vs: List<&2, Dr.Verdict>, +cap: Nat, eo: {Dr.Dec.out(d) == Dr.Cont{} : Dr.Out}) -> {Dr.settle(d, 0n, s, vs, cap) == Dr.Loop{0n, Dr.kept(s, vs, cap), Some{Dr.Hand{}}} : Dr.Loop}:
  match d:
    case Dr.Dec{o, t}:
      match o:
        case Dr.Cont{}:
          {==}
        case Dr.Hand{}:
          LA.pd.out_absurd({Dr.settle(Dr.Dec{Dr.Hand{}, t}, 0n, s, vs, cap) == Dr.Loop{0n, Dr.kept(s, vs, cap), Some{Dr.Hand{}}} : Dr.Loop}, Dr.Hand{}, Dr.Cont{}, eo, {==})
        case Dr.Failed{}:
          LA.pd.out_absurd({Dr.settle(Dr.Dec{Dr.Failed{}, t}, 0n, s, vs, cap) == Dr.Loop{0n, Dr.kept(s, vs, cap), Some{Dr.Hand{}}} : Dr.Loop}, Dr.Failed{}, Dr.Cont{}, eo, {==})

def Director.dir_step_out_of_steps(cap, s, vs, t, on):
  +Df = Director.dir_leads(vs, Dr.Defer{})
  +R = Nat.is_lt(List.length(&2, Dr.Layer, s), cap)
  +D = Dr.decide.go(s, vs, R, False{})
  +E = Dr.decide.go(s, vs, R, True{})
  +eD = po.cont1(Dr.decide.go(s, Df, R, False{}), s, Df, cap, t, on)
  +eE = Equal.trans(Dr.Dec, E, Dr.decide.go(s, Df, R, False{}), Dr.Dec{Dr.Cont{}, t}, PL.pd.defer_as(s, vs, R, False{}), eD)
  +eo = Equal.trans(Dr.Out, Dr.Dec.out(D), Dr.Dec.out(E), Dr.Cont{}, Equal.sym(Dr.Out, Dr.Dec.out(E), Dr.Dec.out(D), PL.pd.out_stay(s, vs, R)), Equal.cong(Dr.Dec, Dr.Out, x => Dr.Dec.out(x), E, Dr.Dec{Dr.Cont{}, t}, eE))
  Equal.trans(Dr.Loop, Dr.settle(D, 0n, s, vs, cap), Dr.Loop{0n, Dr.kept(s, vs, cap), Some{Dr.Hand{}}}, Dr.Loop{0n, t, Some{Dr.Hand{}}}, po.settle0(D, s, vs, cap, eo), Equal.cong(List<&2, Dr.Layer>, Dr.Loop, k => Dr.Loop{0n, k, Some{Dr.Hand{}}}, Dr.kept(s, vs, cap), t, Equal.cong(Dr.Dec, List<&2, Dr.Layer>, x => Dr.Dec.stack(x), E, Dr.Dec{Dr.Cont{}, t}, eE)))
