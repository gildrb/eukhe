# eukhe: the proof of LAW loop_failed_turn_counts
#
# PROOF: the condition is split: with none the premise is False == True;
# with one the event is the loop's own (lb.turn_mine: Nat.is_eq(i, i) is
# True) and the step of a failed turn computes to the gate with 1 + f
# failed turns, which asks for the check of iteration i.

import Base
import ../../bend/loop.bend as Lp
import ../../spec/loop/loop.bend as S
import ../../laws/loop/model.bend as Loop
import ./base/bounds.bend as LALoopBounds

def Loop.loop_failed_turn_counts(i, l, d, c, b, f, x, now, fu, hc):
  match c:
    case Lp.NoCond{}:
      LALoopBounds.lb.absurd_ft({(S.does(Lp.St{Lp.Turn{}, i, l, d, Lp.NoCond{}, b, f, x}, Lp.Settled{i, Lp.Errored{}, False{}, now, fu}), S.fails(S.next(Lp.St{Lp.Turn{}, i, l, d, Lp.NoCond{}, b, f, x}, Lp.Settled{i, Lp.Errored{}, False{}, now, fu}))) == (Lp.Judge{i}, 1n+f) : Lp.Act & Nat}, hc)
    case Lp.Until{cmd}:
      %LALoopBounds.lb.turn_mine(i, l, d, Lp.Until{cmd}, b, f, x, Lp.Errored{}, False{}, now, fu) : {(S.act(_), S.fails(S.state(_))) == (Lp.Judge{i}, 1n+f) : Lp.Act & Nat}
      {==}
    case Lp.While{cmd}:
      %LALoopBounds.lb.turn_mine(i, l, d, Lp.While{cmd}, b, f, x, Lp.Errored{}, False{}, now, fu) : {(S.act(_), S.fails(S.state(_))) == (Lp.Judge{i}, 1n+f) : Lp.Act & Nat}
      {==}
