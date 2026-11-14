# eukhe: the proof of LAW loop_halted_turn_keeps
#
# PROOF: the halted turn is the loop's own (lb.turn_mine: Nat.is_eq(i, i)
# is True); the step computes to the paused state, which keeps every field
# read.

import Base
import ../../bend/loop.bend as Lp
import ../../spec/loop/loop.bend as S
import ../../laws/loop/model.bend as Loop
import ./base/bounds.bend as LALoopBounds

def Loop.loop_halted_turn_keeps(i, l, d, c, b, f, x, now, fu):
  +j = i
  %LALoopBounds.lb.turn_mine(j, l, d, c, b, f, x, Lp.Halted{}, False{}, now, fu) : {(S.iter(S.state(_)), (S.left(S.state(_)), (S.deadline(S.state(_)), (S.cond(S.state(_)), (S.fails(S.state(_)), S.last(S.state(_))))))) == (i, (l, (d, (c, (f, x))))) : Nat & (Maybe<&2, Nat> & (Maybe<&2, Nat> & (Lp.Cond & (Nat & Lp.Last))))}
  {==}
