# eukhe: the proof of LAW loop_take_up_judges
#
# PROOF: the restart of a loop in its turn computes to the same state, so
# each settle after it is the settle of the turn itself, the loop's own
# (lb.turn_mine: Nat.is_eq(i, i) is True), which computes to Lp.gate; the
# condition is split: with none the premise is False == True (Unit), each
# condition computes to the judging state of iteration i with the check
# asked and the failed turns cleared or one more.

import Base
import ../../bend/loop.bend as Lp
import ../../spec/loop/loop.bend as S
import ../../laws/loop/model.bend as Loop
import ./base/bounds.bend as LALoopBounds

def ltj.G(c: Lp.Cond, o: Lp.Out, f2: Nat, i: Nat, l: Maybe<&2, Nat>, d: Maybe<&2, Nat>, b: String, f: Nat, x: Lp.Last, now: Nat, fu: Bool) -> Type:
  {Lp.settled.mine(False{}, o, i, l, d, c, b, f, x, now, fu) == (Lp.St{Lp.Judging{}, i, l, d, c, b, f2, x}, Lp.Judge{i}) : Lp.St & Lp.Act}

def ltj.ran(c: Lp.Cond, -i: Nat, -l: Maybe<&2, Nat>, -d: Maybe<&2, Nat>, -b: String, -f: Nat, -x: Lp.Last, -now: Nat, -fu: Bool) -> LALoopBounds.lb.When(S.has_cond(c), ltj.G(c, Lp.Ran{}, 0n, i, l, d, b, f, x, now, fu)):
  match c:
    case Lp.NoCond{}:
      Unit{}
    case Lp.Until{cmd}:
      {==}
    case Lp.While{cmd}:
      {==}
    case Lp.Stated{u, t}:
      {==}

def ltj.errored(c: Lp.Cond, -i: Nat, -l: Maybe<&2, Nat>, -d: Maybe<&2, Nat>, -b: String, -f: Nat, -x: Lp.Last, -now: Nat, -fu: Bool) -> LALoopBounds.lb.When(S.has_cond(c), ltj.G(c, Lp.Errored{}, 1n+f, i, l, d, b, f, x, now, fu)):
  match c:
    case Lp.NoCond{}:
      Unit{}
    case Lp.Until{cmd}:
      {==}
    case Lp.While{cmd}:
      {==}
    case Lp.Stated{u, t}:
      {==}

def Loop.loop_take_up_judges(i, l, d, c, b, f, x, now, fu, hc):
  +j = i
  +h = hc
  (%LALoopBounds.lb.turn_mine(j, l, d, c, b, f, x, Lp.Ran{}, False{}, now, fu) : {_ == (Lp.St{Lp.Judging{}, i, l, d, c, b, 0n, x}, Lp.Judge{i}) : Lp.St & Lp.Act}; LALoopBounds.lb.when(S.has_cond(c), ltj.G(c, Lp.Ran{}, 0n, j, l, d, b, f, x, now, fu), h, ltj.ran(c, j, l, d, b, f, x, now, fu)),
   %LALoopBounds.lb.turn_mine(j, l, d, c, b, f, x, Lp.Errored{}, False{}, now, fu) : {_ == (Lp.St{Lp.Judging{}, i, l, d, c, b, 1n+f, x}, Lp.Judge{i}) : Lp.St & Lp.Act}; LALoopBounds.lb.when(S.has_cond(c), ltj.G(c, Lp.Errored{}, 1n+f, j, l, d, b, f, x, now, fu), h, ltj.errored(c, j, l, d, b, f, x, now, fu)))
