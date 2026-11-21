# eukhe: the proof of LAW loop_failed_turn_never_waits
#
# PROOF: the turn is the loop's own (lj.settled_own), so the step is
# Lp.settled.mine, which computes to the gate with 1 + f failed turns.
# lfw.gate splits the condition: with one, the loop is judging and asks
# the check, the failed turns kept; with none, lfw.adv splits the bound
# the advance found: ended with its report, or in the next turn with its
# submission, the failed turns kept too.

import Base
import ../../bend/loop.bend as Lp
import ../../spec/loop/loop.bend as S
import ../../laws/loop/model.bend as Loop
import ./base/judged.bend as LALoopJudged

# the step r moves on (a phase with its own act) and keeps the failed
# turns it was given (f)
def lfw.Goes(r: Lp.St & Lp.Act, f: Nat) -> Type:
  {(S.moves_on(S.phase(S.state(r)), S.act(r)), S.fails(S.state(r))) == (True{}, f) : Bool & Nat}

def lfw.adv(h: Maybe<&2, Lp.End>, -i: Nat, -l: Maybe<&2, Nat>, -d: Maybe<&2, Nat>, -c: Lp.Cond, -b: String, -f: Nat, -x: Lp.Last) -> lfw.Goes(Lp.advance.on(h, i, l, d, c, b, f, x), f):
  match h:
    case Some{w}:
      {==}
    case None{}:
      {==}

def lfw.gate(c: Lp.Cond, -i: Nat, l: Maybe<&2, Nat>, d: Maybe<&2, Nat>, -b: String, f: Nat, -x: Lp.Last, now: Nat, fu: Bool) -> lfw.Goes(Lp.gate(c, i, l, d, b, f, x, now, fu), f):
  match c:
    case Lp.NoCond{}:
      lfw.adv(Lp.halt(f, fu, l, d, now), i, l, d, Lp.NoCond{}, b, f, x)
    case Lp.Until{cmd}:
      {==}
    case Lp.While{cmd}:
      {==}
    case Lp.Stated{u, t}:
      {==}

def Loop.loop_failed_turn_never_waits(i, l, d, c, b, f, x, now, fu):
  %LALoopJudged.lj.settled_own(i, l, d, c, b, f, x, Lp.Errored{}, False{}, now, fu) : lfw.Goes(_, 1n+f)
  lfw.gate(c, i, l, d, b, 1n+f, x, now, fu)
