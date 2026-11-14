# eukhe: the proof of LAW loop_stale_check_ignored
#
# PROOF: the premise is rewritten into the goal (lb.Unless); the phase is
# split: when not judging the step computes to the same state with Rest;
# judging, the Bool `Nat.is_eq(k, i)` is split: True leaves no goal (the
# premise is False), False computes to the same state with Rest.

import Base
import ../../bend/loop.bend as Lp
import ../../spec/loop/loop.bend as S
import ../../laws/loop/model.bend as Loop
import ./base/bounds.bend as LALoopBounds

def lsc.G(s: Lp.St, k: Nat, ev: Lp.Evid, bl: Bool, now: Nat, fu: Bool) -> Type:
  {Lp.step(s, Lp.Judged{k, ev, bl, now, fu}) == (s, Lp.Rest{}) : Lp.St & Lp.Act}

def lsc.judging(m: Bool, -i: Nat, -l: Maybe<&2, Nat>, -d: Maybe<&2, Nat>, -c: Lp.Cond, -b: String, -f: Nat, -x: Lp.Last, -ev: Lp.Evid, -bl: Bool, -now: Nat, -fu: Bool) -> LALoopBounds.lb.Unless(m, {Lp.judged(m, Lp.Judging{}, i, l, d, c, b, f, x, ev, bl, now, fu) == (Lp.St{Lp.Judging{}, i, l, d, c, b, f, x}, Lp.Rest{}) : Lp.St & Lp.Act}):
  match m:
    case True{}:
      Unit{}
    case False{}:
      {==}

def lsc.ignored(s: Lp.St, k: Nat, -ev: Lp.Evid, -bl: Bool, -now: Nat, -fu: Bool) -> LALoopBounds.lb.Unless(Bool.and(S.is_judging(S.phase(s)), Nat.is_eq(k, S.iter(s))), lsc.G(s, k, ev, bl, now, fu)):
  match s:
    case Lp.St{Lp.Off{}, i, l, d, c, b, f, x}:
      {==}
    case Lp.St{Lp.Armed{}, i, l, d, c, b, f, x}:
      {==}
    case Lp.St{Lp.Turn{}, i, l, d, c, b, f, x}:
      {==}
    case Lp.St{Lp.Judging{}, i, l, d, c, b, f, x}:
      lsc.judging(Nat.is_eq(k, i), i, l, d, c, b, f, x, ev, bl, now, fu)
    case Lp.St{Lp.Paused{}, i, l, d, c, b, f, x}:
      {==}
    case Lp.St{Lp.Ended{w}, i, l, d, c, b, f, x}:
      {==}

def Loop.loop_stale_check_ignored(s, k, ev, bl, now, fu, h):
  %h : LALoopBounds.lb.Unless(_, lsc.G(s, k, ev, bl, now, fu))
  lsc.ignored(s, k, ev, bl, now, fu)
