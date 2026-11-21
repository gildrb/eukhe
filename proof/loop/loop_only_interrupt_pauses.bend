# eukhe: the proof of LAW loop_only_interrupt_pauses
#
# PROOF: the premise is rewritten into the goal (lj.IfN); the state and the
# event are split. A paused state has nothing to prove. The interrupt of a
# loop that is on computes to the pause; every other event computes to a
# phase that is not paused, or reaches a def that matches on a value the
# step computes: the start of a new loop (loi.start: armed or in a turn),
# the loop's own settled turn (loi.settled: deferred, the check, or the
# advance), its own judged check (loi.judged, loi.cond, loi.verdict: the
# end, the advance, or the check again), and the advance (loi.adv: the end
# or the next turn). None of them is the pause.

import Base
import ../../bend/loop.bend as Lp
import ../../spec/loop/loop.bend as S
import ../../laws/loop/model.bend as Loop
import ./base/judged.bend as LALoopJudged

def loi.G(s: Lp.St, e: Lp.Ev) -> Type:
  {S.is_paused(S.phase(S.next(s, e))) == Bool.and(S.is_abort(e), S.is_on(S.phase(s))) : Bool}

# the step r leaves the loop not paused
def loi.Calm(r: Lp.St & Lp.Act) -> Type:
  {S.is_paused(S.phase(S.state(r))) == False{} : Bool}

def loi.adv(h: Maybe<&2, Lp.End>, -i: Nat, -l: Maybe<&2, Nat>, -d: Maybe<&2, Nat>, -c: Lp.Cond, -b: String, -f: Nat, -x: Lp.Last) -> loi.Calm(Lp.advance.on(h, i, l, d, c, b, f, x)):
  match h:
    case Some{w}:
      {==}
    case None{}:
      {==}

def loi.gate(c: Lp.Cond, -i: Nat, l: Maybe<&2, Nat>, d: Maybe<&2, Nat>, -b: String, f: Nat, -x: Lp.Last, now: Nat, fu: Bool) -> loi.Calm(Lp.gate(c, i, l, d, b, f, x, now, fu)):
  match c:
    case Lp.NoCond{}:
      loi.adv(Lp.halt(f, fu, l, d, now), i, l, d, Lp.NoCond{}, b, f, x)
    case Lp.Until{cmd}:
      {==}
    case Lp.While{cmd}:
      {==}
    case Lp.Stated{u, t}:
      {==}

def loi.settled(m: Bool, bl: Bool, o: Lp.Out, c: Lp.Cond, -i: Nat, l: Maybe<&2, Nat>, d: Maybe<&2, Nat>, -b: String, f: Nat, -x: Lp.Last, now: Nat, fu: Bool) -> loi.Calm(Lp.settled(m, Lp.Turn{}, i, l, d, c, b, f, x, o, bl, now, fu)):
  match m bl o:
    case False{} _ _:
      {==}
    case True{} True{} _:
      {==}
    case True{} False{} Lp.Ran{}:
      loi.gate(c, i, l, d, b, 0n, x, now, fu)
    case True{} False{} Lp.Errored{}:
      loi.gate(c, i, l, d, b, 1n+f, x, now, fu)

def loi.verdict(v: Lp.Verdict, -i: Nat, l: Maybe<&2, Nat>, d: Maybe<&2, Nat>, -c: Lp.Cond, -b: String, f: Nat, -x: Lp.Last, -ev: Lp.Evid, now: Nat, fu: Bool) -> loi.Calm(Lp.judged.verdict(v, i, l, d, c, b, f, x, ev, now, fu)):
  match v:
    case Lp.Confirmed{}:
      {==}
    case Lp.Refuted{}:
      loi.adv(Lp.halt(f, fu, l, d, now), i, l, d, c, b, f, Lp.Check{i, ev})
    case Lp.Broken{}:
      {==}
    case Lp.Unjudged{}:
      {==}

def loi.cond(c: Lp.Cond, -i: Nat, l: Maybe<&2, Nat>, d: Maybe<&2, Nat>, -b: String, f: Nat, -x: Lp.Last, ev: Lp.Evid, now: Nat, fu: Bool) -> loi.Calm(Lp.judged.cond(c, i, l, d, b, f, x, ev, now, fu)):
  match c:
    case Lp.NoCond{}:
      loi.adv(Lp.halt(f, fu, l, d, now), i, l, d, Lp.NoCond{}, b, f, x)
    case Lp.Until{cmd}:
      loi.verdict(Lp.judge(True{}, ev), i, l, d, Lp.Until{cmd}, b, f, x, ev, now, fu)
    case Lp.While{cmd}:
      loi.verdict(Lp.judge(False{}, ev), i, l, d, Lp.While{cmd}, b, f, x, ev, now, fu)
    case Lp.Stated{u, t}:
      loi.verdict(Lp.said(u, ev), i, l, d, Lp.Stated{u, t}, b, f, x, ev, now, fu)

def loi.judged(m: Bool, bl: Bool, c: Lp.Cond, -i: Nat, l: Maybe<&2, Nat>, d: Maybe<&2, Nat>, -b: String, f: Nat, -x: Lp.Last, ev: Lp.Evid, now: Nat, fu: Bool) -> loi.Calm(Lp.judged(m, Lp.Judging{}, i, l, d, c, b, f, x, ev, bl, now, fu)):
  match m bl:
    case False{} _:
      {==}
    case True{} True{}:
      {==}
    case True{} False{}:
      loi.cond(c, i, l, d, b, f, x, ev, now, fu)

def loi.start(lim: Lp.Limit, -c: Lp.Cond, pr: Maybe<&2, String>, -now: Nat) -> loi.Calm(Lp.start(lim, c, pr, now)):
  match pr:
    case None{}:
      {==}
    case Some{t}:
      {==}

def loi.all(s: Lp.St, e: Lp.Ev) -> LALoopJudged.lj.IfN(S.is_paused(S.phase(s)), loi.G(s, e)):
  match s:
    case Lp.St{p, i, l, d, c, b, f, x}:
      match p e:
        case Lp.Off{} Lp.Enter{lim, c2, pr, now}:
          loi.start(lim, c2, pr, now)
        case Lp.Off{} Lp.Stop{}:
          {==}
        case Lp.Off{} Lp.Abort{}:
          {==}
        case Lp.Off{} Lp.Prompt{t}:
          {==}
        case Lp.Off{} Lp.Settled{k, o, bl, now, fu}:
          {==}
        case Lp.Off{} Lp.Judged{k, ev, bl, now, fu}:
          {==}
        case Lp.Off{} Lp.Restart{}:
          {==}
        case Lp.Armed{} Lp.Enter{lim, c2, pr, now}:
          {==}
        case Lp.Armed{} Lp.Stop{}:
          {==}
        case Lp.Armed{} Lp.Abort{}:
          {==}
        case Lp.Armed{} Lp.Prompt{t}:
          {==}
        case Lp.Armed{} Lp.Settled{k, o, bl, now, fu}:
          {==}
        case Lp.Armed{} Lp.Judged{k, ev, bl, now, fu}:
          {==}
        case Lp.Armed{} Lp.Restart{}:
          {==}
        case Lp.Turn{} Lp.Enter{lim, c2, pr, now}:
          {==}
        case Lp.Turn{} Lp.Stop{}:
          {==}
        case Lp.Turn{} Lp.Abort{}:
          {==}
        case Lp.Turn{} Lp.Prompt{t}:
          {==}
        case Lp.Turn{} Lp.Settled{k, o, bl, now, fu}:
          loi.settled(Nat.is_eq(k, i), bl, o, c, i, l, d, b, f, x, now, fu)
        case Lp.Turn{} Lp.Judged{k, ev, bl, now, fu}:
          {==}
        case Lp.Turn{} Lp.Restart{}:
          {==}
        case Lp.Judging{} Lp.Enter{lim, c2, pr, now}:
          {==}
        case Lp.Judging{} Lp.Stop{}:
          {==}
        case Lp.Judging{} Lp.Abort{}:
          {==}
        case Lp.Judging{} Lp.Prompt{t}:
          {==}
        case Lp.Judging{} Lp.Settled{k, o, bl, now, fu}:
          {==}
        case Lp.Judging{} Lp.Judged{k, ev, bl, now, fu}:
          loi.judged(Nat.is_eq(k, i), bl, c, i, l, d, b, f, x, ev, now, fu)
        case Lp.Judging{} Lp.Restart{}:
          {==}
        case Lp.Paused{} _:
          Unit{}
        case Lp.Ended{w} Lp.Enter{lim, c2, pr, now}:
          loi.start(lim, c2, pr, now)
        case Lp.Ended{w} Lp.Stop{}:
          {==}
        case Lp.Ended{w} Lp.Abort{}:
          {==}
        case Lp.Ended{w} Lp.Prompt{t}:
          {==}
        case Lp.Ended{w} Lp.Settled{k, o, bl, now, fu}:
          {==}
        case Lp.Ended{w} Lp.Judged{k, ev, bl, now, fu}:
          {==}
        case Lp.Ended{w} Lp.Restart{}:
          {==}

def Loop.loop_only_interrupt_pauses(s, e, np):
  %np : LALoopJudged.lj.IfN(_, loi.G(s, e))
  loi.all(s, e)
