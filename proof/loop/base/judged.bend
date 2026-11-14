# eukhe: lemmas the proofs of area loop, section model, share (topic
# judged: the verdict, the start and the stop, what is sent again). A law
# with a Bool premise is proven as lj.If(premise, claim): a case where the
# premise computes to False has nothing to prove (Unit), and the fill
# rewrites its goal with the premise. Where Lp.step tests Nat.is_eq(k, i)
# the lemma takes that Bool as a parameter m and matches on it.

import Base
import ../../../bend/loop.bend as Lp
import ../../../spec/loop/loop.bend as S

# Logic
# -----

# G when b is True; nothing to prove when it is False
def lj.If(b: Bool, G: Type) -> Type:
  match b:
    case True{}:
      G
    case False{}:
      Unit

# G when b is False; nothing to prove when it is True
def lj.IfN(b: Bool, G: Type) -> Type:
  match b:
    case True{}:
      Unit
    case False{}:
      G

# a proven claim holds under any premise
def lj.if_any(b: Bool, -G: Type, g: G) -> lj.If(b, G):
  match b:
    case True{}:
      g
    case False{}:
      Unit{}

# a premise not(a) and a never holds
def lj.if_not_self(a: Bool, -G: Type) -> lj.If(Bool.and(Bool.not(a), a), G):
  match a:
    case True{}:
      Unit{}
    case False{}:
      Unit{}

# a premise a and False never holds
def lj.if_and_f(a: Bool, -G: Type) -> lj.If(Bool.and(a, False{}), G):
  match a:
    case True{}:
      Unit{}
    case False{}:
      Unit{}

# a claim under b, itself under a, holds under a and b
def lj.if_and(a: Bool, -b: Bool, -G: Type, x: lj.If(b, lj.If(a, G))) -> lj.If(Bool.and(a, b), G):
  match a:
    case True{}:
      x
    case False{}:
      Unit{}

def lj.and2(-a: Bool, -b: Bool, ha: {a == True{} : Bool}, hb: {b == True{} : Bool}) -> {Bool.and(a, b) == True{} : Bool}:
  %Equal.sym(Bool, a, True{}, ha) : {Bool.and(_, b) == True{} : Bool}
  hb

def lj.not_t(-a: Bool, h: {a == False{} : Bool}) -> {Bool.not(a) == True{} : Bool}:
  %Equal.sym(Bool, a, False{}, h) : {Bool.not(_) == True{} : Bool}
  {==}

def lj.eq_refl(i: Nat) -> {True{} == Nat.is_eq(i, i) : Bool}:
  match i:
    case 0n:
      {==}
    case 1n+p:
      lj.eq_refl(p)

# The loop's own events
# ---------------------

# a settled turn of the iteration in flight is the loop's own
def lj.settled_own(i: Nat, -l: Maybe<&2, Nat>, -d: Maybe<&2, Nat>, -c: Lp.Cond, -b: String, -f: Nat, -x: Lp.Last, -o: Lp.Out, -bl: Bool, -now: Nat, -fu: Bool) -> {Lp.settled.mine(bl, o, i, l, d, c, b, f, x, now, fu) == Lp.step(Lp.St{Lp.Turn{}, i, l, d, c, b, f, x}, Lp.Settled{i, o, bl, now, fu}) : Lp.St & Lp.Act}:
  %lj.eq_refl(i) : {Lp.settled.mine(bl, o, i, l, d, c, b, f, x, now, fu) == Lp.settled(_, Lp.Turn{}, i, l, d, c, b, f, x, o, bl, now, fu) : Lp.St & Lp.Act}
  {==}

# a judged check of the iteration judged is the loop's own
def lj.judged_own(i: Nat, -l: Maybe<&2, Nat>, -d: Maybe<&2, Nat>, -c: Lp.Cond, -b: String, -f: Nat, -x: Lp.Last, -ev: Lp.Evid, -bl: Bool, -now: Nat, -fu: Bool) -> {Lp.judged.mine(bl, i, l, d, c, b, f, x, ev, now, fu) == Lp.step(Lp.St{Lp.Judging{}, i, l, d, c, b, f, x}, Lp.Judged{i, ev, bl, now, fu}) : Lp.St & Lp.Act}:
  %lj.eq_refl(i) : {Lp.judged.mine(bl, i, l, d, c, b, f, x, ev, now, fu) == Lp.judged(_, Lp.Judging{}, i, l, d, c, b, f, x, ev, bl, now, fu) : Lp.St & Lp.Act}
  {==}

# The verdict (L3)
# ----------------

# loop_settled_turn_is_judged, once the turn is the loop's own
def lj.settled_judged(c: Lp.Cond, o: Lp.Out, -i: Nat, -l: Maybe<&2, Nat>, -d: Maybe<&2, Nat>, -b: String, -f: Nat, -x: Lp.Last, -now: Nat, -fu: Bool) -> lj.If(Bool.and(S.has_cond(c), Bool.not(S.out_halted(o))), {(S.act(Lp.settled.mine(False{}, o, i, l, d, c, b, f, x, now, fu)), S.phase(S.state(Lp.settled.mine(False{}, o, i, l, d, c, b, f, x, now, fu)))) == (Lp.Judge{i}, Lp.Judging{}) : Lp.Act & Lp.Phase}):
  match c o:
    case Lp.NoCond{} _:
      Unit{}
    case Lp.Until{cmd} Lp.Ran{}:
      {==}
    case Lp.Until{cmd} Lp.Errored{}:
      {==}
    case Lp.Until{cmd} Lp.Halted{}:
      Unit{}
    case Lp.While{cmd} Lp.Ran{}:
      {==}
    case Lp.While{cmd} Lp.Errored{}:
      {==}
    case Lp.While{cmd} Lp.Halted{}:
      Unit{}

# a nonzero exit of a `--while` condition, neither 126 nor 127 (bb, the
# test of those two, False), ends the loop satisfied
def lj.confirmed_w(bb: Bool, -cmd: String, -k: Nat, -i: Nat, -l: Maybe<&2, Nat>, -d: Maybe<&2, Nat>, -b: String, -f: Nat, -x: Lp.Last, -now: Nat, -fu: Bool) -> lj.If(Bool.not(bb), {Lp.judged.verdict(Lp.judge.nonzero(bb, Lp.Confirmed{}), i, l, d, Lp.While{cmd}, b, f, x, Lp.Exited{1n+k}, now, fu) == (Lp.St{Lp.Ended{Lp.Satisfied{}}, i, l, d, Lp.While{cmd}, b, f, Lp.Check{i, Lp.Exited{1n+k}}}, Lp.Report{Lp.Satisfied{}}) : Lp.St & Lp.Act}):
  match bb:
    case True{}:
      Unit{}
    case False{}:
      {==}

# loop_confirmed_ends, once the check is the loop's own
def lj.confirmed(c: Lp.Cond, ev: Lp.Evid, -i: Nat, -l: Maybe<&2, Nat>, -d: Maybe<&2, Nat>, -b: String, -f: Nat, -x: Lp.Last, -now: Nat, -fu: Bool) -> lj.If(S.shows_stop(c, ev), {Lp.judged.mine(False{}, i, l, d, c, b, f, x, ev, now, fu) == (Lp.St{Lp.Ended{Lp.Satisfied{}}, i, l, d, c, b, f, Lp.Check{i, ev}}, Lp.Report{Lp.Satisfied{}}) : Lp.St & Lp.Act}):
  match c ev:
    case Lp.NoCond{} _:
      Unit{}
    case Lp.Until{cmd} Lp.Exited{0n}:
      {==}
    case Lp.Until{cmd} Lp.Exited{1n+k}:
      Unit{}
    case Lp.Until{cmd} Lp.NoStatus{}:
      Unit{}
    case Lp.Until{cmd} Lp.TimedOut{}:
      Unit{}
    case Lp.Until{cmd} Lp.SpawnFailed{}:
      Unit{}
    case Lp.Until{cmd} Lp.Cancelled{}:
      Unit{}
    case Lp.While{cmd} Lp.Exited{0n}:
      Unit{}
    case Lp.While{cmd} Lp.Exited{1n++k}:
      lj.confirmed_w(Lp.cannot_run(1n+k), cmd, k, i, l, d, b, f, x, now, fu)
    case Lp.While{cmd} Lp.NoStatus{}:
      Unit{}
    case Lp.While{cmd} Lp.TimedOut{}:
      Unit{}
    case Lp.While{cmd} Lp.SpawnFailed{}:
      Unit{}
    case Lp.While{cmd} Lp.Cancelled{}:
      Unit{}

# the four premises of loop_broken_check_ends, as one
def lj.broken_if(-c: Lp.Cond, -ev: Lp.Evid, hc: {S.has_cond(c) == True{} : Bool}, hd: {S.decides(ev) == True{} : Bool}, hs: {S.shows_stop(c, ev) == False{} : Bool}, hg: {S.shows_go(c, ev) == False{} : Bool}) -> {Bool.and(S.has_cond(c), Bool.and(S.decides(ev), Bool.and(Bool.not(S.shows_stop(c, ev)), Bool.not(S.shows_go(c, ev))))) == True{} : Bool}:
  lj.and2(S.has_cond(c), Bool.and(S.decides(ev), Bool.and(Bool.not(S.shows_stop(c, ev)), Bool.not(S.shows_go(c, ev)))), hc, lj.and2(S.decides(ev), Bool.and(Bool.not(S.shows_stop(c, ev)), Bool.not(S.shows_go(c, ev))), hd, lj.and2(Bool.not(S.shows_stop(c, ev)), Bool.not(S.shows_go(c, ev)), lj.not_t(S.shows_stop(c, ev), hs), lj.not_t(S.shows_go(c, ev), hg))))

# a nonzero exit of a condition is a broken check exactly when it is 126
# or 127 (bb, the test of those two, True)
def lj.broken_u(bb: Bool, -cmd: String, -k: Nat, -i: Nat, -l: Maybe<&2, Nat>, -d: Maybe<&2, Nat>, -b: String, -f: Nat, -x: Lp.Last, -now: Nat, -fu: Bool) -> lj.If(Bool.not(Bool.not(bb)), {(S.act(Lp.judged.verdict(Lp.judge.nonzero(bb, Lp.Refuted{}), i, l, d, Lp.Until{cmd}, b, f, x, Lp.Exited{1n+k}, now, fu)), S.phase(S.state(Lp.judged.verdict(Lp.judge.nonzero(bb, Lp.Refuted{}), i, l, d, Lp.Until{cmd}, b, f, x, Lp.Exited{1n+k}, now, fu)))) == (Lp.Report{Lp.CheckBroke{}}, Lp.Ended{Lp.CheckBroke{}}) : Lp.Act & Lp.Phase}):
  match bb:
    case True{}:
      {==}
    case False{}:
      Unit{}

def lj.broken_w(bb: Bool, -cmd: String, -k: Nat, -i: Nat, -l: Maybe<&2, Nat>, -d: Maybe<&2, Nat>, -b: String, -f: Nat, -x: Lp.Last, -now: Nat, -fu: Bool) -> lj.If(Bool.and(Bool.not(Bool.not(bb)), True{}), {(S.act(Lp.judged.verdict(Lp.judge.nonzero(bb, Lp.Confirmed{}), i, l, d, Lp.While{cmd}, b, f, x, Lp.Exited{1n+k}, now, fu)), S.phase(S.state(Lp.judged.verdict(Lp.judge.nonzero(bb, Lp.Confirmed{}), i, l, d, Lp.While{cmd}, b, f, x, Lp.Exited{1n+k}, now, fu)))) == (Lp.Report{Lp.CheckBroke{}}, Lp.Ended{Lp.CheckBroke{}}) : Lp.Act & Lp.Phase}):
  match bb:
    case True{}:
      {==}
    case False{}:
      Unit{}

# loop_broken_check_ends, once the check is the loop's own
def lj.broken(c: Lp.Cond, ev: Lp.Evid, -i: Nat, -l: Maybe<&2, Nat>, -d: Maybe<&2, Nat>, -b: String, -f: Nat, -x: Lp.Last, -now: Nat, -fu: Bool) -> lj.If(Bool.and(S.has_cond(c), Bool.and(S.decides(ev), Bool.and(Bool.not(S.shows_stop(c, ev)), Bool.not(S.shows_go(c, ev))))), {(S.act(Lp.judged.mine(False{}, i, l, d, c, b, f, x, ev, now, fu)), S.phase(S.state(Lp.judged.mine(False{}, i, l, d, c, b, f, x, ev, now, fu)))) == (Lp.Report{Lp.CheckBroke{}}, Lp.Ended{Lp.CheckBroke{}}) : Lp.Act & Lp.Phase}):
  match c ev:
    case Lp.NoCond{} _:
      Unit{}
    case Lp.Until{cmd} Lp.Exited{0n}:
      Unit{}
    case Lp.Until{cmd} Lp.Exited{1n++k}:
      lj.broken_u(Lp.cannot_run(1n+k), cmd, k, i, l, d, b, f, x, now, fu)
    case Lp.Until{cmd} Lp.NoStatus{}:
      {==}
    case Lp.Until{cmd} Lp.TimedOut{}:
      {==}
    case Lp.Until{cmd} Lp.SpawnFailed{}:
      {==}
    case Lp.Until{cmd} Lp.Cancelled{}:
      Unit{}
    case Lp.While{cmd} Lp.Exited{0n}:
      Unit{}
    case Lp.While{cmd} Lp.Exited{1n++k}:
      lj.broken_w(Lp.cannot_run(1n+k), cmd, k, i, l, d, b, f, x, now, fu)
    case Lp.While{cmd} Lp.NoStatus{}:
      {==}
    case Lp.While{cmd} Lp.TimedOut{}:
      {==}
    case Lp.While{cmd} Lp.SpawnFailed{}:
      {==}
    case Lp.While{cmd} Lp.Cancelled{}:
      Unit{}

# loop_cancelled_check_waits, once the check is the loop's own
def lj.cancelled(c: Lp.Cond, -i: Nat, -l: Maybe<&2, Nat>, -d: Maybe<&2, Nat>, -b: String, -f: Nat, -x: Lp.Last, -now: Nat, -fu: Bool) -> lj.If(S.has_cond(c), {Lp.judged.mine(False{}, i, l, d, c, b, f, x, Lp.Cancelled{}, now, fu) == (Lp.St{Lp.Judging{}, i, l, d, c, b, f, x}, Lp.Rest{}) : Lp.St & Lp.Act}):
  match c:
    case Lp.NoCond{}:
      Unit{}
    case Lp.Until{cmd}:
      {==}
    case Lp.While{cmd}:
      {==}

# a bound never ends the loop satisfied
def lj.halt_unsat(t: Bool, fu: Bool, sp: Bool, la: Bool, -i: Nat, -l: Maybe<&2, Nat>, -d: Maybe<&2, Nat>, -c: Lp.Cond, -b: String, -f: Nat, -x: Lp.Last, -G: Type) -> lj.If(S.is_satisfied(S.phase(S.state(Lp.advance.on(Lp.halt.fails(t, fu, sp, la), i, l, d, c, b, f, x)))), G):
  match t fu sp la:
    case True{} _ _ _:
      Unit{}
    case False{} False{} _ _:
      Unit{}
    case False{} True{} True{} _:
      Unit{}
    case False{} True{} False{} True{}:
      Unit{}
    case False{} True{} False{} False{}:
      Unit{}

# a settled turn never ends the loop satisfied (m: it is the loop's own)
def lj.settled_sat(m: Bool, bl: Bool, o: Lp.Out, c: Lp.Cond, +i: Nat, +l: Maybe<&2, Nat>, +d: Maybe<&2, Nat>, +b: String, +f: Nat, +x: Lp.Last, +now: Nat, +fu: Bool) -> lj.If(S.is_satisfied(S.phase(S.state(Lp.settled(m, Lp.Turn{}, i, l, d, c, b, f, x, o, bl, now, fu)))), {False{} == True{} : Bool}):
  match m bl o c:
    case False{} _ _ _:
      Unit{}
    case True{} True{} _ _:
      Unit{}
    case True{} False{} Lp.Ran{} Lp.NoCond{}:
      lj.halt_unsat(Lp.tired(0n), fu, Lp.spent(l), Lp.late(d, now), i, l, d, Lp.NoCond{}, b, 0n, x, {False{} == True{} : Bool})
    case True{} False{} Lp.Ran{} Lp.Until{cmd}:
      Unit{}
    case True{} False{} Lp.Ran{} Lp.While{cmd}:
      Unit{}
    case True{} False{} Lp.Errored{} Lp.NoCond{}:
      lj.halt_unsat(Lp.tired(1n+f), fu, Lp.spent(l), Lp.late(d, now), i, l, d, Lp.NoCond{}, b, 1n+f, x, {False{} == True{} : Bool})
    case True{} False{} Lp.Errored{} Lp.Until{cmd}:
      Unit{}
    case True{} False{} Lp.Errored{} Lp.While{cmd}:
      Unit{}
    case True{} False{} Lp.Halted{} _:
      Unit{}

# a nonzero exit of an `--until` condition never ends the loop satisfied:
# a broken check (bb: 126 or 127) or "not yet"
def lj.sat_u(bb: Bool, cmd: String, k: Nat, +i: Nat, +l: Maybe<&2, Nat>, +d: Maybe<&2, Nat>, +b: String, +f: Nat, +x: Lp.Last, +now: Nat, +fu: Bool) -> lj.If(S.is_satisfied(S.phase(S.state(Lp.judged.verdict(Lp.judge.nonzero(bb, Lp.Refuted{}), i, l, d, Lp.Until{cmd}, b, f, x, Lp.Exited{1n+k}, now, fu)))), {False{} == True{} : Bool}):
  match bb:
    case True{}:
      Unit{}
    case False{}:
      lj.halt_unsat(Lp.tired(f), fu, Lp.spent(l), Lp.late(d, now), i, l, d, Lp.Until{cmd}, b, f, Lp.Check{i, Lp.Exited{1n+k}}, {False{} == True{} : Bool})

# a nonzero exit of a `--while` condition ends the loop satisfied only
# when it is neither 126 nor 127 (bb False)
def lj.sat_w(bb: Bool, -cmd: String, -k: Nat, -i: Nat, -l: Maybe<&2, Nat>, -d: Maybe<&2, Nat>, -b: String, -f: Nat, -x: Lp.Last, -now: Nat, -fu: Bool) -> lj.If(S.is_satisfied(S.phase(S.state(Lp.judged.verdict(Lp.judge.nonzero(bb, Lp.Confirmed{}), i, l, d, Lp.While{cmd}, b, f, x, Lp.Exited{1n+k}, now, fu)))), {Bool.not(bb) == True{} : Bool}):
  match bb:
    case True{}:
      Unit{}
    case False{}:
      {==}

# a judged check ends the loop satisfied only if it is the loop's own (m),
# in an idle session, and shows the stop condition
def lj.judged_sat(m: Bool, bl: Bool, c: Lp.Cond, ev: Lp.Evid, +i: Nat, +l: Maybe<&2, Nat>, +d: Maybe<&2, Nat>, +b: String, +f: Nat, +x: Lp.Last, +now: Nat, +fu: Bool) -> lj.If(S.is_satisfied(S.phase(S.state(Lp.judged(m, Lp.Judging{}, i, l, d, c, b, f, x, ev, bl, now, fu)))), {Bool.and(m, Bool.and(Bool.not(bl), S.shows_stop(c, ev))) == True{} : Bool}):
  match m bl c ev:
    case False{} _ _ _:
      Unit{}
    case True{} True{} _ _:
      Unit{}
    case True{} False{} Lp.NoCond{} _:
      lj.halt_unsat(Lp.tired(f), fu, Lp.spent(l), Lp.late(d, now), i, l, d, Lp.NoCond{}, b, f, x, {False{} == True{} : Bool})
    case True{} False{} Lp.Until{cmd} Lp.Exited{0n}:
      {==}
    case True{} False{} Lp.Until{cmd} Lp.Exited{1n++k}:
      lj.sat_u(Lp.cannot_run(1n+k), cmd, k, i, l, d, b, f, x, now, fu)
    case True{} False{} Lp.Until{cmd} Lp.NoStatus{}:
      Unit{}
    case True{} False{} Lp.Until{cmd} Lp.TimedOut{}:
      Unit{}
    case True{} False{} Lp.Until{cmd} Lp.SpawnFailed{}:
      Unit{}
    case True{} False{} Lp.Until{cmd} Lp.Cancelled{}:
      Unit{}
    case True{} False{} Lp.While{cmd} Lp.Exited{0n}:
      lj.halt_unsat(Lp.tired(f), fu, Lp.spent(l), Lp.late(d, now), i, l, d, Lp.While{cmd}, b, f, Lp.Check{i, Lp.Exited{0n}}, {False{} == True{} : Bool})
    case True{} False{} Lp.While{cmd} Lp.Exited{1n++k}:
      lj.sat_w(Lp.cannot_run(1n+k), cmd, k, i, l, d, b, f, x, now, fu)
    case True{} False{} Lp.While{cmd} Lp.NoStatus{}:
      Unit{}
    case True{} False{} Lp.While{cmd} Lp.TimedOut{}:
      Unit{}
    case True{} False{} Lp.While{cmd} Lp.SpawnFailed{}:
      Unit{}
    case True{} False{} Lp.While{cmd} Lp.Cancelled{}:
      Unit{}

# loop_satisfied_needs_confirmation, by the event and the phase
def lj.sat(+e: Lp.Ev, +s: Lp.St) -> lj.If(S.newly_satisfied(s, e), {S.confirms(s, e) == True{} : Bool}):
  match e s:
    case Lp.Enter{lim, c2, None{}, now} Lp.St{Lp.Off{}, i, l, d, c, b, f, x}:
      Unit{}
    case Lp.Enter{lim, c2, None{}, now} Lp.St{Lp.Armed{}, i, l, d, c, b, f, x}:
      Unit{}
    case Lp.Enter{lim, c2, None{}, now} Lp.St{Lp.Turn{}, i, l, d, c, b, f, x}:
      Unit{}
    case Lp.Enter{lim, c2, None{}, now} Lp.St{Lp.Judging{}, i, l, d, c, b, f, x}:
      Unit{}
    case Lp.Enter{lim, c2, None{}, now} Lp.St{Lp.Paused{}, i, l, d, c, b, f, x}:
      Unit{}
    case Lp.Enter{lim, c2, None{}, now} Lp.St{Lp.Ended{w}, i, l, d, c, b, f, x}:
      lj.if_and_f(Bool.not(S.end_is_satisfied(w)), {False{} == True{} : Bool})
    case Lp.Enter{lim, c2, Some{t}, now} Lp.St{Lp.Off{}, i, l, d, c, b, f, x}:
      Unit{}
    case Lp.Enter{lim, c2, Some{t}, now} Lp.St{Lp.Armed{}, i, l, d, c, b, f, x}:
      Unit{}
    case Lp.Enter{lim, c2, Some{t}, now} Lp.St{Lp.Turn{}, i, l, d, c, b, f, x}:
      Unit{}
    case Lp.Enter{lim, c2, Some{t}, now} Lp.St{Lp.Judging{}, i, l, d, c, b, f, x}:
      Unit{}
    case Lp.Enter{lim, c2, Some{t}, now} Lp.St{Lp.Paused{}, i, l, d, c, b, f, x}:
      Unit{}
    case Lp.Enter{lim, c2, Some{t}, now} Lp.St{Lp.Ended{w}, i, l, d, c, b, f, x}:
      lj.if_and_f(Bool.not(S.end_is_satisfied(w)), {False{} == True{} : Bool})
    case Lp.Stop{} Lp.St{Lp.Off{}, i, l, d, c, b, f, x}:
      Unit{}
    case Lp.Stop{} Lp.St{Lp.Armed{}, i, l, d, c, b, f, x}:
      Unit{}
    case Lp.Stop{} Lp.St{Lp.Turn{}, i, l, d, c, b, f, x}:
      Unit{}
    case Lp.Stop{} Lp.St{Lp.Judging{}, i, l, d, c, b, f, x}:
      Unit{}
    case Lp.Stop{} Lp.St{Lp.Paused{}, i, l, d, c, b, f, x}:
      Unit{}
    case Lp.Stop{} Lp.St{Lp.Ended{w}, i, l, d, c, b, f, x}:
      lj.if_not_self(S.end_is_satisfied(w), {False{} == True{} : Bool})
    case Lp.Abort{} Lp.St{Lp.Off{}, i, l, d, c, b, f, x}:
      Unit{}
    case Lp.Abort{} Lp.St{Lp.Armed{}, i, l, d, c, b, f, x}:
      Unit{}
    case Lp.Abort{} Lp.St{Lp.Turn{}, i, l, d, c, b, f, x}:
      Unit{}
    case Lp.Abort{} Lp.St{Lp.Judging{}, i, l, d, c, b, f, x}:
      Unit{}
    case Lp.Abort{} Lp.St{Lp.Paused{}, i, l, d, c, b, f, x}:
      Unit{}
    case Lp.Abort{} Lp.St{Lp.Ended{w}, i, l, d, c, b, f, x}:
      lj.if_not_self(S.end_is_satisfied(w), {False{} == True{} : Bool})
    case Lp.Prompt{t} Lp.St{Lp.Off{}, i, l, d, c, b, f, x}:
      Unit{}
    case Lp.Prompt{t} Lp.St{Lp.Armed{}, i, l, d, c, b, f, x}:
      Unit{}
    case Lp.Prompt{t} Lp.St{Lp.Turn{}, i, l, d, c, b, f, x}:
      Unit{}
    case Lp.Prompt{t} Lp.St{Lp.Judging{}, i, l, d, c, b, f, x}:
      Unit{}
    case Lp.Prompt{t} Lp.St{Lp.Paused{}, i, l, d, c, b, f, x}:
      Unit{}
    case Lp.Prompt{t} Lp.St{Lp.Ended{w}, i, l, d, c, b, f, x}:
      lj.if_not_self(S.end_is_satisfied(w), {False{} == True{} : Bool})
    case Lp.Settled{k, o, bl, now, fu} Lp.St{Lp.Off{}, i, l, d, c, b, f, x}:
      Unit{}
    case Lp.Settled{k, o, bl, now, fu} Lp.St{Lp.Armed{}, i, l, d, c, b, f, x}:
      Unit{}
    case Lp.Settled{k, o, bl, now, fu} Lp.St{Lp.Turn{}, i, l, d, c, b, f, x}:
      lj.settled_sat(Nat.is_eq(k, i), bl, o, c, i, l, d, b, f, x, now, fu)
    case Lp.Settled{k, o, bl, now, fu} Lp.St{Lp.Judging{}, i, l, d, c, b, f, x}:
      Unit{}
    case Lp.Settled{k, o, bl, now, fu} Lp.St{Lp.Paused{}, i, l, d, c, b, f, x}:
      Unit{}
    case Lp.Settled{k, o, bl, now, fu} Lp.St{Lp.Ended{w}, i, l, d, c, b, f, x}:
      lj.if_not_self(S.end_is_satisfied(w), {False{} == True{} : Bool})
    case Lp.Judged{k, ev, bl, now, fu} Lp.St{Lp.Off{}, i, l, d, c, b, f, x}:
      Unit{}
    case Lp.Judged{k, ev, bl, now, fu} Lp.St{Lp.Armed{}, i, l, d, c, b, f, x}:
      Unit{}
    case Lp.Judged{k, ev, bl, now, fu} Lp.St{Lp.Turn{}, i, l, d, c, b, f, x}:
      Unit{}
    case Lp.Judged{k, ev, bl, now, fu} Lp.St{Lp.Judging{}, i, l, d, c, b, f, x}:
      lj.judged_sat(Nat.is_eq(k, i), bl, c, ev, i, l, d, b, f, x, now, fu)
    case Lp.Judged{k, ev, bl, now, fu} Lp.St{Lp.Paused{}, i, l, d, c, b, f, x}:
      Unit{}
    case Lp.Judged{k, ev, bl, now, fu} Lp.St{Lp.Ended{w}, i, l, d, c, b, f, x}:
      lj.if_not_self(S.end_is_satisfied(w), {False{} == True{} : Bool})
    case Lp.Restart{} Lp.St{Lp.Off{}, i, l, d, c, b, f, x}:
      Unit{}
    case Lp.Restart{} Lp.St{Lp.Armed{}, i, l, d, c, b, f, x}:
      Unit{}
    case Lp.Restart{} Lp.St{Lp.Turn{}, i, l, d, c, b, f, x}:
      Unit{}
    case Lp.Restart{} Lp.St{Lp.Judging{}, i, l, d, c, b, f, x}:
      Unit{}
    case Lp.Restart{} Lp.St{Lp.Paused{}, i, l, d, c, b, f, x}:
      Unit{}
    case Lp.Restart{} Lp.St{Lp.Ended{w}, i, l, d, c, b, f, x}:
      lj.if_not_self(S.end_is_satisfied(w), {False{} == True{} : Bool})

# a settled turn starts no iteration of a loop with a condition
def lj.settled_auto(m: Bool, bl: Bool, o: Lp.Out, c: Lp.Cond, +i: Nat, +l: Maybe<&2, Nat>, +d: Maybe<&2, Nat>, +b: String, +f: Nat, +x: Lp.Last, +now: Nat, +fu: Bool) -> lj.If(S.is_submit(S.act(Lp.settled(m, Lp.Turn{}, i, l, d, c, b, f, x, o, bl, now, fu))), lj.If(S.has_cond(c), {False{} == True{} : Bool})):
  match m bl o c:
    case False{} _ _ _:
      Unit{}
    case True{} True{} _ _:
      Unit{}
    case True{} False{} Lp.Ran{} Lp.NoCond{}:
      lj.if_any(S.is_submit(S.act(Lp.advance(i, l, d, Lp.NoCond{}, b, 0n, x, now, fu))), Unit, Unit{})
    case True{} False{} Lp.Ran{} Lp.Until{cmd}:
      Unit{}
    case True{} False{} Lp.Ran{} Lp.While{cmd}:
      Unit{}
    case True{} False{} Lp.Errored{} Lp.NoCond{}:
      lj.if_any(S.is_submit(S.act(Lp.advance(i, l, d, Lp.NoCond{}, b, 1n+f, x, now, fu))), Unit, Unit{})
    case True{} False{} Lp.Errored{} Lp.Until{cmd}:
      Unit{}
    case True{} False{} Lp.Errored{} Lp.While{cmd}:
      Unit{}
    case True{} False{} Lp.Halted{} _:
      Unit{}

# a nonzero exit of an `--until` condition starts an iteration only when
# it is neither 126 nor 127 (bb False)
def lj.auto_u(bb: Bool, cmd: String, k: Nat, +i: Nat, +l: Maybe<&2, Nat>, +d: Maybe<&2, Nat>, +b: String, +f: Nat, +x: Lp.Last, +now: Nat, +fu: Bool) -> lj.If(S.is_submit(S.act(Lp.judged.verdict(Lp.judge.nonzero(bb, Lp.Refuted{}), i, l, d, Lp.Until{cmd}, b, f, x, Lp.Exited{1n+k}, now, fu))), {Bool.not(bb) == True{} : Bool}):
  match bb:
    case True{}:
      Unit{}
    case False{}:
      lj.if_any(S.is_submit(S.act(Lp.advance(i, l, d, Lp.Until{cmd}, b, f, Lp.Check{i, Lp.Exited{1n+k}}, now, fu))), {True{} == True{} : Bool}, {==})

# a nonzero exit of a `--while` condition never starts an iteration
def lj.auto_w(bb: Bool, -cmd: String, -k: Nat, -i: Nat, -l: Maybe<&2, Nat>, -d: Maybe<&2, Nat>, -b: String, -f: Nat, -x: Lp.Last, -now: Nat, -fu: Bool) -> lj.If(S.is_submit(S.act(Lp.judged.verdict(Lp.judge.nonzero(bb, Lp.Confirmed{}), i, l, d, Lp.While{cmd}, b, f, x, Lp.Exited{1n+k}, now, fu))), {False{} == True{} : Bool}):
  match bb:
    case True{}:
      Unit{}
    case False{}:
      Unit{}

# a judged check starts an iteration of a loop with a condition only if it
# is the loop's own (m), in an idle session, and shows the stop condition
# does not hold yet
def lj.judged_auto(m: Bool, bl: Bool, c: Lp.Cond, ev: Lp.Evid, +i: Nat, +l: Maybe<&2, Nat>, +d: Maybe<&2, Nat>, +b: String, +f: Nat, +x: Lp.Last, +now: Nat, +fu: Bool) -> lj.If(S.is_submit(S.act(Lp.judged(m, Lp.Judging{}, i, l, d, c, b, f, x, ev, bl, now, fu))), lj.If(S.has_cond(c), {Bool.and(m, Bool.and(Bool.not(bl), S.shows_go(c, ev))) == True{} : Bool})):
  match m bl c ev:
    case False{} _ _ _:
      Unit{}
    case True{} True{} _ _:
      Unit{}
    case True{} False{} Lp.NoCond{} _:
      lj.if_any(S.is_submit(S.act(Lp.advance(i, l, d, Lp.NoCond{}, b, f, x, now, fu))), Unit, Unit{})
    case True{} False{} Lp.Until{cmd} Lp.Exited{0n}:
      Unit{}
    case True{} False{} Lp.Until{cmd} Lp.Exited{1n++k}:
      lj.auto_u(Lp.cannot_run(1n+k), cmd, k, i, l, d, b, f, x, now, fu)
    case True{} False{} Lp.Until{cmd} Lp.NoStatus{}:
      Unit{}
    case True{} False{} Lp.Until{cmd} Lp.TimedOut{}:
      Unit{}
    case True{} False{} Lp.Until{cmd} Lp.SpawnFailed{}:
      Unit{}
    case True{} False{} Lp.Until{cmd} Lp.Cancelled{}:
      Unit{}
    case True{} False{} Lp.While{cmd} Lp.Exited{0n}:
      lj.if_any(S.is_submit(S.act(Lp.advance(i, l, d, Lp.While{cmd}, b, f, Lp.Check{i, Lp.Exited{0n}}, now, fu))), {True{} == True{} : Bool}, {==})
    case True{} False{} Lp.While{cmd} Lp.Exited{1n++k}:
      lj.auto_w(Lp.cannot_run(1n+k), cmd, k, i, l, d, b, f, x, now, fu)
    case True{} False{} Lp.While{cmd} Lp.NoStatus{}:
      Unit{}
    case True{} False{} Lp.While{cmd} Lp.TimedOut{}:
      Unit{}
    case True{} False{} Lp.While{cmd} Lp.SpawnFailed{}:
      Unit{}
    case True{} False{} Lp.While{cmd} Lp.Cancelled{}:
      Unit{}

def lj.auto_tbl(+e: Lp.Ev, +s: Lp.St) -> lj.If(Bool.and(Bool.not(S.is_enter(e)), S.is_submit(S.does(s, e))), lj.If(S.has_cond(S.cond(s)), {S.refutes(s, e) == True{} : Bool})):
  match e s:
    case Lp.Enter{lim, c2, pr, now} _:
      Unit{}
    case Lp.Stop{} Lp.St{Lp.Off{}, i, l, d, c, b, f, x}:
      Unit{}
    case Lp.Stop{} Lp.St{Lp.Armed{}, i, l, d, c, b, f, x}:
      Unit{}
    case Lp.Stop{} Lp.St{Lp.Turn{}, i, l, d, c, b, f, x}:
      Unit{}
    case Lp.Stop{} Lp.St{Lp.Judging{}, i, l, d, c, b, f, x}:
      Unit{}
    case Lp.Stop{} Lp.St{Lp.Paused{}, i, l, d, c, b, f, x}:
      Unit{}
    case Lp.Stop{} Lp.St{Lp.Ended{w}, i, l, d, c, b, f, x}:
      Unit{}
    case Lp.Abort{} Lp.St{Lp.Off{}, i, l, d, c, b, f, x}:
      Unit{}
    case Lp.Abort{} Lp.St{Lp.Armed{}, i, l, d, c, b, f, x}:
      Unit{}
    case Lp.Abort{} Lp.St{Lp.Turn{}, i, l, d, c, b, f, x}:
      Unit{}
    case Lp.Abort{} Lp.St{Lp.Judging{}, i, l, d, c, b, f, x}:
      Unit{}
    case Lp.Abort{} Lp.St{Lp.Paused{}, i, l, d, c, b, f, x}:
      Unit{}
    case Lp.Abort{} Lp.St{Lp.Ended{w}, i, l, d, c, b, f, x}:
      Unit{}
    case Lp.Prompt{t} Lp.St{Lp.Off{}, i, l, d, c, b, f, x}:
      Unit{}
    case Lp.Prompt{t} Lp.St{Lp.Armed{}, i, l, d, c, b, f, x}:
      Unit{}
    case Lp.Prompt{t} Lp.St{Lp.Turn{}, i, l, d, c, b, f, x}:
      Unit{}
    case Lp.Prompt{t} Lp.St{Lp.Judging{}, i, l, d, c, b, f, x}:
      Unit{}
    case Lp.Prompt{t} Lp.St{Lp.Paused{}, i, l, d, c, b, f, x}:
      Unit{}
    case Lp.Prompt{t} Lp.St{Lp.Ended{w}, i, l, d, c, b, f, x}:
      Unit{}
    case Lp.Settled{k, o, bl, now, fu} Lp.St{Lp.Off{}, i, l, d, c, b, f, x}:
      Unit{}
    case Lp.Settled{k, o, bl, now, fu} Lp.St{Lp.Armed{}, i, l, d, c, b, f, x}:
      Unit{}
    case Lp.Settled{k, o, bl, now, fu} Lp.St{Lp.Turn{}, i, l, d, c, b, f, x}:
      lj.settled_auto(Nat.is_eq(k, i), bl, o, c, i, l, d, b, f, x, now, fu)
    case Lp.Settled{k, o, bl, now, fu} Lp.St{Lp.Judging{}, i, l, d, c, b, f, x}:
      Unit{}
    case Lp.Settled{k, o, bl, now, fu} Lp.St{Lp.Paused{}, i, l, d, c, b, f, x}:
      Unit{}
    case Lp.Settled{k, o, bl, now, fu} Lp.St{Lp.Ended{w}, i, l, d, c, b, f, x}:
      Unit{}
    case Lp.Judged{k, ev, bl, now, fu} Lp.St{Lp.Off{}, i, l, d, c, b, f, x}:
      Unit{}
    case Lp.Judged{k, ev, bl, now, fu} Lp.St{Lp.Armed{}, i, l, d, c, b, f, x}:
      Unit{}
    case Lp.Judged{k, ev, bl, now, fu} Lp.St{Lp.Turn{}, i, l, d, c, b, f, x}:
      Unit{}
    case Lp.Judged{k, ev, bl, now, fu} Lp.St{Lp.Judging{}, i, l, d, c, b, f, x}:
      lj.judged_auto(Nat.is_eq(k, i), bl, c, ev, i, l, d, b, f, x, now, fu)
    case Lp.Judged{k, ev, bl, now, fu} Lp.St{Lp.Paused{}, i, l, d, c, b, f, x}:
      Unit{}
    case Lp.Judged{k, ev, bl, now, fu} Lp.St{Lp.Ended{w}, i, l, d, c, b, f, x}:
      Unit{}
    case Lp.Restart{} Lp.St{Lp.Off{}, i, l, d, c, b, f, x}:
      Unit{}
    case Lp.Restart{} Lp.St{Lp.Armed{}, i, l, d, c, b, f, x}:
      Unit{}
    case Lp.Restart{} Lp.St{Lp.Turn{}, i, l, d, c, b, f, x}:
      Unit{}
    case Lp.Restart{} Lp.St{Lp.Judging{}, i, l, d, c, b, f, x}:
      Unit{}
    case Lp.Restart{} Lp.St{Lp.Paused{}, i, l, d, c, b, f, x}:
      Unit{}
    case Lp.Restart{} Lp.St{Lp.Ended{w}, i, l, d, c, b, f, x}:
      Unit{}

# loop_auto_needs_refutation, by the event and the phase
def lj.auto(+e: Lp.Ev, +s: Lp.St) -> lj.If(Bool.and(S.has_cond(S.cond(s)), Bool.and(Bool.not(S.is_enter(e)), S.is_submit(S.does(s, e)))), {S.refutes(s, e) == True{} : Bool}):
  lj.if_and(S.has_cond(S.cond(s)), Bool.and(Bool.not(S.is_enter(e)), S.is_submit(S.does(s, e))), {S.refutes(s, e) == True{} : Bool}, lj.auto_tbl(e, s))

# The start and the stop (L1)
# ---------------------------

def lj.enter_first(s: Lp.St, -lim: Lp.Limit, -c: Lp.Cond, -t: String, -now: Nat) -> lj.IfN(S.is_on(S.phase(s)), {(S.does(s, Lp.Enter{lim, c, Some{t}, now}), (S.phase(S.next(s, Lp.Enter{lim, c, Some{t}, now})), (S.body(S.next(s, Lp.Enter{lim, c, Some{t}, now})), S.cond(S.next(s, Lp.Enter{lim, c, Some{t}, now}))))) == (Lp.Submit{1n, t}, (Lp.Turn{}, (t, c))) : Lp.Act & (Lp.Phase & (String & Lp.Cond))}):
  match s:
    case Lp.St{Lp.Off{}, i, l, d, c0, b, f, x}:
      {==}
    case Lp.St{Lp.Armed{}, i, l, d, c0, b, f, x}:
      Unit{}
    case Lp.St{Lp.Turn{}, i, l, d, c0, b, f, x}:
      Unit{}
    case Lp.St{Lp.Judging{}, i, l, d, c0, b, f, x}:
      Unit{}
    case Lp.St{Lp.Paused{}, i, l, d, c0, b, f, x}:
      Unit{}
    case Lp.St{Lp.Ended{w}, i, l, d, c0, b, f, x}:
      {==}

def lj.enter_arms(s: Lp.St, -lim: Lp.Limit, -c: Lp.Cond, -now: Nat) -> lj.IfN(S.is_on(S.phase(s)), {(S.does(s, Lp.Enter{lim, c, None{}, now}), (S.phase(S.next(s, Lp.Enter{lim, c, None{}, now})), S.cond(S.next(s, Lp.Enter{lim, c, None{}, now})))) == (Lp.Rest{}, (Lp.Armed{}, c)) : Lp.Act & (Lp.Phase & Lp.Cond)}):
  match s:
    case Lp.St{Lp.Off{}, i, l, d, c0, b, f, x}:
      {==}
    case Lp.St{Lp.Armed{}, i, l, d, c0, b, f, x}:
      Unit{}
    case Lp.St{Lp.Turn{}, i, l, d, c0, b, f, x}:
      Unit{}
    case Lp.St{Lp.Judging{}, i, l, d, c0, b, f, x}:
      Unit{}
    case Lp.St{Lp.Paused{}, i, l, d, c0, b, f, x}:
      Unit{}
    case Lp.St{Lp.Ended{w}, i, l, d, c0, b, f, x}:
      {==}

def lj.enter_ends(s: Lp.St, -lim: Lp.Limit, -c: Lp.Cond, -pr: Maybe<&2, String>, -now: Nat) -> lj.If(S.is_on(S.phase(s)), {(S.does(s, Lp.Enter{lim, c, pr, now}), S.phase(S.next(s, Lp.Enter{lim, c, pr, now}))) == (Lp.Report{Lp.Stopped{}}, Lp.Ended{Lp.Stopped{}}) : Lp.Act & Lp.Phase}):
  match s:
    case Lp.St{Lp.Off{}, i, l, d, c0, b, f, x}:
      Unit{}
    case Lp.St{Lp.Armed{}, i, l, d, c0, b, f, x}:
      {==}
    case Lp.St{Lp.Turn{}, i, l, d, c0, b, f, x}:
      {==}
    case Lp.St{Lp.Judging{}, i, l, d, c0, b, f, x}:
      {==}
    case Lp.St{Lp.Paused{}, i, l, d, c0, b, f, x}:
      {==}
    case Lp.St{Lp.Ended{w}, i, l, d, c0, b, f, x}:
      Unit{}

def lj.stop_ends(s: Lp.St) -> lj.If(S.is_on(S.phase(s)), {(S.does(s, Lp.Stop{}), S.phase(S.next(s, Lp.Stop{}))) == (Lp.Report{Lp.Stopped{}}, Lp.Ended{Lp.Stopped{}}) : Lp.Act & Lp.Phase}):
  match s:
    case Lp.St{Lp.Off{}, i, l, d, c0, b, f, x}:
      Unit{}
    case Lp.St{Lp.Armed{}, i, l, d, c0, b, f, x}:
      {==}
    case Lp.St{Lp.Turn{}, i, l, d, c0, b, f, x}:
      {==}
    case Lp.St{Lp.Judging{}, i, l, d, c0, b, f, x}:
      {==}
    case Lp.St{Lp.Paused{}, i, l, d, c0, b, f, x}:
      {==}
    case Lp.St{Lp.Ended{w}, i, l, d, c0, b, f, x}:
      Unit{}

def lj.stop_idle(s: Lp.St) -> lj.IfN(S.is_on(S.phase(s)), {Lp.step(s, Lp.Stop{}) == (s, Lp.Rest{}) : Lp.St & Lp.Act}):
  match s:
    case Lp.St{Lp.Off{}, i, l, d, c0, b, f, x}:
      {==}
    case Lp.St{Lp.Armed{}, i, l, d, c0, b, f, x}:
      Unit{}
    case Lp.St{Lp.Turn{}, i, l, d, c0, b, f, x}:
      Unit{}
    case Lp.St{Lp.Judging{}, i, l, d, c0, b, f, x}:
      Unit{}
    case Lp.St{Lp.Paused{}, i, l, d, c0, b, f, x}:
      Unit{}
    case Lp.St{Lp.Ended{w}, i, l, d, c0, b, f, x}:
      {==}

# What is sent again (L2)
# -----------------------

# an iteration the bounds allow sends the prompt, numbered one past
def lj.adv_resends(h: Maybe<&2, Lp.End>, -i: Nat, -l: Maybe<&2, Nat>, -d: Maybe<&2, Nat>, -c: Lp.Cond, -b: String, -f: Nat, -x: Lp.Last) -> lj.If(S.is_submit(S.act(Lp.advance.on(h, i, l, d, c, b, f, x))), {S.act(Lp.advance.on(h, i, l, d, c, b, f, x)) == Lp.Submit{1n+i, b} : Lp.Act}):
  match h:
    case None{}:
      {==}
    case Some{w}:
      Unit{}

def lj.settled_resends(m: Bool, bl: Bool, o: Lp.Out, c: Lp.Cond, +i: Nat, +l: Maybe<&2, Nat>, +d: Maybe<&2, Nat>, +b: String, +f: Nat, +x: Lp.Last, +now: Nat, +fu: Bool) -> lj.If(S.is_submit(S.act(Lp.settled(m, Lp.Turn{}, i, l, d, c, b, f, x, o, bl, now, fu))), {S.act(Lp.settled(m, Lp.Turn{}, i, l, d, c, b, f, x, o, bl, now, fu)) == Lp.Submit{1n+i, b} : Lp.Act}):
  match m bl o c:
    case False{} _ _ _:
      Unit{}
    case True{} True{} _ _:
      Unit{}
    case True{} False{} Lp.Ran{} Lp.NoCond{}:
      lj.adv_resends(Lp.halt(0n, fu, l, d, now), i, l, d, Lp.NoCond{}, b, 0n, x)
    case True{} False{} Lp.Ran{} Lp.Until{cmd}:
      Unit{}
    case True{} False{} Lp.Ran{} Lp.While{cmd}:
      Unit{}
    case True{} False{} Lp.Errored{} Lp.NoCond{}:
      lj.adv_resends(Lp.halt(1n+f, fu, l, d, now), i, l, d, Lp.NoCond{}, b, 1n+f, x)
    case True{} False{} Lp.Errored{} Lp.Until{cmd}:
      Unit{}
    case True{} False{} Lp.Errored{} Lp.While{cmd}:
      Unit{}
    case True{} False{} Lp.Halted{} _:
      Unit{}

def lj.verdict_resends(v: Lp.Verdict, -c: Lp.Cond, -ev: Lp.Evid, +i: Nat, +l: Maybe<&2, Nat>, +d: Maybe<&2, Nat>, +b: String, +f: Nat, +x: Lp.Last, +now: Nat, +fu: Bool) -> lj.If(S.is_submit(S.act(Lp.judged.verdict(v, i, l, d, c, b, f, x, ev, now, fu))), {S.act(Lp.judged.verdict(v, i, l, d, c, b, f, x, ev, now, fu)) == Lp.Submit{1n+i, b} : Lp.Act}):
  match v:
    case Lp.Confirmed{}:
      Unit{}
    case Lp.Refuted{}:
      lj.adv_resends(Lp.halt(f, fu, l, d, now), i, l, d, c, b, f, Lp.Check{i, ev})
    case Lp.Broken{}:
      Unit{}
    case Lp.Unjudged{}:
      Unit{}

def lj.judged_resends(m: Bool, bl: Bool, c: Lp.Cond, +ev: Lp.Evid, +i: Nat, +l: Maybe<&2, Nat>, +d: Maybe<&2, Nat>, +b: String, +f: Nat, +x: Lp.Last, +now: Nat, +fu: Bool) -> lj.If(S.is_submit(S.act(Lp.judged(m, Lp.Judging{}, i, l, d, c, b, f, x, ev, bl, now, fu))), {S.act(Lp.judged(m, Lp.Judging{}, i, l, d, c, b, f, x, ev, bl, now, fu)) == Lp.Submit{1n+i, b} : Lp.Act}):
  match m bl c:
    case False{} _ _:
      Unit{}
    case True{} True{} _:
      Unit{}
    case True{} False{} Lp.NoCond{}:
      lj.adv_resends(Lp.halt(f, fu, l, d, now), i, l, d, Lp.NoCond{}, b, f, x)
    case True{} False{} Lp.Until{cmd}:
      lj.verdict_resends(Lp.judge(True{}, ev), Lp.Until{cmd}, ev, i, l, d, b, f, x, now, fu)
    case True{} False{} Lp.While{cmd}:
      lj.verdict_resends(Lp.judge(False{}, ev), Lp.While{cmd}, ev, i, l, d, b, f, x, now, fu)

# loop_resends_body, by the event and the phase
def lj.resends(+e: Lp.Ev, +s: Lp.St) -> lj.If(Bool.and(Bool.not(S.is_enter(e)), S.is_submit(S.does(s, e))), {S.does(s, e) == Lp.Submit{1n+S.iter(s), S.body(s)} : Lp.Act}):
  match e s:
    case Lp.Enter{lim, c2, pr, now} _:
      Unit{}
    case Lp.Stop{} Lp.St{Lp.Off{}, i, l, d, c, b, f, x}:
      Unit{}
    case Lp.Stop{} Lp.St{Lp.Armed{}, i, l, d, c, b, f, x}:
      Unit{}
    case Lp.Stop{} Lp.St{Lp.Turn{}, i, l, d, c, b, f, x}:
      Unit{}
    case Lp.Stop{} Lp.St{Lp.Judging{}, i, l, d, c, b, f, x}:
      Unit{}
    case Lp.Stop{} Lp.St{Lp.Paused{}, i, l, d, c, b, f, x}:
      Unit{}
    case Lp.Stop{} Lp.St{Lp.Ended{w}, i, l, d, c, b, f, x}:
      Unit{}
    case Lp.Abort{} Lp.St{Lp.Off{}, i, l, d, c, b, f, x}:
      Unit{}
    case Lp.Abort{} Lp.St{Lp.Armed{}, i, l, d, c, b, f, x}:
      Unit{}
    case Lp.Abort{} Lp.St{Lp.Turn{}, i, l, d, c, b, f, x}:
      Unit{}
    case Lp.Abort{} Lp.St{Lp.Judging{}, i, l, d, c, b, f, x}:
      Unit{}
    case Lp.Abort{} Lp.St{Lp.Paused{}, i, l, d, c, b, f, x}:
      Unit{}
    case Lp.Abort{} Lp.St{Lp.Ended{w}, i, l, d, c, b, f, x}:
      Unit{}
    case Lp.Prompt{t} Lp.St{Lp.Off{}, i, l, d, c, b, f, x}:
      Unit{}
    case Lp.Prompt{t} Lp.St{Lp.Armed{}, i, l, d, c, b, f, x}:
      Unit{}
    case Lp.Prompt{t} Lp.St{Lp.Turn{}, i, l, d, c, b, f, x}:
      Unit{}
    case Lp.Prompt{t} Lp.St{Lp.Judging{}, i, l, d, c, b, f, x}:
      Unit{}
    case Lp.Prompt{t} Lp.St{Lp.Paused{}, i, l, d, c, b, f, x}:
      Unit{}
    case Lp.Prompt{t} Lp.St{Lp.Ended{w}, i, l, d, c, b, f, x}:
      Unit{}
    case Lp.Settled{k, o, bl, now, fu} Lp.St{Lp.Off{}, i, l, d, c, b, f, x}:
      Unit{}
    case Lp.Settled{k, o, bl, now, fu} Lp.St{Lp.Armed{}, i, l, d, c, b, f, x}:
      Unit{}
    case Lp.Settled{k, o, bl, now, fu} Lp.St{Lp.Turn{}, i, l, d, c, b, f, x}:
      lj.settled_resends(Nat.is_eq(k, i), bl, o, c, i, l, d, b, f, x, now, fu)
    case Lp.Settled{k, o, bl, now, fu} Lp.St{Lp.Judging{}, i, l, d, c, b, f, x}:
      Unit{}
    case Lp.Settled{k, o, bl, now, fu} Lp.St{Lp.Paused{}, i, l, d, c, b, f, x}:
      Unit{}
    case Lp.Settled{k, o, bl, now, fu} Lp.St{Lp.Ended{w}, i, l, d, c, b, f, x}:
      Unit{}
    case Lp.Judged{k, ev, bl, now, fu} Lp.St{Lp.Off{}, i, l, d, c, b, f, x}:
      Unit{}
    case Lp.Judged{k, ev, bl, now, fu} Lp.St{Lp.Armed{}, i, l, d, c, b, f, x}:
      Unit{}
    case Lp.Judged{k, ev, bl, now, fu} Lp.St{Lp.Turn{}, i, l, d, c, b, f, x}:
      Unit{}
    case Lp.Judged{k, ev, bl, now, fu} Lp.St{Lp.Judging{}, i, l, d, c, b, f, x}:
      lj.judged_resends(Nat.is_eq(k, i), bl, c, ev, i, l, d, b, f, x, now, fu)
    case Lp.Judged{k, ev, bl, now, fu} Lp.St{Lp.Paused{}, i, l, d, c, b, f, x}:
      Unit{}
    case Lp.Judged{k, ev, bl, now, fu} Lp.St{Lp.Ended{w}, i, l, d, c, b, f, x}:
      Unit{}
    case Lp.Restart{} Lp.St{Lp.Off{}, i, l, d, c, b, f, x}:
      Unit{}
    case Lp.Restart{} Lp.St{Lp.Armed{}, i, l, d, c, b, f, x}:
      Unit{}
    case Lp.Restart{} Lp.St{Lp.Turn{}, i, l, d, c, b, f, x}:
      Unit{}
    case Lp.Restart{} Lp.St{Lp.Judging{}, i, l, d, c, b, f, x}:
      Unit{}
    case Lp.Restart{} Lp.St{Lp.Paused{}, i, l, d, c, b, f, x}:
      Unit{}
    case Lp.Restart{} Lp.St{Lp.Ended{w}, i, l, d, c, b, f, x}:
      Unit{}

def lj.adopted(s: Lp.St, -t: String) -> lj.If(S.is_on(S.phase(s)), {(S.does(s, Lp.Prompt{t}), (S.phase(S.next(s, Lp.Prompt{t})), (S.body(S.next(s, Lp.Prompt{t})), (S.left(S.next(s, Lp.Prompt{t})), S.cond(S.next(s, Lp.Prompt{t})))))) == (Lp.Adopt{1n+S.iter(s)}, (Lp.Turn{}, (t, (S.left(s), S.cond(s))))) : Lp.Act & (Lp.Phase & (String & (Maybe<&2, Nat> & Lp.Cond)))}):
  match s:
    case Lp.St{Lp.Off{}, i, l, d, c0, b, f, x}:
      Unit{}
    case Lp.St{Lp.Armed{}, i, l, d, c0, b, f, x}:
      {==}
    case Lp.St{Lp.Turn{}, i, l, d, c0, b, f, x}:
      {==}
    case Lp.St{Lp.Judging{}, i, l, d, c0, b, f, x}:
      {==}
    case Lp.St{Lp.Paused{}, i, l, d, c0, b, f, x}:
      {==}
    case Lp.St{Lp.Ended{w}, i, l, d, c0, b, f, x}:
      Unit{}
