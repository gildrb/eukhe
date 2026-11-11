# eukhe: lemmas of area loop, topic bounds: the lemmas of the laws of
# laws/loop/model.bend about the bounds (L1, L4), the interrupt (L5), the
# end (L6), the restart (L7), queued input (L8) and the evidence kept (L9).
#
# Lp.step matches the state, then the event; a settled turn and a judged
# check then test `Nat.is_eq(k, i)` and their flags. Each lemma below
# follows one of these defs with the tested Bool as a parameter (m, live,
# bl) and matches on it, so a fill gives the Bool the code computes.
# A premise `b == True` of a law is carried as lb.When(b, G): the case
# analysis answers Unit{} where the premise computes to False.

import Base
import ../../../bend/loop.bend as Lp
import ../../../spec/loop/loop.bend as S

# Logic
# -----

# G under the premise b
def lb.When(b: Bool, G: Type) -> Type:
  match b:
    case True{}:
      G
    case False{}:
      Unit

# G under the premise not b
def lb.Unless(b: Bool, G: Type) -> Type:
  match b:
    case True{}:
      Unit
    case False{}:
      G

def lb.when(-b: Bool, -G: Type, h: {b == True{} : Bool}, x: lb.When(b, G)) -> G:
  %h : lb.When(_, G)
  x

def lb.when2(-a: Bool, -b: Bool, -G: Type, ha: {a == True{} : Bool}, hb: {b == True{} : Bool}, x: lb.When(a, lb.When(b, G))) -> G:
  lb.when(b, G, hb, lb.when(a, lb.When(b, G), ha, x))

def lb.unless(-b: Bool, -G: Type, h: {b == False{} : Bool}, x: lb.Unless(b, G)) -> G:
  %h : lb.Unless(_, G)
  x

# a premise False == True proves anything
def lb.absurd_ft(-G: Type, e: {False{} == True{} : Bool}) -> G:
  %e : lb.When(_, G)
  Unit{}

# a premise True == False proves anything
def lb.absurd_tf(-G: Type, e: {True{} == False{} : Bool}) -> G:
  %e : lb.Unless(_, G)
  Unit{}

# Order
# -----

def lb.refl(i: Nat) -> {True{} == Nat.is_eq(i, i) : Bool}:
  match i:
    case 0n:
      {==}
    case 1n+p:
      lb.refl(p)

# k is i: k is not 1 + i
def lb.eq_not_succ(k: Nat, i: Nat, h: {True{} == Nat.is_eq(k, i) : Bool}) -> {False{} == Nat.is_eq(k, 1n+i) : Bool}:
  match k i:
    case 0n 0n:
      {==}
    case 0n 1n+ip:
      {==}
    case 1n+kp 0n:
      lb.absurd_tf({False{} == Nat.is_eq(1n+kp, 1n) : Bool}, h)
    case 1n+kp 1n+ip:
      lb.eq_not_succ(kp, ip, h)

# a < b: b is not at or before a
def lb.lt_not_le(a: Nat, b: Nat, h: {Nat.is_lt(a, b) == True{} : Bool}) -> {Nat.is_le(b, a) == False{} : Bool}:
  match a b:
    case 0n 0n:
      lb.absurd_ft({Nat.is_le(0n, 0n) == False{} : Bool}, h)
    case 0n 1n+bp:
      {==}
    case 1n+ap 0n:
      lb.absurd_ft({Nat.is_le(0n, 1n+ap) == False{} : Bool}, h)
    case 1n+ap 1n+bp:
      lb.lt_not_le(ap, bp, h)

def lb.fresh.no(k: Nat, hf: {Nat.is_lt(3n+k, 3n) == True{} : Bool}) -> {True{} == False{} : Bool}:
  match k:
    case 0n:
      lb.absurd_ft({True{} == False{} : Bool}, hf)
    case 1n+q:
      lb.absurd_ft({True{} == False{} : Bool}, hf)

# fewer than three failed turns in a row: the loop is not tired
def lb.fresh(f: Nat, hf: {Nat.is_lt(f, 3n) == True{} : Bool}) -> {Lp.tired(f) == False{} : Bool}:
  match f:
    case 0n:
      {==}
    case 1n:
      {==}
    case 2n:
      {==}
    case 3n+k:
      lb.fresh.no(k, hf)

# fewer than two failed turns in a row: one more does not tire the loop
def lb.fresh_next(f: Nat, hf: {Nat.is_lt(f, 2n) == True{} : Bool}) -> {False{} == Lp.tired(1n+f) : Bool}:
  match f:
    case 0n:
      {==}
    case 1n:
      {==}
    case 2n+k:
      match k:
        case 0n:
          hf
        case 1n+q:
          hf

# The loop's own events
# ---------------------

# the turn of iteration i settles in a loop in its turn i: the event is its own
def lb.turn_mine(i: Nat, -l: Maybe<&2, Nat>, -d: Maybe<&2, Nat>, -c: Lp.Cond, -b: String, -f: Nat, -x: Lp.Last, -o: Lp.Out, -bl: Bool, -now: Nat, -fu: Bool) -> {Lp.settled.mine(bl, o, i, l, d, c, b, f, x, now, fu) == Lp.step(Lp.St{Lp.Turn{}, i, l, d, c, b, f, x}, Lp.Settled{i, o, bl, now, fu}) : Lp.St & Lp.Act}:
  %lb.refl(i) : {Lp.settled.mine(bl, o, i, l, d, c, b, f, x, now, fu) == Lp.settled(_, Lp.Turn{}, i, l, d, c, b, f, x, o, bl, now, fu) : Lp.St & Lp.Act}
  {==}

# the check of iteration i is judged in a loop judging i: the event is its own
def lb.judging_mine(i: Nat, -l: Maybe<&2, Nat>, -d: Maybe<&2, Nat>, -c: Lp.Cond, -b: String, -f: Nat, -x: Lp.Last, -ev: Lp.Evid, -bl: Bool, -now: Nat, -fu: Bool) -> {Lp.judged.mine(bl, i, l, d, c, b, f, x, ev, now, fu) == Lp.step(Lp.St{Lp.Judging{}, i, l, d, c, b, f, x}, Lp.Judged{i, ev, bl, now, fu}) : Lp.St & Lp.Act}:
  %lb.refl(i) : {Lp.judged.mine(bl, i, l, d, c, b, f, x, ev, now, fu) == Lp.judged(_, Lp.Judging{}, i, l, d, c, b, f, x, ev, bl, now, fu) : Lp.St & Lp.Act}
  {==}

# The decision point
# ------------------

def lb.exit0(ev: Lp.Evid, h: {S.exited_with(ev, 0n) == True{} : Bool}) -> {Lp.Exited{0n} == ev : Lp.Evid}:
  match ev:
    case Lp.Exited{code}:
      match code:
        case 0n:
          {==}
        case 1n+p:
          lb.absurd_ft({Lp.Exited{0n} == Lp.Exited{1n+p} : Lp.Evid}, h)
    case Lp.NoStatus{}:
      lb.absurd_ft({Lp.Exited{0n} == Lp.NoStatus{} : Lp.Evid}, h)
    case Lp.TimedOut{}:
      lb.absurd_ft({Lp.Exited{0n} == Lp.TimedOut{} : Lp.Evid}, h)
    case Lp.SpawnFailed{}:
      lb.absurd_ft({Lp.Exited{0n} == Lp.SpawnFailed{} : Lp.Evid}, h)
    case Lp.Cancelled{}:
      lb.absurd_ft({Lp.Exited{0n} == Lp.Cancelled{} : Lp.Evid}, h)

def lb.exit1(ev: Lp.Evid, h: {S.exited_with(ev, 1n) == True{} : Bool}) -> {Lp.Exited{1n} == ev : Lp.Evid}:
  match ev:
    case Lp.Exited{code}:
      match code:
        case 0n:
          lb.absurd_ft({Lp.Exited{1n} == Lp.Exited{0n} : Lp.Evid}, h)
        case 1n:
          {==}
        case 2n+q:
          lb.absurd_ft({Lp.Exited{1n} == Lp.Exited{2n+q} : Lp.Evid}, h)
    case Lp.NoStatus{}:
      lb.absurd_ft({Lp.Exited{1n} == Lp.NoStatus{} : Lp.Evid}, h)
    case Lp.TimedOut{}:
      lb.absurd_ft({Lp.Exited{1n} == Lp.TimedOut{} : Lp.Evid}, h)
    case Lp.SpawnFailed{}:
      lb.absurd_ft({Lp.Exited{1n} == Lp.SpawnFailed{} : Lp.Evid}, h)
    case Lp.Cancelled{}:
      lb.absurd_ft({Lp.Exited{1n} == Lp.Cancelled{} : Lp.Evid}, h)

# evidence that shows the stop condition does not hold yet is refuted: the
# check advances the loop and keeps the evidence
def lb.go_cond(c: Lp.Cond, ev: Lp.Evid, -i: Nat, -l: Maybe<&2, Nat>, -d: Maybe<&2, Nat>, -b: String, -f: Nat, -x: Lp.Last, -now: Nat, -fu: Bool, hg: {S.shows_go(c, ev) == True{} : Bool}) -> {Lp.advance(i, l, d, c, b, f, Lp.Check{i, ev}, now, fu) == Lp.judged.cond(c, i, l, d, b, f, x, ev, now, fu) : Lp.St & Lp.Act}:
  match c:
    case Lp.NoCond{}:
      lb.absurd_ft({Lp.advance(i, l, d, Lp.NoCond{}, b, f, Lp.Check{i, ev}, now, fu) == Lp.judged.cond(Lp.NoCond{}, i, l, d, b, f, x, ev, now, fu) : Lp.St & Lp.Act}, hg)
    case Lp.Until{cmd}:
      %lb.exit1(ev, hg) : {Lp.advance(i, l, d, Lp.Until{cmd}, b, f, Lp.Check{i, _}, now, fu) == Lp.judged.cond(Lp.Until{cmd}, i, l, d, b, f, x, _, now, fu) : Lp.St & Lp.Act}
      {==}
    case Lp.While{cmd}:
      %lb.exit0(ev, hg) : {Lp.advance(i, l, d, Lp.While{cmd}, b, f, Lp.Check{i, _}, now, fu) == Lp.judged.cond(Lp.While{cmd}, i, l, d, b, f, x, _, now, fu) : Lp.St & Lp.Act}
      {==}

# the decision point of a loop with a condition: judging iteration i, it
# reads fresh evidence that shows "not yet"
def lb.go(c: Lp.Cond, ev: Lp.Evid, i: Nat, -l: Maybe<&2, Nat>, -d: Maybe<&2, Nat>, -b: String, -f: Nat, -x: Lp.Last, -now: Nat, -fu: Bool, hg: {S.shows_go(c, ev) == True{} : Bool}) -> {Lp.advance(i, l, d, c, b, f, Lp.Check{i, ev}, now, fu) == Lp.step(Lp.St{Lp.Judging{}, i, l, d, c, b, f, x}, Lp.Judged{i, ev, False{}, now, fu}) : Lp.St & Lp.Act}:
  %lb.judging_mine(i, l, d, c, b, f, x, ev, False{}, now, fu) : {Lp.advance(i, l, d, c, b, f, Lp.Check{i, ev}, now, fu) == _ : Lp.St & Lp.Act}
  lb.go_cond(c, ev, i, l, d, b, f, x, now, fu, hg)

# ... with fewer than three failed turns in a row: the budget, the count
# and the time decide
def lb.go_fresh(c: Lp.Cond, ev: Lp.Evid, i: Nat, f: Nat, -l: Maybe<&2, Nat>, -d: Maybe<&2, Nat>, -b: String, -x: Lp.Last, -now: Nat, -fu: Bool, hg: {S.shows_go(c, ev) == True{} : Bool}, hf: {Nat.is_lt(f, 3n) == True{} : Bool}) -> {Lp.advance.on(Lp.halt.budget(fu, Lp.spent(l), Lp.late(d, now)), i, l, d, c, b, f, Lp.Check{i, ev}) == Lp.step(Lp.St{Lp.Judging{}, i, l, d, c, b, f, x}, Lp.Judged{i, ev, False{}, now, fu}) : Lp.St & Lp.Act}:
  %lb.fresh(f, hf) : {Lp.advance.on(Lp.halt.fails(_, fu, Lp.spent(l), Lp.late(d, now)), i, l, d, c, b, f, Lp.Check{i, ev}) == Lp.step(Lp.St{Lp.Judging{}, i, l, d, c, b, f, x}, Lp.Judged{i, ev, False{}, now, fu}) : Lp.St & Lp.Act}
  lb.go(c, ev, i, l, d, b, f, x, now, fu, hg)

# ... with a deadline dl that the clock has reached or not (late)
def lb.go_time(-late: Bool, c: Lp.Cond, ev: Lp.Evid, i: Nat, f: Nat, -l: Maybe<&2, Nat>, -dl: Nat, -b: String, -x: Lp.Last, -now: Nat, -fu: Bool, hg: {S.shows_go(c, ev) == True{} : Bool}, hf: {Nat.is_lt(f, 3n) == True{} : Bool}, hl: {Nat.is_le(dl, now) == late : Bool}) -> {Lp.advance.on(Lp.halt.budget(fu, Lp.spent(l), late), i, l, Some{dl}, c, b, f, Lp.Check{i, ev}) == Lp.step(Lp.St{Lp.Judging{}, i, l, Some{dl}, c, b, f, x}, Lp.Judged{i, ev, False{}, now, fu}) : Lp.St & Lp.Act}:
  %hl : {Lp.advance.on(Lp.halt.budget(fu, Lp.spent(l), _), i, l, Some{dl}, c, b, f, Lp.Check{i, ev}) == Lp.step(Lp.St{Lp.Judging{}, i, l, Some{dl}, c, b, f, x}, Lp.Judged{i, ev, False{}, now, fu}) : Lp.St & Lp.Act}
  lb.go_fresh(c, ev, i, f, l, Some{dl}, b, x, now, fu, hg, hf)

# the decision point of a loop with no condition: its turn i ran to its end
def lb.ran(i: Nat, -l: Maybe<&2, Nat>, -d: Maybe<&2, Nat>, -b: String, -f: Nat, -x: Lp.Last, -now: Nat, -fu: Bool) -> {Lp.advance(i, l, d, Lp.NoCond{}, b, 0n, x, now, fu) == Lp.step(Lp.St{Lp.Turn{}, i, l, d, Lp.NoCond{}, b, f, x}, Lp.Settled{i, Lp.Ran{}, False{}, now, fu}) : Lp.St & Lp.Act}:
  lb.turn_mine(i, l, d, Lp.NoCond{}, b, f, x, Lp.Ran{}, False{}, now, fu)

# ... with a deadline dl that the clock has reached or not (late)
def lb.ran_time(-late: Bool, i: Nat, -l: Maybe<&2, Nat>, -dl: Nat, -b: String, -f: Nat, -x: Lp.Last, -now: Nat, -fu: Bool, hl: {Nat.is_le(dl, now) == late : Bool}) -> {Lp.advance.on(Lp.halt.budget(fu, Lp.spent(l), late), i, l, Some{dl}, Lp.NoCond{}, b, 0n, x) == Lp.step(Lp.St{Lp.Turn{}, i, l, Some{dl}, Lp.NoCond{}, b, f, x}, Lp.Settled{i, Lp.Ran{}, False{}, now, fu}) : Lp.St & Lp.Act}:
  %hl : {Lp.advance.on(Lp.halt.budget(fu, Lp.spent(l), _), i, l, Some{dl}, Lp.NoCond{}, b, 0n, x) == Lp.step(Lp.St{Lp.Turn{}, i, l, Some{dl}, Lp.NoCond{}, b, f, x}, Lp.Settled{i, Lp.Ran{}, False{}, now, fu}) : Lp.St & Lp.Act}
  lb.ran(i, l, Some{dl}, b, f, x, now, fu)

# ... or its turn i failed: one more failed turn in a row
def lb.errored(i: Nat, -l: Maybe<&2, Nat>, -d: Maybe<&2, Nat>, -b: String, -f: Nat, -x: Lp.Last, -now: Nat, -fu: Bool) -> {Lp.advance(i, l, d, Lp.NoCond{}, b, 1n+f, x, now, fu) == Lp.step(Lp.St{Lp.Turn{}, i, l, d, Lp.NoCond{}, b, f, x}, Lp.Settled{i, Lp.Errored{}, False{}, now, fu}) : Lp.St & Lp.Act}:
  lb.turn_mine(i, l, d, Lp.NoCond{}, b, f, x, Lp.Errored{}, False{}, now, fu)

# ... the first or the second in a row: the budget, the count and the time
# decide
def lb.errored_fresh(i: Nat, f: Nat, -l: Maybe<&2, Nat>, -d: Maybe<&2, Nat>, -b: String, -x: Lp.Last, -now: Nat, -fu: Bool, hf: {Nat.is_lt(f, 2n) == True{} : Bool}) -> {Lp.advance.on(Lp.halt.budget(fu, Lp.spent(l), Lp.late(d, now)), i, l, d, Lp.NoCond{}, b, 1n+f, x) == Lp.step(Lp.St{Lp.Turn{}, i, l, d, Lp.NoCond{}, b, f, x}, Lp.Settled{i, Lp.Errored{}, False{}, now, fu}) : Lp.St & Lp.Act}:
  %Equal.sym(Bool, False{}, Lp.tired(1n+f), lb.fresh_next(f, hf)) : {Lp.advance.on(Lp.halt.fails(_, fu, Lp.spent(l), Lp.late(d, now)), i, l, d, Lp.NoCond{}, b, 1n+f, x) == Lp.step(Lp.St{Lp.Turn{}, i, l, d, Lp.NoCond{}, b, f, x}, Lp.Settled{i, Lp.Errored{}, False{}, now, fu}) : Lp.St & Lp.Act}
  lb.errored(i, l, d, b, f, x, now, fu)

# ... with a deadline dl that the clock has reached or not (late)
def lb.errored_time(-late: Bool, i: Nat, f: Nat, -l: Maybe<&2, Nat>, -dl: Nat, -b: String, -x: Lp.Last, -now: Nat, -fu: Bool, hf: {Nat.is_lt(f, 2n) == True{} : Bool}, hl: {Nat.is_le(dl, now) == late : Bool}) -> {Lp.advance.on(Lp.halt.budget(fu, Lp.spent(l), late), i, l, Some{dl}, Lp.NoCond{}, b, 1n+f, x) == Lp.step(Lp.St{Lp.Turn{}, i, l, Some{dl}, Lp.NoCond{}, b, f, x}, Lp.Settled{i, Lp.Errored{}, False{}, now, fu}) : Lp.St & Lp.Act}:
  %hl : {Lp.advance.on(Lp.halt.budget(fu, Lp.spent(l), _), i, l, Some{dl}, Lp.NoCond{}, b, 1n+f, x) == Lp.step(Lp.St{Lp.Turn{}, i, l, Some{dl}, Lp.NoCond{}, b, f, x}, Lp.Settled{i, Lp.Errored{}, False{}, now, fu}) : Lp.St & Lp.Act}
  lb.errored_fresh(i, f, l, Some{dl}, b, x, now, fu, hf)

# What an advance keeps
# ---------------------

def lb.adv_fails(h: Maybe<&2, Lp.End>, -i: Nat, -l: Maybe<&2, Nat>, -d: Maybe<&2, Nat>, -c: Lp.Cond, -b: String, -f: Nat, -x: Lp.Last) -> {S.fails(S.state(Lp.advance.on(h, i, l, d, c, b, f, x))) == f : Nat}:
  match h:
    case Some{w}:
      {==}
    case None{}:
      {==}

# the gate after a settled turn keeps the failed turns it was given
def lb.gate_fails(c: Lp.Cond, -i: Nat, l: Maybe<&2, Nat>, d: Maybe<&2, Nat>, -b: String, f: Nat, -x: Lp.Last, now: Nat, fu: Bool) -> {S.fails(S.state(Lp.gate(c, i, l, d, b, f, x, now, fu))) == f : Nat}:
  match c:
    case Lp.NoCond{}:
      lb.adv_fails(Lp.halt(f, fu, l, d, now), i, l, d, Lp.NoCond{}, b, f, x)
    case Lp.Until{cmd}:
      {==}
    case Lp.While{cmd}:
      {==}

def lb.adv_last(h: Maybe<&2, Lp.End>, -i: Nat, -l: Maybe<&2, Nat>, -d: Maybe<&2, Nat>, -c: Lp.Cond, -b: String, -f: Nat, -x: Lp.Last) -> {S.last(S.state(Lp.advance.on(h, i, l, d, c, b, f, x))) == x : Lp.Last}:
  match h:
    case Some{w}:
      {==}
    case None{}:
      {==}

# No automatic iteration
# ----------------------

# the result starts no automatic iteration
def lb.NoSub(r: Lp.St & Lp.Act) -> Type:
  {S.is_submit(S.act(r)) == False{} : Bool}

# a bound forbids one more automatic iteration
def lb.halts(h: Maybe<&2, Lp.End>) -> Bool:
  match h:
    case Some{w}:
      True{}
    case None{}:
      False{}

def lb.ns_adv(h: Maybe<&2, Lp.End>, -i: Nat, -l: Maybe<&2, Nat>, -d: Maybe<&2, Nat>, -c: Lp.Cond, -b: String, -f: Nat, -x: Lp.Last, hs: {lb.halts(h) == True{} : Bool}) -> lb.NoSub(Lp.advance.on(h, i, l, d, c, b, f, x)):
  match h:
    case Some{w}:
      {==}
    case None{}:
      lb.absurd_ft(lb.NoSub(Lp.advance.on(None{}, i, l, d, c, b, f, x)), hs)

def lb.ns_gate(c: Lp.Cond, -i: Nat, l: Maybe<&2, Nat>, d: Maybe<&2, Nat>, -b: String, f: Nat, -x: Lp.Last, now: Nat, fu: Bool, hs: {lb.halts(Lp.halt(f, fu, l, d, now)) == True{} : Bool}) -> lb.NoSub(Lp.gate(c, i, l, d, b, f, x, now, fu)):
  match c:
    case Lp.NoCond{}:
      lb.ns_adv(Lp.halt(f, fu, l, d, now), i, l, d, Lp.NoCond{}, b, f, x, hs)
    case Lp.Until{cmd}:
      {==}
    case Lp.While{cmd}:
      {==}

# a settled turn starts no automatic iteration when a bound halts the
# loop after a turn that ran (h0) and after one that failed (h1)
def lb.ns_settled(m: Bool, bl: Bool, o: Lp.Out, c: Lp.Cond, -p: Lp.Phase, -i: Nat, l: Maybe<&2, Nat>, d: Maybe<&2, Nat>, -b: String, f: Nat, -x: Lp.Last, now: Nat, fu: Bool, h0: {lb.halts(Lp.halt(0n, fu, l, d, now)) == True{} : Bool}, h1: {lb.halts(Lp.halt(1n+f, fu, l, d, now)) == True{} : Bool}) -> lb.NoSub(Lp.settled(m, p, i, l, d, c, b, f, x, o, bl, now, fu)):
  match m:
    case True{}:
      match bl:
        case True{}:
          {==}
        case False{}:
          match o:
            case Lp.Ran{}:
              lb.ns_gate(c, i, l, d, b, 0n, x, now, fu, h0)
            case Lp.Errored{}:
              lb.ns_gate(c, i, l, d, b, 1n+f, x, now, fu, h1)
            case Lp.Halted{}:
              {==}
    case False{}:
      {==}

def lb.ns_verdict(v: Lp.Verdict, -i: Nat, l: Maybe<&2, Nat>, d: Maybe<&2, Nat>, -c: Lp.Cond, -b: String, f: Nat, -x: Lp.Last, -ev: Lp.Evid, now: Nat, fu: Bool, hs: {lb.halts(Lp.halt(f, fu, l, d, now)) == True{} : Bool}) -> lb.NoSub(Lp.judged.verdict(v, i, l, d, c, b, f, x, ev, now, fu)):
  match v:
    case Lp.Confirmed{}:
      {==}
    case Lp.Refuted{}:
      lb.ns_adv(Lp.halt(f, fu, l, d, now), i, l, d, c, b, f, Lp.Check{i, ev}, hs)
    case Lp.Broken{}:
      {==}
    case Lp.Unjudged{}:
      {==}

# a judged check starts no automatic iteration when a bound halts the loop
def lb.ns_judged(m: Bool, bl: Bool, c: Lp.Cond, -p: Lp.Phase, -i: Nat, l: Maybe<&2, Nat>, d: Maybe<&2, Nat>, -b: String, f: Nat, -x: Lp.Last, ev: Lp.Evid, now: Nat, fu: Bool, hs: {lb.halts(Lp.halt(f, fu, l, d, now)) == True{} : Bool}) -> lb.NoSub(Lp.judged(m, p, i, l, d, c, b, f, x, ev, bl, now, fu)):
  match m:
    case True{}:
      match bl:
        case True{}:
          {==}
        case False{}:
          match c:
            case Lp.NoCond{}:
              lb.ns_adv(Lp.halt(f, fu, l, d, now), i, l, d, Lp.NoCond{}, b, f, x, hs)
            case Lp.Until{cmd}:
              lb.ns_verdict(Lp.judge(True{}, ev), i, l, d, Lp.Until{cmd}, b, f, x, ev, now, fu, hs)
            case Lp.While{cmd}:
              lb.ns_verdict(Lp.judge(False{}, ev), i, l, d, Lp.While{cmd}, b, f, x, ev, now, fu, hs)
    case False{}:
      {==}

def lb.ns_stop(live: Bool, -p: Lp.Phase, -i: Nat, -l: Maybe<&2, Nat>, -d: Maybe<&2, Nat>, -c: Lp.Cond, -b: String, -f: Nat, -x: Lp.Last) -> lb.NoSub(Lp.stop(live, p, i, l, d, c, b, f, x)):
  match live:
    case True{}:
      {==}
    case False{}:
      {==}

def lb.ns_abort(live: Bool, -p: Lp.Phase, -i: Nat, -l: Maybe<&2, Nat>, -d: Maybe<&2, Nat>, -c: Lp.Cond, -b: String, -f: Nat, -x: Lp.Last) -> lb.NoSub(Lp.abort(live, p, i, l, d, c, b, f, x)):
  match live:
    case True{}:
      {==}
    case False{}:
      {==}

def lb.ns_prompt(live: Bool, -p: Lp.Phase, -i: Nat, -l: Maybe<&2, Nat>, -d: Maybe<&2, Nat>, -c: Lp.Cond, -b: String, -f: Nat, -x: Lp.Last, -t: String) -> lb.NoSub(Lp.prompt(live, p, i, l, d, c, b, f, x, t)):
  match live:
    case True{}:
      {==}
    case False{}:
      {==}

def lb.ns_restart(p: Lp.Phase, -i: Nat, -l: Maybe<&2, Nat>, -d: Maybe<&2, Nat>, -c: Lp.Cond, -b: String, -f: Nat, -x: Lp.Last) -> lb.NoSub(Lp.restart(p, i, l, d, c, b, f, x)):
  match p:
    case Lp.Off{}:
      {==}
    case Lp.Armed{}:
      {==}
    case Lp.Turn{}:
      {==}
    case Lp.Judging{}:
      {==}
    case Lp.Paused{}:
      {==}
    case Lp.Ended{w}:
      {==}

# a clock at or past the deadline halts the loop, whatever the other bounds
def lb.halt_late(t: Bool, fu: Bool, sp: Bool, -late: Bool, hl: {late == True{} : Bool}) -> {lb.halts(Lp.halt.fails(t, fu, sp, late)) == True{} : Bool}:
  match t:
    case True{}:
      {==}
    case False{}:
      match fu:
        case True{}:
          match sp:
            case True{}:
              {==}
            case False{}:
              %Equal.sym(Bool, late, True{}, hl) : {lb.halts(Lp.halt.time(_)) == True{} : Bool}
              {==}
        case False{}:
          {==}

def lb.late_halts(f: Nat, fu: Bool, l: Maybe<&2, Nat>, -dl: Nat, -now: Nat, hp: {Nat.is_le(dl, now) == True{} : Bool}) -> {lb.halts(Lp.halt(f, fu, l, Some{dl}, now)) == True{} : Bool}:
  lb.halt_late(Lp.tired(f), fu, Lp.spent(l), Nat.is_le(dl, now), hp)

# a budget that funds no further turn halts the loop
def lb.halt_unfunded(t: Bool, -sp: Bool, -late: Bool) -> {lb.halts(Lp.halt.fails(t, False{}, sp, late)) == True{} : Bool}:
  match t:
    case True{}:
      {==}
    case False{}:
      {==}

# LAW loop_deadline_bounds, on a state with deadline dl
def lb.deadline(+e: Lp.Ev, p: Lp.Phase, i: Nat, +l: Maybe<&2, Nat>, +dl: Nat, c: Lp.Cond, -b: String, +f: Nat, -x: Lp.Last, +hp: {S.past(e, dl) == True{} : Bool}) -> lb.NoSub(Lp.step(Lp.St{p, i, l, Some{dl}, c, b, f, x}, e)):
  match e:
    case Lp.Enter{lim, c2, pr, now}:
      lb.absurd_ft(lb.NoSub(Lp.step(Lp.St{p, i, l, Some{dl}, c, b, f, x}, Lp.Enter{lim, c2, pr, now})), hp)
    case Lp.Stop{}:
      lb.ns_stop(Lp.on(p), p, i, l, Some{dl}, c, b, f, x)
    case Lp.Abort{}:
      lb.ns_abort(Lp.on(p), p, i, l, Some{dl}, c, b, f, x)
    case Lp.Prompt{t}:
      lb.ns_prompt(Lp.on(p), p, i, l, Some{dl}, c, b, f, x, t)
    case Lp.Settled{k, o, bl, now, fu}:
      lb.ns_settled(Bool.and(Lp.in_turn(p), Nat.is_eq(k, i)), bl, o, c, p, i, l, Some{dl}, b, f, x, now, fu, lb.late_halts(0n, fu, l, dl, now, hp), lb.late_halts(1n+f, fu, l, dl, now, hp))
    case Lp.Judged{k, ev, bl, now, fu}:
      lb.ns_judged(Bool.and(Lp.in_judging(p), Nat.is_eq(k, i)), bl, c, p, i, l, Some{dl}, b, f, x, ev, now, fu, lb.late_halts(f, fu, l, dl, now, hp))
    case Lp.Restart{}:
      lb.ns_restart(p, i, l, Some{dl}, c, b, f, x)

# LAW loop_unfunded_never_starts, on an open state
def lb.unfunded(+e: Lp.Ev, p: Lp.Phase, i: Nat, +l: Maybe<&2, Nat>, +d: Maybe<&2, Nat>, c: Lp.Cond, -b: String, +f: Nat, -x: Lp.Last) -> lb.When(S.unfunded(e), lb.NoSub(Lp.step(Lp.St{p, i, l, d, c, b, f, x}, e))):
  match e:
    case Lp.Enter{lim, c2, pr, now}:
      Unit{}
    case Lp.Stop{}:
      Unit{}
    case Lp.Abort{}:
      Unit{}
    case Lp.Prompt{t}:
      Unit{}
    case Lp.Settled{k, o, bl, now, fu}:
      match fu:
        case True{}:
          Unit{}
        case False{}:
          lb.ns_settled(Bool.and(Lp.in_turn(p), Nat.is_eq(k, i)), bl, o, c, p, i, l, d, b, f, x, now, False{}, lb.halt_unfunded(Lp.tired(0n), Lp.spent(l), Lp.late(d, now)), lb.halt_unfunded(Lp.tired(1n+f), Lp.spent(l), Lp.late(d, now)))
    case Lp.Judged{k, ev, bl, now, fu}:
      match fu:
        case True{}:
          Unit{}
        case False{}:
          lb.ns_judged(Bool.and(Lp.in_judging(p), Nat.is_eq(k, i)), bl, c, p, i, l, d, b, f, x, ev, now, False{}, lb.halt_unfunded(Lp.tired(f), Lp.spent(l), Lp.late(d, now)))
    case Lp.Restart{}:
      Unit{}

# What a restart takes up
# -----------------------

# the act and the state it leaves agree: a restart after a Submit resumes
# that turn with that text, after a Judge asks for that check again; after
# a Report the state is ended with the reason reported
def lb.TiedTo(a: Lp.Act, -s: Lp.St) -> Type:
  match a:
    case Lp.Rest{}:
      Unit
    case Lp.Submit{k, t}:
      {S.does(s, Lp.Restart{}) == Lp.Resume{k, t} : Lp.Act}
    case Lp.Adopt{k}:
      Unit
    case Lp.Judge{k}:
      {S.does(s, Lp.Restart{}) == Lp.Judge{k} : Lp.Act}
    case Lp.Resume{k, t}:
      Unit
    case Lp.Report{w}:
      {S.phase(s) == Lp.Ended{w} : Lp.Phase}
    case Lp.Defer{}:
      Unit

def lb.Tied(r: Lp.St & Lp.Act) -> Type:
  lb.TiedTo(S.act(r), S.state(r))

def lb.tied_adv(h: Maybe<&2, Lp.End>, -i: Nat, -l: Maybe<&2, Nat>, -d: Maybe<&2, Nat>, -c: Lp.Cond, -b: String, -f: Nat, -x: Lp.Last) -> lb.Tied(Lp.advance.on(h, i, l, d, c, b, f, x)):
  match h:
    case Some{w}:
      {==}
    case None{}:
      {==}

def lb.tied_gate(c: Lp.Cond, -i: Nat, l: Maybe<&2, Nat>, d: Maybe<&2, Nat>, -b: String, f: Nat, -x: Lp.Last, now: Nat, fu: Bool) -> lb.Tied(Lp.gate(c, i, l, d, b, f, x, now, fu)):
  match c:
    case Lp.NoCond{}:
      lb.tied_adv(Lp.halt(f, fu, l, d, now), i, l, d, Lp.NoCond{}, b, f, x)
    case Lp.Until{cmd}:
      {==}
    case Lp.While{cmd}:
      {==}

def lb.tied_settled(m: Bool, bl: Bool, o: Lp.Out, c: Lp.Cond, -p: Lp.Phase, -i: Nat, l: Maybe<&2, Nat>, d: Maybe<&2, Nat>, -b: String, f: Nat, -x: Lp.Last, now: Nat, fu: Bool) -> lb.Tied(Lp.settled(m, p, i, l, d, c, b, f, x, o, bl, now, fu)):
  match m:
    case True{}:
      match bl:
        case True{}:
          Unit{}
        case False{}:
          match o:
            case Lp.Ran{}:
              lb.tied_gate(c, i, l, d, b, 0n, x, now, fu)
            case Lp.Errored{}:
              lb.tied_gate(c, i, l, d, b, 1n+f, x, now, fu)
            case Lp.Halted{}:
              Unit{}
    case False{}:
      Unit{}

def lb.tied_verdict(v: Lp.Verdict, -i: Nat, l: Maybe<&2, Nat>, d: Maybe<&2, Nat>, -c: Lp.Cond, -b: String, f: Nat, -x: Lp.Last, -ev: Lp.Evid, now: Nat, fu: Bool) -> lb.Tied(Lp.judged.verdict(v, i, l, d, c, b, f, x, ev, now, fu)):
  match v:
    case Lp.Confirmed{}:
      {==}
    case Lp.Refuted{}:
      lb.tied_adv(Lp.halt(f, fu, l, d, now), i, l, d, c, b, f, Lp.Check{i, ev})
    case Lp.Broken{}:
      {==}
    case Lp.Unjudged{}:
      Unit{}

def lb.tied_judged(m: Bool, bl: Bool, c: Lp.Cond, -p: Lp.Phase, -i: Nat, l: Maybe<&2, Nat>, d: Maybe<&2, Nat>, -b: String, f: Nat, -x: Lp.Last, ev: Lp.Evid, now: Nat, fu: Bool) -> lb.Tied(Lp.judged(m, p, i, l, d, c, b, f, x, ev, bl, now, fu)):
  match m:
    case True{}:
      match bl:
        case True{}:
          Unit{}
        case False{}:
          match c:
            case Lp.NoCond{}:
              lb.tied_adv(Lp.halt(f, fu, l, d, now), i, l, d, Lp.NoCond{}, b, f, x)
            case Lp.Until{cmd}:
              lb.tied_verdict(Lp.judge(True{}, ev), i, l, d, Lp.Until{cmd}, b, f, x, ev, now, fu)
            case Lp.While{cmd}:
              lb.tied_verdict(Lp.judge(False{}, ev), i, l, d, Lp.While{cmd}, b, f, x, ev, now, fu)
    case False{}:
      Unit{}

def lb.tied_enter(live: Bool, pr: Maybe<&2, String>, -i: Nat, -l: Maybe<&2, Nat>, -d: Maybe<&2, Nat>, -c: Lp.Cond, -b: String, -f: Nat, -x: Lp.Last, -lim: Lp.Limit, -c2: Lp.Cond, -now: Nat) -> lb.Tied(Lp.enter(live, i, l, d, c, b, f, x, lim, c2, pr, now)):
  match live:
    case True{}:
      {==}
    case False{}:
      match pr:
        case None{}:
          Unit{}
        case Some{t}:
          {==}

def lb.tied_stop(live: Bool, -p: Lp.Phase, -i: Nat, -l: Maybe<&2, Nat>, -d: Maybe<&2, Nat>, -c: Lp.Cond, -b: String, -f: Nat, -x: Lp.Last) -> lb.Tied(Lp.stop(live, p, i, l, d, c, b, f, x)):
  match live:
    case True{}:
      {==}
    case False{}:
      Unit{}

def lb.tied_abort(live: Bool, -p: Lp.Phase, -i: Nat, -l: Maybe<&2, Nat>, -d: Maybe<&2, Nat>, -c: Lp.Cond, -b: String, -f: Nat, -x: Lp.Last) -> lb.Tied(Lp.abort(live, p, i, l, d, c, b, f, x)):
  match live:
    case True{}:
      Unit{}
    case False{}:
      Unit{}

def lb.tied_prompt(live: Bool, -p: Lp.Phase, -i: Nat, -l: Maybe<&2, Nat>, -d: Maybe<&2, Nat>, -c: Lp.Cond, -b: String, -f: Nat, -x: Lp.Last, -t: String) -> lb.Tied(Lp.prompt(live, p, i, l, d, c, b, f, x, t)):
  match live:
    case True{}:
      Unit{}
    case False{}:
      Unit{}

def lb.tied_restart(p: Lp.Phase, -i: Nat, -l: Maybe<&2, Nat>, -d: Maybe<&2, Nat>, -c: Lp.Cond, -b: String, -f: Nat, -x: Lp.Last) -> lb.Tied(Lp.restart(p, i, l, d, c, b, f, x)):
  match p:
    case Lp.Off{}:
      Unit{}
    case Lp.Armed{}:
      Unit{}
    case Lp.Turn{}:
      Unit{}
    case Lp.Judging{}:
      {==}
    case Lp.Paused{}:
      Unit{}
    case Lp.Ended{w}:
      Unit{}

# every step leaves an act and a state that agree
def lb.tied(s: Lp.St, e: Lp.Ev) -> lb.Tied(Lp.step(s, e)):
  match s:
    case Lp.St{p, i, l, d, c, b, f, x}:
      match e:
        case Lp.Enter{lim, c2, pr, now}:
          lb.tied_enter(Lp.on(p), pr, i, l, d, c, b, f, x, lim, c2, now)
        case Lp.Stop{}:
          lb.tied_stop(Lp.on(p), p, i, l, d, c, b, f, x)
        case Lp.Abort{}:
          lb.tied_abort(Lp.on(p), p, i, l, d, c, b, f, x)
        case Lp.Prompt{t}:
          lb.tied_prompt(Lp.on(p), p, i, l, d, c, b, f, x, t)
        case Lp.Settled{k, o, bl, now, fu}:
          lb.tied_settled(Bool.and(Lp.in_turn(p), Nat.is_eq(k, i)), bl, o, c, p, i, l, d, b, f, x, now, fu)
        case Lp.Judged{k, ev, bl, now, fu}:
          lb.tied_judged(Bool.and(Lp.in_judging(p), Nat.is_eq(k, i)), bl, c, p, i, l, d, b, f, x, ev, now, fu)
        case Lp.Restart{}:
          lb.tied_restart(p, i, l, d, c, b, f, x)

# an act that is Submit{k, t}, tied to its state: a restart resumes k with t
def lb.tied_submit(-a: Lp.Act, -s: Lp.St, -k: Nat, -t: String, x: lb.TiedTo(a, s), h: {a == Lp.Submit{k, t} : Lp.Act}) -> {S.does(s, Lp.Restart{}) == Lp.Resume{k, t} : Lp.Act}:
  %h : lb.TiedTo(_, s)
  x

# an act that is Judge{k}, tied to its state: a restart judges k again
def lb.tied_judge(-a: Lp.Act, -s: Lp.St, -k: Nat, x: lb.TiedTo(a, s), h: {a == Lp.Judge{k} : Lp.Act}) -> {S.does(s, Lp.Restart{}) == Lp.Judge{k} : Lp.Act}:
  %h : lb.TiedTo(_, s)
  x

# an act that is Report{w}, tied to its state: the state is ended with w
def lb.tied_report(-a: Lp.Act, -s: Lp.St, -w: Lp.End, x: lb.TiedTo(a, s), h: {a == Lp.Report{w} : Lp.Act}) -> {S.phase(s) == Lp.Ended{w} : Lp.Phase}:
  %h : lb.TiedTo(_, s)
  x

# The bounds of a new loop
# ------------------------

# the result has l automatic iterations left and the deadline d
def lb.Bounds(r: Lp.St & Lp.Act, l: Maybe<&2, Nat>, d: Maybe<&2, Nat>) -> Type:
  {(S.left(S.state(r)), S.deadline(S.state(r))) == (l, d) : Maybe<&2, Nat> & Maybe<&2, Nat>}

# a new loop has the bounds of its limit, with or without an inline prompt
def lb.start_bounds(pr: Maybe<&2, String>, -lim: Lp.Limit, -c: Lp.Cond, -now: Nat) -> lb.Bounds(Lp.start(lim, c, pr, now), Lp.turns(lim), Lp.until(lim, now)):
  match pr:
    case None{}:
      {==}
    case Some{t}:
      {==}

def lb.enter_bounds.on(p: Lp.Phase, pr: Maybe<&2, String>, -i: Nat, -l: Maybe<&2, Nat>, -d: Maybe<&2, Nat>, -c: Lp.Cond, -b: String, -f: Nat, -x: Lp.Last, -lim: Lp.Limit, -c2: Lp.Cond, -now: Nat) -> lb.Unless(S.is_on(p), lb.Bounds(Lp.step(Lp.St{p, i, l, d, c, b, f, x}, Lp.Enter{lim, c2, pr, now}), Lp.turns(lim), Lp.until(lim, now))):
  match p:
    case Lp.Off{}:
      lb.start_bounds(pr, lim, c2, now)
    case Lp.Armed{}:
      Unit{}
    case Lp.Turn{}:
      Unit{}
    case Lp.Judging{}:
      Unit{}
    case Lp.Paused{}:
      Unit{}
    case Lp.Ended{w}:
      lb.start_bounds(pr, lim, c2, now)

# `/loop` with no loop on: the new loop has the bounds of its limit
def lb.enter_bounds(p: Lp.Phase, pr: Maybe<&2, String>, -i: Nat, -l: Maybe<&2, Nat>, -d: Maybe<&2, Nat>, -c: Lp.Cond, -b: String, -f: Nat, -x: Lp.Last, -lim: Lp.Limit, -c2: Lp.Cond, -now: Nat, off: {S.is_on(p) == False{} : Bool}) -> lb.Bounds(Lp.step(Lp.St{p, i, l, d, c, b, f, x}, Lp.Enter{lim, c2, pr, now}), Lp.turns(lim), Lp.until(lim, now)):
  lb.unless(S.is_on(p), lb.Bounds(Lp.step(Lp.St{p, i, l, d, c, b, f, x}, Lp.Enter{lim, c2, pr, now}), Lp.turns(lim), Lp.until(lim, now)), off, lb.enter_bounds.on(p, pr, i, l, d, c, b, f, x, lim, c2, now))

# the result is at iteration k, with no failed turn counted and no evidence
def lb.Fresh(r: Lp.St & Lp.Act, k: Nat) -> Type:
  {(S.iter(S.state(r)), (S.fails(S.state(r)), S.last(S.state(r)))) == (k, (0n, Lp.NoCheck{})) : Nat & (Nat & Lp.Last)}

def lb.enter_fresh.on(p: Lp.Phase, -i: Nat, -l: Maybe<&2, Nat>, -d: Maybe<&2, Nat>, -c: Lp.Cond, -b: String, -f: Nat, -x: Lp.Last, -lim: Lp.Limit, -c2: Lp.Cond, -t: String, -now: Nat) -> lb.Unless(S.is_on(p), lb.Fresh(Lp.step(Lp.St{p, i, l, d, c, b, f, x}, Lp.Enter{lim, c2, Some{t}, now}), 1n) & lb.Fresh(Lp.step(Lp.St{p, i, l, d, c, b, f, x}, Lp.Enter{lim, c2, None{}, now}), 0n)):
  match p:
    case Lp.Off{}:
      ({==}, {==})
    case Lp.Armed{}:
      Unit{}
    case Lp.Turn{}:
      Unit{}
    case Lp.Judging{}:
      Unit{}
    case Lp.Paused{}:
      Unit{}
    case Lp.Ended{w}:
      ({==}, {==})

# `/loop` with no loop on: the new loop keeps nothing of the state before
# it; with an inline prompt t it is at iteration 1, without one at 0
def lb.enter_fresh(p: Lp.Phase, -i: Nat, -l: Maybe<&2, Nat>, -d: Maybe<&2, Nat>, -c: Lp.Cond, -b: String, -f: Nat, -x: Lp.Last, -lim: Lp.Limit, -c2: Lp.Cond, -t: String, -now: Nat, off: {S.is_on(p) == False{} : Bool}) -> lb.Fresh(Lp.step(Lp.St{p, i, l, d, c, b, f, x}, Lp.Enter{lim, c2, Some{t}, now}), 1n) & lb.Fresh(Lp.step(Lp.St{p, i, l, d, c, b, f, x}, Lp.Enter{lim, c2, None{}, now}), 0n):
  lb.unless(S.is_on(p), lb.Fresh(Lp.step(Lp.St{p, i, l, d, c, b, f, x}, Lp.Enter{lim, c2, Some{t}, now}), 1n) & lb.Fresh(Lp.step(Lp.St{p, i, l, d, c, b, f, x}, Lp.Enter{lim, c2, None{}, now}), 0n), off, lb.enter_fresh.on(p, i, l, d, c, b, f, x, lim, c2, t, now))

# An event delivered twice
# ------------------------

# e, applied to the state of the result r, changes nothing and does nothing
def lb.Noop(r: Lp.St & Lp.Act, e: Lp.Ev) -> Type:
  {Lp.step(S.state(r), e) == (S.state(r), Lp.Rest{}) : Lp.St & Lp.Act}

# after an advance the settled turn k is stale: the loop ended, or is in
# turn 1 + i and k is i
def lb.noop_adv_s(h: Maybe<&2, Lp.End>, -i: Nat, -l: Maybe<&2, Nat>, -d: Maybe<&2, Nat>, -c: Lp.Cond, -b: String, -f: Nat, -x: Lp.Last, -k: Nat, -o: Lp.Out, -now: Nat, -fu: Bool, hk: {False{} == Nat.is_eq(k, 1n+i) : Bool}) -> lb.Noop(Lp.advance.on(h, i, l, d, c, b, f, x), Lp.Settled{k, o, False{}, now, fu}):
  match h:
    case Some{w}:
      {==}
    case None{}:
      %hk : {Lp.settled(_, Lp.Turn{}, 1n+i, Lp.less(l), d, c, b, f, x, o, False{}, now, fu) == (Lp.St{Lp.Turn{}, 1n+i, Lp.less(l), d, c, b, f, x}, Lp.Rest{}) : Lp.St & Lp.Act}
      {==}

def lb.noop_gate_s(c: Lp.Cond, -i: Nat, l: Maybe<&2, Nat>, d: Maybe<&2, Nat>, -b: String, f: Nat, -x: Lp.Last, -k: Nat, -o: Lp.Out, now: Nat, fu: Bool, hk: {False{} == Nat.is_eq(k, 1n+i) : Bool}) -> lb.Noop(Lp.gate(c, i, l, d, b, f, x, now, fu), Lp.Settled{k, o, False{}, now, fu}):
  match c:
    case Lp.NoCond{}:
      lb.noop_adv_s(Lp.halt(f, fu, l, d, now), i, l, d, Lp.NoCond{}, b, f, x, k, o, now, fu, hk)
    case Lp.Until{cmd}:
      {==}
    case Lp.While{cmd}:
      {==}

# a settled turn of an idle session, delivered again to a loop that was in
# its turn: not its own (m False), or its own and the loop moved on
def lb.noop_settled(m: Bool, o: Lp.Out, c: Lp.Cond, k: Nat, i: Nat, l: Maybe<&2, Nat>, d: Maybe<&2, Nat>, -b: String, f: Nat, -x: Lp.Last, now: Nat, fu: Bool, hm: {m == Nat.is_eq(k, i) : Bool}) -> lb.Noop(Lp.settled(m, Lp.Turn{}, i, l, d, c, b, f, x, o, False{}, now, fu), Lp.Settled{k, o, False{}, now, fu}):
  match m:
    case True{}:
      match o:
        case Lp.Ran{}:
          lb.noop_gate_s(c, i, l, d, b, 0n, x, k, Lp.Ran{}, now, fu, lb.eq_not_succ(k, i, hm))
        case Lp.Errored{}:
          lb.noop_gate_s(c, i, l, d, b, 1n+f, x, k, Lp.Errored{}, now, fu, lb.eq_not_succ(k, i, hm))
        case Lp.Halted{}:
          {==}
    case False{}:
      %hm : {Lp.settled(_, Lp.Turn{}, i, l, d, c, b, f, x, o, False{}, now, fu) == (Lp.St{Lp.Turn{}, i, l, d, c, b, f, x}, Lp.Rest{}) : Lp.St & Lp.Act}
      {==}

# after an advance a judged check is stale: the loop ended or is in a turn
def lb.noop_adv_j(h: Maybe<&2, Lp.End>, -i: Nat, -l: Maybe<&2, Nat>, -d: Maybe<&2, Nat>, -c: Lp.Cond, -b: String, -f: Nat, -x: Lp.Last, -k: Nat, -ev: Lp.Evid, -now: Nat, -fu: Bool) -> lb.Noop(Lp.advance.on(h, i, l, d, c, b, f, x), Lp.Judged{k, ev, False{}, now, fu}):
  match h:
    case Some{w}:
      {==}
    case None{}:
      {==}

# a judged check of an idle session, delivered again to a loop that was
# judging: not its own (m False); its own and the loop ended or moved on;
# or cancelled, which changed nothing the first time either
def lb.noop_judged(m: Bool, c: Lp.Cond, ev: Lp.Evid, -k: Nat, -i: Nat, l: Maybe<&2, Nat>, d: Maybe<&2, Nat>, -b: String, f: Nat, -x: Lp.Last, now: Nat, fu: Bool, hm: {m == Nat.is_eq(k, i) : Bool}) -> lb.Noop(Lp.judged(m, Lp.Judging{}, i, l, d, c, b, f, x, ev, False{}, now, fu), Lp.Judged{k, ev, False{}, now, fu}):
  match m:
    case True{}:
      match c:
        case Lp.NoCond{}:
          lb.noop_adv_j(Lp.halt(f, fu, l, d, now), i, l, d, Lp.NoCond{}, b, f, x, k, ev, now, fu)
        case Lp.Until{cmd}:
          match ev:
            case Lp.Exited{code}:
              match code:
                case 0n:
                  {==}
                case 1n:
                  lb.noop_adv_j(Lp.halt(f, fu, l, d, now), i, l, d, Lp.Until{cmd}, b, f, Lp.Check{i, Lp.Exited{1n}}, k, Lp.Exited{1n}, now, fu)
                case 2n+q:
                  {==}
            case Lp.NoStatus{}:
              {==}
            case Lp.TimedOut{}:
              {==}
            case Lp.SpawnFailed{}:
              {==}
            case Lp.Cancelled{}:
              %hm : {Lp.judged(_, Lp.Judging{}, i, l, d, Lp.Until{cmd}, b, f, x, Lp.Cancelled{}, False{}, now, fu) == (Lp.St{Lp.Judging{}, i, l, d, Lp.Until{cmd}, b, f, x}, Lp.Rest{}) : Lp.St & Lp.Act}
              {==}
        case Lp.While{cmd}:
          match ev:
            case Lp.Exited{code}:
              match code:
                case 0n:
                  lb.noop_adv_j(Lp.halt(f, fu, l, d, now), i, l, d, Lp.While{cmd}, b, f, Lp.Check{i, Lp.Exited{0n}}, k, Lp.Exited{0n}, now, fu)
                case 1n:
                  {==}
                case 2n+q:
                  {==}
            case Lp.NoStatus{}:
              {==}
            case Lp.TimedOut{}:
              {==}
            case Lp.SpawnFailed{}:
              {==}
            case Lp.Cancelled{}:
              %hm : {Lp.judged(_, Lp.Judging{}, i, l, d, Lp.While{cmd}, b, f, x, Lp.Cancelled{}, False{}, now, fu) == (Lp.St{Lp.Judging{}, i, l, d, Lp.While{cmd}, b, f, x}, Lp.Rest{}) : Lp.St & Lp.Act}
              {==}
    case False{}:
      %hm : {Lp.judged(_, Lp.Judging{}, i, l, d, c, b, f, x, ev, False{}, now, fu) == (Lp.St{Lp.Judging{}, i, l, d, c, b, f, x}, Lp.Rest{}) : Lp.St & Lp.Act}
      {==}

def lb.noop_stop(p: Lp.Phase, -i: Nat, -l: Maybe<&2, Nat>, -d: Maybe<&2, Nat>, -c: Lp.Cond, -b: String, -f: Nat, -x: Lp.Last) -> lb.Noop(Lp.step(Lp.St{p, i, l, d, c, b, f, x}, Lp.Stop{}), Lp.Stop{}):
  match p:
    case Lp.Off{}:
      {==}
    case Lp.Armed{}:
      {==}
    case Lp.Turn{}:
      {==}
    case Lp.Judging{}:
      {==}
    case Lp.Paused{}:
      {==}
    case Lp.Ended{w}:
      {==}

def lb.noop_abort(p: Lp.Phase, -i: Nat, -l: Maybe<&2, Nat>, -d: Maybe<&2, Nat>, -c: Lp.Cond, -b: String, -f: Nat, -x: Lp.Last) -> lb.Noop(Lp.step(Lp.St{p, i, l, d, c, b, f, x}, Lp.Abort{}), Lp.Abort{}):
  match p:
    case Lp.Off{}:
      {==}
    case Lp.Armed{}:
      {==}
    case Lp.Turn{}:
      {==}
    case Lp.Judging{}:
      {==}
    case Lp.Paused{}:
      {==}
    case Lp.Ended{w}:
      {==}

def lb.noop_turn(p: Lp.Phase, +k: Nat, +i: Nat, l: Maybe<&2, Nat>, d: Maybe<&2, Nat>, c: Lp.Cond, -b: String, f: Nat, -x: Lp.Last, o: Lp.Out, now: Nat, fu: Bool) -> lb.Noop(Lp.step(Lp.St{p, i, l, d, c, b, f, x}, Lp.Settled{k, o, False{}, now, fu}), Lp.Settled{k, o, False{}, now, fu}):
  match p:
    case Lp.Off{}:
      {==}
    case Lp.Armed{}:
      {==}
    case Lp.Turn{}:
      lb.noop_settled(Nat.is_eq(k, i), o, c, k, i, l, d, b, f, x, now, fu, {==})
    case Lp.Judging{}:
      {==}
    case Lp.Paused{}:
      {==}
    case Lp.Ended{w}:
      {==}

def lb.noop_check(p: Lp.Phase, k: Nat, i: Nat, l: Maybe<&2, Nat>, d: Maybe<&2, Nat>, c: Lp.Cond, -b: String, f: Nat, -x: Lp.Last, ev: Lp.Evid, now: Nat, fu: Bool) -> lb.Noop(Lp.step(Lp.St{p, i, l, d, c, b, f, x}, Lp.Judged{k, ev, False{}, now, fu}), Lp.Judged{k, ev, False{}, now, fu}):
  match p:
    case Lp.Off{}:
      {==}
    case Lp.Armed{}:
      {==}
    case Lp.Turn{}:
      {==}
    case Lp.Judging{}:
      lb.noop_judged(Nat.is_eq(k, i), c, ev, k, i, l, d, b, f, x, now, fu, {==})
    case Lp.Paused{}:
      {==}
    case Lp.Ended{w}:
      {==}

# LAW loop_redelivery_is_noop, on an open state
def lb.noop(e: Lp.Ev, p: Lp.Phase, i: Nat, l: Maybe<&2, Nat>, d: Maybe<&2, Nat>, c: Lp.Cond, -b: String, f: Nat, -x: Lp.Last) -> lb.When(S.once(e), lb.Noop(Lp.step(Lp.St{p, i, l, d, c, b, f, x}, e), e)):
  match e:
    case Lp.Enter{lim, c2, pr, now}:
      Unit{}
    case Lp.Stop{}:
      lb.noop_stop(p, i, l, d, c, b, f, x)
    case Lp.Abort{}:
      lb.noop_abort(p, i, l, d, c, b, f, x)
    case Lp.Prompt{t}:
      Unit{}
    case Lp.Settled{k, o, bl, now, fu}:
      match bl:
        case True{}:
          Unit{}
        case False{}:
          lb.noop_turn(p, k, i, l, d, c, b, f, x, o, now, fu)
    case Lp.Judged{k, ev, bl, now, fu}:
      match bl:
        case True{}:
          Unit{}
        case False{}:
          lb.noop_check(p, k, i, l, d, c, b, f, x, ev, now, fu)
    case Lp.Restart{}:
      Unit{}

# Queued input
# ------------

# the result keeps the state s and only waits
def lb.Waits(r: Lp.St & Lp.Act, s: Lp.St) -> Type:
  {(S.state(r), S.waits(S.act(r))) == (s, True{}) : Lp.St & Bool}

def lb.blocked_mine(m: Bool, -i: Nat, -l: Maybe<&2, Nat>, -d: Maybe<&2, Nat>, -c: Lp.Cond, -b: String, -f: Nat, -x: Lp.Last, -o: Lp.Out, -now: Nat, -fu: Bool) -> lb.Waits(Lp.settled(m, Lp.Turn{}, i, l, d, c, b, f, x, o, True{}, now, fu), Lp.St{Lp.Turn{}, i, l, d, c, b, f, x}):
  match m:
    case True{}:
      {==}
    case False{}:
      {==}

def lb.blocked_turn(p: Lp.Phase, k: Nat, i: Nat, -l: Maybe<&2, Nat>, -d: Maybe<&2, Nat>, -c: Lp.Cond, -b: String, -f: Nat, -x: Lp.Last, -o: Lp.Out, -now: Nat, -fu: Bool) -> lb.Waits(Lp.step(Lp.St{p, i, l, d, c, b, f, x}, Lp.Settled{k, o, True{}, now, fu}), Lp.St{p, i, l, d, c, b, f, x}):
  match p:
    case Lp.Off{}:
      {==}
    case Lp.Armed{}:
      {==}
    case Lp.Turn{}:
      lb.blocked_mine(Nat.is_eq(k, i), i, l, d, c, b, f, x, o, now, fu)
    case Lp.Judging{}:
      {==}
    case Lp.Paused{}:
      {==}
    case Lp.Ended{w}:
      {==}

def lb.blocked_own(m: Bool, -i: Nat, -l: Maybe<&2, Nat>, -d: Maybe<&2, Nat>, -c: Lp.Cond, -b: String, -f: Nat, -x: Lp.Last, -ev: Lp.Evid, -now: Nat, -fu: Bool) -> lb.Waits(Lp.judged(m, Lp.Judging{}, i, l, d, c, b, f, x, ev, True{}, now, fu), Lp.St{Lp.Judging{}, i, l, d, c, b, f, x}):
  match m:
    case True{}:
      {==}
    case False{}:
      {==}

def lb.blocked_check(p: Lp.Phase, k: Nat, i: Nat, -l: Maybe<&2, Nat>, -d: Maybe<&2, Nat>, -c: Lp.Cond, -b: String, -f: Nat, -x: Lp.Last, -ev: Lp.Evid, -now: Nat, -fu: Bool) -> lb.Waits(Lp.step(Lp.St{p, i, l, d, c, b, f, x}, Lp.Judged{k, ev, True{}, now, fu}), Lp.St{p, i, l, d, c, b, f, x}):
  match p:
    case Lp.Off{}:
      {==}
    case Lp.Armed{}:
      {==}
    case Lp.Turn{}:
      {==}
    case Lp.Judging{}:
      lb.blocked_own(Nat.is_eq(k, i), i, l, d, c, b, f, x, ev, now, fu)
    case Lp.Paused{}:
      {==}
    case Lp.Ended{w}:
      {==}

# LAW loop_blocked_waits, on an open state
def lb.blocked(e: Lp.Ev, p: Lp.Phase, i: Nat, -l: Maybe<&2, Nat>, -d: Maybe<&2, Nat>, -c: Lp.Cond, -b: String, -f: Nat, -x: Lp.Last) -> lb.When(S.blocked(e), lb.Waits(Lp.step(Lp.St{p, i, l, d, c, b, f, x}, e), Lp.St{p, i, l, d, c, b, f, x})):
  match e:
    case Lp.Enter{lim, c2, pr, now}:
      Unit{}
    case Lp.Stop{}:
      Unit{}
    case Lp.Abort{}:
      Unit{}
    case Lp.Prompt{t}:
      Unit{}
    case Lp.Settled{k, o, bl, now, fu}:
      match bl:
        case True{}:
          lb.blocked_turn(p, k, i, l, d, c, b, f, x, o, now, fu)
        case False{}:
          Unit{}
    case Lp.Judged{k, ev, bl, now, fu}:
      match bl:
        case True{}:
          lb.blocked_check(p, k, i, l, d, c, b, f, x, ev, now, fu)
        case False{}:
          Unit{}
    case Lp.Restart{}:
      Unit{}

# The evidence kept
# -----------------

# LAW loop_records_evidence, at the check: every verdict but Unjudged
# keeps the evidence with the iteration
def lb.records(c: Lp.Cond, ev: Lp.Evid, -i: Nat, l: Maybe<&2, Nat>, d: Maybe<&2, Nat>, -b: String, f: Nat, -x: Lp.Last, now: Nat, fu: Bool) -> lb.When(S.has_cond(c), lb.When(S.decides(ev), {S.last(S.state(Lp.judged.cond(c, i, l, d, b, f, x, ev, now, fu))) == Lp.Check{i, ev} : Lp.Last})):
  match c:
    case Lp.NoCond{}:
      Unit{}
    case Lp.Until{cmd}:
      match ev:
        case Lp.Exited{code}:
          match code:
            case 0n:
              {==}
            case 1n:
              lb.adv_last(Lp.halt(f, fu, l, d, now), i, l, d, Lp.Until{cmd}, b, f, Lp.Check{i, Lp.Exited{1n}})
            case 2n+q:
              {==}
        case Lp.NoStatus{}:
          {==}
        case Lp.TimedOut{}:
          {==}
        case Lp.SpawnFailed{}:
          {==}
        case Lp.Cancelled{}:
          Unit{}
    case Lp.While{cmd}:
      match ev:
        case Lp.Exited{code}:
          match code:
            case 0n:
              lb.adv_last(Lp.halt(f, fu, l, d, now), i, l, d, Lp.While{cmd}, b, f, Lp.Check{i, Lp.Exited{0n}})
            case 1n:
              {==}
            case 2n+q:
              {==}
        case Lp.NoStatus{}:
          {==}
        case Lp.TimedOut{}:
          {==}
        case Lp.SpawnFailed{}:
          {==}
        case Lp.Cancelled{}:
          Unit{}

# the result keeps the evidence x
def lb.Kept(r: Lp.St & Lp.Act, x: Lp.Last) -> Type:
  {S.last(S.state(r)) == x : Lp.Last}

def lb.kept_gate(c: Lp.Cond, -i: Nat, l: Maybe<&2, Nat>, d: Maybe<&2, Nat>, -b: String, f: Nat, -x: Lp.Last, now: Nat, fu: Bool) -> lb.Kept(Lp.gate(c, i, l, d, b, f, x, now, fu), x):
  match c:
    case Lp.NoCond{}:
      lb.adv_last(Lp.halt(f, fu, l, d, now), i, l, d, Lp.NoCond{}, b, f, x)
    case Lp.Until{cmd}:
      {==}
    case Lp.While{cmd}:
      {==}

def lb.kept_settled(m: Bool, bl: Bool, o: Lp.Out, c: Lp.Cond, -p: Lp.Phase, -i: Nat, l: Maybe<&2, Nat>, d: Maybe<&2, Nat>, -b: String, f: Nat, -x: Lp.Last, now: Nat, fu: Bool) -> lb.Kept(Lp.settled(m, p, i, l, d, c, b, f, x, o, bl, now, fu), x):
  match m:
    case True{}:
      match bl:
        case True{}:
          {==}
        case False{}:
          match o:
            case Lp.Ran{}:
              lb.kept_gate(c, i, l, d, b, 0n, x, now, fu)
            case Lp.Errored{}:
              lb.kept_gate(c, i, l, d, b, 1n+f, x, now, fu)
            case Lp.Halted{}:
              {==}
    case False{}:
      {==}

def lb.kept_stop(live: Bool, -p: Lp.Phase, -i: Nat, -l: Maybe<&2, Nat>, -d: Maybe<&2, Nat>, -c: Lp.Cond, -b: String, -f: Nat, -x: Lp.Last) -> lb.Kept(Lp.stop(live, p, i, l, d, c, b, f, x), x):
  match live:
    case True{}:
      {==}
    case False{}:
      {==}

def lb.kept_abort(live: Bool, -p: Lp.Phase, -i: Nat, -l: Maybe<&2, Nat>, -d: Maybe<&2, Nat>, -c: Lp.Cond, -b: String, -f: Nat, -x: Lp.Last) -> lb.Kept(Lp.abort(live, p, i, l, d, c, b, f, x), x):
  match live:
    case True{}:
      {==}
    case False{}:
      {==}

def lb.kept_prompt(live: Bool, -p: Lp.Phase, -i: Nat, -l: Maybe<&2, Nat>, -d: Maybe<&2, Nat>, -c: Lp.Cond, -b: String, -f: Nat, -x: Lp.Last, -t: String) -> lb.Kept(Lp.prompt(live, p, i, l, d, c, b, f, x, t), x):
  match live:
    case True{}:
      {==}
    case False{}:
      {==}

def lb.kept_restart(p: Lp.Phase, -i: Nat, -l: Maybe<&2, Nat>, -d: Maybe<&2, Nat>, -c: Lp.Cond, -b: String, -f: Nat, -x: Lp.Last) -> lb.Kept(Lp.restart(p, i, l, d, c, b, f, x), x):
  match p:
    case Lp.Off{}:
      {==}
    case Lp.Armed{}:
      {==}
    case Lp.Turn{}:
      {==}
    case Lp.Judging{}:
      {==}
    case Lp.Paused{}:
      {==}
    case Lp.Ended{w}:
      {==}

# LAW loop_evidence_only_from_checks, on an open state
def lb.kept(e: Lp.Ev, p: Lp.Phase, i: Nat, l: Maybe<&2, Nat>, d: Maybe<&2, Nat>, c: Lp.Cond, -b: String, f: Nat, -x: Lp.Last) -> lb.Unless(Bool.or(S.is_enter(e), S.is_judged(e)), lb.Kept(Lp.step(Lp.St{p, i, l, d, c, b, f, x}, e), x)):
  match e:
    case Lp.Enter{lim, c2, pr, now}:
      Unit{}
    case Lp.Stop{}:
      lb.kept_stop(Lp.on(p), p, i, l, d, c, b, f, x)
    case Lp.Abort{}:
      lb.kept_abort(Lp.on(p), p, i, l, d, c, b, f, x)
    case Lp.Prompt{t}:
      lb.kept_prompt(Lp.on(p), p, i, l, d, c, b, f, x, t)
    case Lp.Settled{k, o, bl, now, fu}:
      lb.kept_settled(Bool.and(Lp.in_turn(p), Nat.is_eq(k, i)), bl, o, c, p, i, l, d, b, f, x, now, fu)
    case Lp.Judged{k, ev, bl, now, fu}:
      Unit{}
    case Lp.Restart{}:
      lb.kept_restart(p, i, l, d, c, b, f, x)
