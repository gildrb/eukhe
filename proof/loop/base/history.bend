# eukhe: lemmas the history proofs of area loop share (laws/loop/history.bend):
# Bool and Nat facts (a refuted premise, the order of Nats), the bounds of
# an automatic iteration read back from `halt`, and four one-step facts of
# Lp.step, each proven by cases on the phase and the event, with the two
# tests the checker cannot compute (Nat.is_eq(k, i), the bound `halt`)
# taken as a parameter:
# - lh.off_step: an off state is fixed by every event but Enter;
# - lh.quiet_step: an off or paused state starts nothing and stays so;
# - lh.view_step: what an unattended event keeps (the condition, the
#   deadline, the count less the iteration it starts, at most one report,
#   the prompt, the text);
# - lh.pot_step: the automatic iterations a failing run can still start.
# The lh.*_hist lemmas fold them over a history by induction.

import Base
import ../../../bend/loop.bend as Lp
import ../../../spec/loop/loop.bend as S

# ---- Bool ----

def lh.IfF(b: Bool, G: Type) -> Type:
  match b:
    case True{}:
      G
    case False{}:
      Unit

def lh.IfT(b: Bool, G: Type) -> Type:
  match b:
    case True{}:
      Unit
    case False{}:
      G

# a premise False == True proves anything
def lh.absurd_ft(-G: Type, e: {False{} == True{} : Bool}) -> G:
  %e : lh.IfF(_, G)
  Unit{}

# a premise True == False proves anything
def lh.absurd_tf(-G: Type, e: {True{} == False{} : Bool}) -> G:
  %e : lh.IfT(_, G)
  Unit{}

def lh.and_l(a: Bool, -b: Bool, e: {Bool.and(a, b) == True{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      e

def lh.and_r(a: Bool, -b: Bool, e: {Bool.and(a, b) == True{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case True{}:
      e
    case False{}:
      lh.absurd_ft({b == True{} : Bool}, e)

def lh.and_tt(-a: Bool, -b: Bool, ha: {a == True{} : Bool}, hb: {b == True{} : Bool}) -> {Bool.and(a, b) == True{} : Bool}:
  %Equal.sym(Bool, a, True{}, ha) : {Bool.and(_, b) == True{} : Bool}
  %Equal.sym(Bool, b, True{}, hb) : {Bool.and(True{}, _) == True{} : Bool}
  {==}

# ---- Nat order ----

def lh.le_zero(n: Nat) -> {Nat.is_le(0n, n) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      {==}

def lh.le_refl(n: Nat) -> {Nat.is_le(n, n) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      lh.le_refl(p)

def lh.le_trans(a: Nat, b: Nat, c: Nat, h1: {Nat.is_le(a, b) == True{} : Bool}, h2: {Nat.is_le(b, c) == True{} : Bool}) -> {Nat.is_le(a, c) == True{} : Bool}:
  match a b c:
    case 0n _ 0n:
      {==}
    case 0n _ 1n+r:
      {==}
    case 1n+p 0n _:
      lh.absurd_ft({Nat.is_le(1n+p, c) == True{} : Bool}, h1)
    case 1n+p 1n+q 0n:
      lh.absurd_ft({Nat.is_le(1n+p, 0n) == True{} : Bool}, h2)
    case 1n+p 1n+q 1n+r:
      lh.le_trans(p, q, r, h1, h2)

def lh.one_if_le(b: Bool) -> {Nat.is_le(S.one_if(b), 1n) == True{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

# a count x under p, and one more (if sb) with p under q: one more with x
# is under q
def lh.le_bump(sb: Bool, x: Nat, p: Nat, q: Nat, ih: {Nat.is_le(x, p) == True{} : Bool}, st: {Nat.is_le(Nat.add(S.one_if(sb), p), q) == True{} : Bool}) -> {Nat.is_le(Nat.add(S.one_if(sb), x), q) == True{} : Bool}:
  match sb:
    case True{}:
      lh.le_trans(1n+x, 1n+p, q, ih, st)
    case False{}:
      lh.le_trans(x, p, q, ih, st)

# ---- the bounds ----

def lh.is_none(h: Maybe<&2, Lp.End>) -> Bool:
  match h:
    case None{}:
      True{}
    case Some{w}:
      False{}

# g holds and no bound forbids the next iteration
def lh.none_if(g: Bool, h: Maybe<&2, Lp.End>) -> Bool:
  match g:
    case True{}:
      lh.is_none(h)
    case False{}:
      False{}

# a spent count forbids the next iteration
def lh.halt_spent(sp: Bool, t: Bool, fu: Bool, -la: Bool) -> {lh.none_if(sp, Lp.halt.fails(t, fu, sp, la)) == False{} : Bool}:
  match sp t fu:
    case False{} _ _:
      {==}
    case True{} True{} _:
      {==}
    case True{} False{} True{}:
      {==}
    case True{} False{} False{}:
      {==}

# three failed turns forbid the next iteration
def lh.halt_tired(t: Bool, -fu: Bool, -sp: Bool, -la: Bool) -> {lh.none_if(t, Lp.halt.fails(t, fu, sp, la)) == False{} : Bool}:
  match t:
    case True{}:
      {==}
    case False{}:
      {==}

# ---- off: nothing changes ----

def lh.OffStep(s: Lp.St, e: Lp.Ev) -> Type:
  {(s, Lp.Rest{}) == Lp.step(s, e) : Lp.St & Lp.Act}

# an off state is fixed by every event but Enter, and answers Rest
def lh.off_step(s: Lp.St, e: Lp.Ev, off: {S.is_on(S.phase(s)) == False{} : Bool}, ne: {Bool.not(S.is_enter(e)) == True{} : Bool}) -> lh.OffStep(s, e):
  match s e:
    case Lp.St{Lp.Armed{}, i, l, d, c, b, f, x} _:
      lh.absurd_tf(lh.OffStep(Lp.St{Lp.Armed{}, i, l, d, c, b, f, x}, e), off)
    case Lp.St{Lp.Turn{}, i, l, d, c, b, f, x} _:
      lh.absurd_tf(lh.OffStep(Lp.St{Lp.Turn{}, i, l, d, c, b, f, x}, e), off)
    case Lp.St{Lp.Judging{}, i, l, d, c, b, f, x} _:
      lh.absurd_tf(lh.OffStep(Lp.St{Lp.Judging{}, i, l, d, c, b, f, x}, e), off)
    case Lp.St{Lp.Paused{}, i, l, d, c, b, f, x} _:
      lh.absurd_tf(lh.OffStep(Lp.St{Lp.Paused{}, i, l, d, c, b, f, x}, e), off)
    case Lp.St{Lp.Off{}, i, l, d, c, b, f, x} Lp.Enter{lim, c2, pr, now}:
      lh.absurd_ft(lh.OffStep(Lp.St{Lp.Off{}, i, l, d, c, b, f, x}, Lp.Enter{lim, c2, pr, now}), ne)
    case Lp.St{Lp.Off{}, i, l, d, c, b, f, x} Lp.Stop{}:
      {==}
    case Lp.St{Lp.Off{}, i, l, d, c, b, f, x} Lp.Abort{}:
      {==}
    case Lp.St{Lp.Off{}, i, l, d, c, b, f, x} Lp.Prompt{t}:
      {==}
    case Lp.St{Lp.Off{}, i, l, d, c, b, f, x} Lp.Settled{k, out, blocked, now, funded}:
      {==}
    case Lp.St{Lp.Off{}, i, l, d, c, b, f, x} Lp.Judged{k, ev, blocked, now, funded}:
      {==}
    case Lp.St{Lp.Off{}, i, l, d, c, b, f, x} Lp.Restart{}:
      {==}
    case Lp.St{Lp.Ended{w}, i, l, d, c, b, f, x} Lp.Enter{lim, c2, pr, now}:
      lh.absurd_ft(lh.OffStep(Lp.St{Lp.Ended{w}, i, l, d, c, b, f, x}, Lp.Enter{lim, c2, pr, now}), ne)
    case Lp.St{Lp.Ended{w}, i, l, d, c, b, f, x} Lp.Stop{}:
      {==}
    case Lp.St{Lp.Ended{w}, i, l, d, c, b, f, x} Lp.Abort{}:
      {==}
    case Lp.St{Lp.Ended{w}, i, l, d, c, b, f, x} Lp.Prompt{t}:
      {==}
    case Lp.St{Lp.Ended{w}, i, l, d, c, b, f, x} Lp.Settled{k, out, blocked, now, funded}:
      {==}
    case Lp.St{Lp.Ended{w}, i, l, d, c, b, f, x} Lp.Judged{k, ev, blocked, now, funded}:
      {==}
    case Lp.St{Lp.Ended{w}, i, l, d, c, b, f, x} Lp.Restart{}:
      {==}

def lh.off_hist(h: List<&2, Lp.Ev>, +s: Lp.St, +off: {S.is_on(S.phase(s)) == False{} : Bool}, ne: {S.no_enter(h) == True{} : Bool}) -> {(S.after(h, s), S.all_rest(S.acts(h, s))) == (s, True{}) : Lp.St & Bool}:
  match h:
    case Nil{}:
      {==}
    case Con{+e, t}:
      +nn = ne
      %lh.off_step(s, e, off, lh.and_l(Bool.not(S.is_enter(e)), S.no_enter(t), nn)) : {(S.after(t, S.state(_)), Bool.and(S.is_rest(S.act(_)), S.all_rest(S.acts(t, S.state(_))))) == (s, True{}) : Lp.St & Bool}
      lh.off_hist(t, s, off, lh.and_r(Bool.not(S.is_enter(e)), S.no_enter(t), nn))

# ---- quiet: off or paused ----

def lh.quiet(p: Lp.Phase) -> Bool:
  match p:
    case Lp.Off{}:
      True{}
    case Lp.Armed{}:
      False{}
    case Lp.Turn{}:
      False{}
    case Lp.Judging{}:
      False{}
    case Lp.Paused{}:
      True{}
    case Lp.Ended{w}:
      True{}

def lh.QuietStep(s: Lp.St, e: Lp.Ev) -> Type:
  {Bool.and(Bool.not(S.starts(S.does(s, e))), lh.quiet(S.phase(S.next(s, e)))) == True{} : Bool}

# a quiet state starts nothing at an unattended event, and stays quiet
def lh.quiet_step(s: Lp.St, e: Lp.Ev, q: {lh.quiet(S.phase(s)) == True{} : Bool}, u: {Bool.not(S.is_user(e)) == True{} : Bool}) -> {Bool.and(Bool.not(S.starts(S.does(s, e))), lh.quiet(S.phase(S.next(s, e)))) == True{} : Bool}:
  match s e:
    case Lp.St{p, i, l, d, c, b, f, x} Lp.Enter{lim, c2, pr, now}:
      lh.absurd_ft(lh.QuietStep(Lp.St{p, i, l, d, c, b, f, x}, Lp.Enter{lim, c2, pr, now}), u)
    case Lp.St{p, i, l, d, c, b, f, x} Lp.Prompt{t}:
      lh.absurd_ft(lh.QuietStep(Lp.St{p, i, l, d, c, b, f, x}, Lp.Prompt{t}), u)
    case Lp.St{Lp.Armed{}, i, l, d, c, b, f, x} _:
      lh.absurd_ft(lh.QuietStep(Lp.St{Lp.Armed{}, i, l, d, c, b, f, x}, e), q)
    case Lp.St{Lp.Turn{}, i, l, d, c, b, f, x} _:
      lh.absurd_ft(lh.QuietStep(Lp.St{Lp.Turn{}, i, l, d, c, b, f, x}, e), q)
    case Lp.St{Lp.Judging{}, i, l, d, c, b, f, x} _:
      lh.absurd_ft(lh.QuietStep(Lp.St{Lp.Judging{}, i, l, d, c, b, f, x}, e), q)
    case Lp.St{Lp.Off{}, i, l, d, c, b, f, x} Lp.Stop{}:
      {==}
    case Lp.St{Lp.Off{}, i, l, d, c, b, f, x} Lp.Abort{}:
      {==}
    case Lp.St{Lp.Off{}, i, l, d, c, b, f, x} Lp.Settled{k, out, blocked, now, funded}:
      {==}
    case Lp.St{Lp.Off{}, i, l, d, c, b, f, x} Lp.Judged{k, ev, blocked, now, funded}:
      {==}
    case Lp.St{Lp.Off{}, i, l, d, c, b, f, x} Lp.Restart{}:
      {==}
    case Lp.St{Lp.Paused{}, i, l, d, c, b, f, x} Lp.Stop{}:
      {==}
    case Lp.St{Lp.Paused{}, i, l, d, c, b, f, x} Lp.Abort{}:
      {==}
    case Lp.St{Lp.Paused{}, i, l, d, c, b, f, x} Lp.Settled{k, out, blocked, now, funded}:
      {==}
    case Lp.St{Lp.Paused{}, i, l, d, c, b, f, x} Lp.Judged{k, ev, blocked, now, funded}:
      {==}
    case Lp.St{Lp.Paused{}, i, l, d, c, b, f, x} Lp.Restart{}:
      {==}
    case Lp.St{Lp.Ended{w}, i, l, d, c, b, f, x} Lp.Stop{}:
      {==}
    case Lp.St{Lp.Ended{w}, i, l, d, c, b, f, x} Lp.Abort{}:
      {==}
    case Lp.St{Lp.Ended{w}, i, l, d, c, b, f, x} Lp.Settled{k, out, blocked, now, funded}:
      {==}
    case Lp.St{Lp.Ended{w}, i, l, d, c, b, f, x} Lp.Judged{k, ev, blocked, now, funded}:
      {==}
    case Lp.St{Lp.Ended{w}, i, l, d, c, b, f, x} Lp.Restart{}:
      {==}

def lh.quiet_hist(h: List<&2, Lp.Ev>, +s: Lp.St, q: {lh.quiet(S.phase(s)) == True{} : Bool}, u: {S.unattended(h) == True{} : Bool}) -> {S.none_starts(S.acts(h, s)) == True{} : Bool}:
  match h:
    case Nil{}:
      {==}
    case Con{+e, t}:
      +uu = u
      +st = lh.quiet_step(s, e, q, lh.and_l(Bool.not(S.is_user(e)), S.unattended(t), uu))
      lh.and_tt(Bool.not(S.starts(S.does(s, e))), S.none_starts(S.acts(t, S.next(s, e))),
        lh.and_l(Bool.not(S.starts(S.does(s, e))), lh.quiet(S.phase(S.next(s, e))), st),
        lh.quiet_hist(t, S.next(s, e), lh.and_r(Bool.not(S.starts(S.does(s, e))), lh.quiet(S.phase(S.next(s, e))), st), lh.and_r(Bool.not(S.is_user(e)), S.unattended(t), uu)))

# the interrupt starts nothing and leaves a quiet state
def lh.abort_first(s: Lp.St) -> {Bool.and(Bool.not(S.starts(S.does(s, Lp.Abort{}))), lh.quiet(S.phase(S.next(s, Lp.Abort{})))) == True{} : Bool}:
  match s:
    case Lp.St{Lp.Off{}, i, l, d, c, b, f, x}:
      {==}
    case Lp.St{Lp.Armed{}, i, l, d, c, b, f, x}:
      {==}
    case Lp.St{Lp.Turn{}, i, l, d, c, b, f, x}:
      {==}
    case Lp.St{Lp.Judging{}, i, l, d, c, b, f, x}:
      {==}
    case Lp.St{Lp.Paused{}, i, l, d, c, b, f, x}:
      {==}
    case Lp.St{Lp.Ended{w}, i, l, d, c, b, f, x}:
      {==}

def lh.abort_hist(+s: Lp.St, h: List<&2, Lp.Ev>, u: {S.unattended(h) == True{} : Bool}) -> {S.none_starts(S.acts(Lp.Abort{} <> h, s)) == True{} : Bool}:
  +st = lh.abort_first(s)
  lh.and_tt(Bool.not(S.starts(S.does(s, Lp.Abort{}))), S.none_starts(S.acts(h, S.next(s, Lp.Abort{}))),
    lh.and_l(Bool.not(S.starts(S.does(s, Lp.Abort{}))), lh.quiet(S.phase(S.next(s, Lp.Abort{}))), st),
    lh.quiet_hist(h, S.next(s, Lp.Abort{}), lh.and_r(Bool.not(S.starts(S.does(s, Lp.Abort{}))), lh.quiet(S.phase(S.next(s, Lp.Abort{}))), st), u))

# ---- the view: what an unattended event keeps ----

type LhView is Data:
  LhView{cond: Lp.Cond, dl: Maybe<&2, Nat>, left: Maybe<&2, Nat>, rep: Bool, body: String, text: String}

def lh.v_cond(v: LhView) -> Lp.Cond:
  match v:
    case LhView{c, d, l, r, k, t}:
      c

def lh.v_dl(v: LhView) -> Maybe<&2, Nat>:
  match v:
    case LhView{c, d, l, r, k, t}:
      d

def lh.v_left(v: LhView) -> Maybe<&2, Nat>:
  match v:
    case LhView{c, d, l, r, k, t}:
      l

def lh.v_rep(v: LhView) -> Bool:
  match v:
    case LhView{c, d, l, r, k, t}:
      r

def lh.v_body(v: LhView) -> String:
  match v:
    case LhView{c, d, l, r, k, t}:
      k

def lh.v_text(v: LhView) -> String:
  match v:
    case LhView{c, d, l, r, k, t}:
      t

def lh.bump.one(l: Maybe<&2, Nat>) -> Maybe<&2, Nat>:
  match l:
    case None{}:
      None{}
    case Some{n}:
      Some{1n+n}

# the count before an act: one more if the act started an iteration
def lh.bump(sb: Bool, l: Maybe<&2, Nat>) -> Maybe<&2, Nat>:
  match sb:
    case True{}:
      lh.bump.one(l)
    case False{}:
      l

# the prompt after a step (b2), unless the state is quiet: then b
def lh.keep(q: Bool, b2: String, b: String) -> String:
  match q:
    case True{}:
      b
    case False{}:
      b2

# the text an act sends, or b if it sends none
def lh.text(a: Lp.Act, b: String) -> String:
  match a:
    case Lp.Rest{}:
      b
    case Lp.Submit{i, t}:
      t
    case Lp.Adopt{i}:
      b
    case Lp.Judge{i}:
      b
    case Lp.Resume{i, t}:
      t
    case Lp.Report{w}:
      b
    case Lp.Defer{}:
      b

# a report, plus one if the loop is on after it, is at most one if the
# loop was on (on), else none
def lh.rep(a: Lp.Act, p2: Lp.Phase, on: Bool) -> Bool:
  Nat.is_le(Nat.add(S.one_if(S.is_report(a)), S.one_if(S.is_on(p2))), S.one_if(on))

def lh.view(+s2: Lp.St, +a: Lp.Act, on: Bool, +b: String) -> LhView:
  LhView{S.cond(s2), S.deadline(s2), lh.bump(S.is_submit(a), S.left(s2)), lh.rep(a, S.phase(s2), on), lh.keep(lh.quiet(S.phase(s2)), S.body(s2), b), lh.text(a, b)}

# the step r, from a state with condition c, deadline d, count l and
# prompt b (on: the loop was on), keeps the condition, the deadline and
# the count less the iteration it starts, reports once at most, keeps the
# prompt unless it leaves a quiet state, and sends no other text
def lh.ViewOk(r: Lp.St & Lp.Act, on: Bool, c: Lp.Cond, d: Maybe<&2, Nat>, l: Maybe<&2, Nat>, +b: String) -> Type:
  {lh.view(S.state(r), S.act(r), on, b) == LhView{c, d, l, True{}, b, b} : LhView}

def lh.ViewStep(+s: Lp.St, e: Lp.Ev) -> Type:
  lh.ViewOk(Lp.step(s, e), S.is_on(S.phase(s)), S.cond(s), S.deadline(s), S.left(s), S.body(s))

def lh.view_adv(h: Maybe<&2, Lp.End>, l: Maybe<&2, Nat>, -i: Nat, -d: Maybe<&2, Nat>, -c: Lp.Cond, -b: String, -f: Nat, -x: Lp.Last, sp: {lh.none_if(Lp.spent(l), h) == False{} : Bool}) -> lh.ViewOk(Lp.advance.on(h, i, l, d, c, b, f, x), True{}, c, d, l, b):
  match h l:
    case Some{why} _:
      {==}
    case None{} None{}:
      {==}
    case None{} Some{0n}:
      lh.absurd_tf(lh.ViewOk(Lp.advance.on(None{}, i, Some{0n}, d, c, b, f, x), True{}, c, d, Some{0n}, b), sp)
    case None{} Some{1n+m}:
      {==}

def lh.view_settled(m: Bool, blocked: Bool, out: Lp.Out, c: Lp.Cond, -i: Nat, +l: Maybe<&2, Nat>, +d: Maybe<&2, Nat>, -b: String, +f: Nat, -x: Lp.Last, +now: Nat, +funded: Bool) -> lh.ViewOk(Lp.settled(m, Lp.Turn{}, i, l, d, c, b, f, x, out, blocked, now, funded), True{}, c, d, l, b):
  match m blocked out c:
    case False{} _ _ _:
      {==}
    case True{} True{} _ _:
      {==}
    case True{} False{} Lp.Halted{} _:
      {==}
    case True{} False{} Lp.Ran{} Lp.NoCond{}:
      lh.view_adv(Lp.halt(0n, funded, l, d, now), l, i, d, Lp.NoCond{}, b, 0n, x, lh.halt_spent(Lp.spent(l), Lp.tired(0n), funded, Lp.late(d, now)))
    case True{} False{} Lp.Ran{} Lp.Until{cmd}:
      {==}
    case True{} False{} Lp.Ran{} Lp.While{cmd}:
      {==}
    case True{} False{} Lp.Errored{} Lp.NoCond{}:
      lh.view_adv(Lp.halt(1n+f, funded, l, d, now), l, i, d, Lp.NoCond{}, b, 1n+f, x, lh.halt_spent(Lp.spent(l), Lp.tired(1n+f), funded, Lp.late(d, now)))
    case True{} False{} Lp.Errored{} Lp.Until{cmd}:
      {==}
    case True{} False{} Lp.Errored{} Lp.While{cmd}:
      {==}

def lh.view_verdict(v: Lp.Verdict, -i: Nat, +l: Maybe<&2, Nat>, +d: Maybe<&2, Nat>, -c: Lp.Cond, -b: String, +f: Nat, -x: Lp.Last, -ev: Lp.Evid, +now: Nat, +funded: Bool) -> lh.ViewOk(Lp.judged.verdict(v, i, l, d, c, b, f, x, ev, now, funded), True{}, c, d, l, b):
  match v:
    case Lp.Confirmed{}:
      {==}
    case Lp.Refuted{}:
      lh.view_adv(Lp.halt(f, funded, l, d, now), l, i, d, c, b, f, Lp.Check{i, ev}, lh.halt_spent(Lp.spent(l), Lp.tired(f), funded, Lp.late(d, now)))
    case Lp.Broken{}:
      {==}
    case Lp.Unjudged{}:
      {==}

def lh.view_judged(m: Bool, blocked: Bool, c: Lp.Cond, -i: Nat, +l: Maybe<&2, Nat>, +d: Maybe<&2, Nat>, -b: String, +f: Nat, -x: Lp.Last, ev: Lp.Evid, +now: Nat, +funded: Bool) -> lh.ViewOk(Lp.judged(m, Lp.Judging{}, i, l, d, c, b, f, x, ev, blocked, now, funded), True{}, c, d, l, b):
  match m blocked c:
    case False{} _ _:
      {==}
    case True{} True{} _:
      {==}
    case True{} False{} Lp.NoCond{}:
      lh.view_adv(Lp.halt(f, funded, l, d, now), l, i, d, Lp.NoCond{}, b, f, x, lh.halt_spent(Lp.spent(l), Lp.tired(f), funded, Lp.late(d, now)))
    case True{} False{} Lp.Until{cmd}:
      lh.view_verdict(Lp.judge(True{}, ev), i, l, d, Lp.Until{cmd}, b, f, x, ev, now, funded)
    case True{} False{} Lp.While{cmd}:
      lh.view_verdict(Lp.judge(False{}, ev), i, l, d, Lp.While{cmd}, b, f, x, ev, now, funded)

def lh.view_step(s: Lp.St, e: Lp.Ev, u: {Bool.not(S.is_user(e)) == True{} : Bool}) -> lh.ViewStep(s, e):
  match s e:
    case Lp.St{p, i, l, d, c, b, f, x} Lp.Enter{lim, c2, pr, now}:
      lh.absurd_ft(lh.ViewStep(Lp.St{p, i, l, d, c, b, f, x}, Lp.Enter{lim, c2, pr, now}), u)
    case Lp.St{p, i, l, d, c, b, f, x} Lp.Prompt{t}:
      lh.absurd_ft(lh.ViewStep(Lp.St{p, i, l, d, c, b, f, x}, Lp.Prompt{t}), u)
    case Lp.St{Lp.Off{}, i, l, d, c, b, f, x} Lp.Stop{}:
      {==}
    case Lp.St{Lp.Off{}, i, l, d, c, b, f, x} Lp.Abort{}:
      {==}
    case Lp.St{Lp.Off{}, i, l, d, c, b, f, x} Lp.Settled{k, out, blocked, now, funded}:
      {==}
    case Lp.St{Lp.Off{}, i, l, d, c, b, f, x} Lp.Judged{k, ev, blocked, now, funded}:
      {==}
    case Lp.St{Lp.Off{}, i, l, d, c, b, f, x} Lp.Restart{}:
      {==}
    case Lp.St{Lp.Armed{}, i, l, d, c, b, f, x} Lp.Stop{}:
      {==}
    case Lp.St{Lp.Armed{}, i, l, d, c, b, f, x} Lp.Abort{}:
      {==}
    case Lp.St{Lp.Armed{}, i, l, d, c, b, f, x} Lp.Settled{k, out, blocked, now, funded}:
      {==}
    case Lp.St{Lp.Armed{}, i, l, d, c, b, f, x} Lp.Judged{k, ev, blocked, now, funded}:
      {==}
    case Lp.St{Lp.Armed{}, i, l, d, c, b, f, x} Lp.Restart{}:
      {==}
    case Lp.St{Lp.Turn{}, i, l, d, c, b, f, x} Lp.Stop{}:
      {==}
    case Lp.St{Lp.Turn{}, i, l, d, c, b, f, x} Lp.Abort{}:
      {==}
    case Lp.St{Lp.Turn{}, i, l, d, c, b, f, x} Lp.Settled{k, out, blocked, now, funded}:
      lh.view_settled(Nat.is_eq(k, i), blocked, out, c, i, l, d, b, f, x, now, funded)
    case Lp.St{Lp.Turn{}, i, l, d, c, b, f, x} Lp.Judged{k, ev, blocked, now, funded}:
      {==}
    case Lp.St{Lp.Turn{}, i, l, d, c, b, f, x} Lp.Restart{}:
      {==}
    case Lp.St{Lp.Judging{}, i, l, d, c, b, f, x} Lp.Stop{}:
      {==}
    case Lp.St{Lp.Judging{}, i, l, d, c, b, f, x} Lp.Abort{}:
      {==}
    case Lp.St{Lp.Judging{}, i, l, d, c, b, f, x} Lp.Settled{k, out, blocked, now, funded}:
      {==}
    case Lp.St{Lp.Judging{}, i, l, d, c, b, f, x} Lp.Judged{k, ev, blocked, now, funded}:
      lh.view_judged(Nat.is_eq(k, i), blocked, c, i, l, d, b, f, x, ev, now, funded)
    case Lp.St{Lp.Judging{}, i, l, d, c, b, f, x} Lp.Restart{}:
      {==}
    case Lp.St{Lp.Paused{}, i, l, d, c, b, f, x} Lp.Stop{}:
      {==}
    case Lp.St{Lp.Paused{}, i, l, d, c, b, f, x} Lp.Abort{}:
      {==}
    case Lp.St{Lp.Paused{}, i, l, d, c, b, f, x} Lp.Settled{k, out, blocked, now, funded}:
      {==}
    case Lp.St{Lp.Paused{}, i, l, d, c, b, f, x} Lp.Judged{k, ev, blocked, now, funded}:
      {==}
    case Lp.St{Lp.Paused{}, i, l, d, c, b, f, x} Lp.Restart{}:
      {==}
    case Lp.St{Lp.Ended{w}, i, l, d, c, b, f, x} Lp.Stop{}:
      {==}
    case Lp.St{Lp.Ended{w}, i, l, d, c, b, f, x} Lp.Abort{}:
      {==}
    case Lp.St{Lp.Ended{w}, i, l, d, c, b, f, x} Lp.Settled{k, out, blocked, now, funded}:
      {==}
    case Lp.St{Lp.Ended{w}, i, l, d, c, b, f, x} Lp.Judged{k, ev, blocked, now, funded}:
      {==}
    case Lp.St{Lp.Ended{w}, i, l, d, c, b, f, x} Lp.Restart{}:
      {==}

# an unattended event keeps the condition
def lh.cond_un(+s: Lp.St, +e: Lp.Ev, u: {Bool.not(S.is_user(e)) == True{} : Bool}) -> {S.cond(S.next(s, e)) == S.cond(s) : Lp.Cond}:
  Equal.cong(LhView, Lp.Cond, v => lh.v_cond(v), lh.view(S.next(s, e), S.does(s, e), S.is_on(S.phase(s)), S.body(s)), LhView{S.cond(s), S.deadline(s), S.left(s), True{}, S.body(s), S.body(s)}, lh.view_step(s, e, u))

# an unattended event keeps the deadline
def lh.dl_un(+s: Lp.St, +e: Lp.Ev, u: {Bool.not(S.is_user(e)) == True{} : Bool}) -> {S.deadline(S.next(s, e)) == S.deadline(s) : Maybe<&2, Nat>}:
  Equal.cong(LhView, Maybe<&2, Nat>, v => lh.v_dl(v), lh.view(S.next(s, e), S.does(s, e), S.is_on(S.phase(s)), S.body(s)), LhView{S.cond(s), S.deadline(s), S.left(s), True{}, S.body(s), S.body(s)}, lh.view_step(s, e, u))

# the count after an unattended event, and one more if it started an
# iteration, is the count before it
def lh.left_un(+s: Lp.St, +e: Lp.Ev, u: {Bool.not(S.is_user(e)) == True{} : Bool}) -> {lh.bump(S.is_submit(S.does(s, e)), S.left(S.next(s, e))) == S.left(s) : Maybe<&2, Nat>}:
  Equal.cong(LhView, Maybe<&2, Nat>, v => lh.v_left(v), lh.view(S.next(s, e), S.does(s, e), S.is_on(S.phase(s)), S.body(s)), LhView{S.cond(s), S.deadline(s), S.left(s), True{}, S.body(s), S.body(s)}, lh.view_step(s, e, u))

def lh.RepStep(+s: Lp.St, +e: Lp.Ev) -> Type:
  {lh.rep(S.does(s, e), S.phase(S.next(s, e)), S.is_on(S.phase(s))) == True{} : Bool}

def lh.rep_un(+s: Lp.St, +e: Lp.Ev, u: {Bool.not(S.is_user(e)) == True{} : Bool}) -> lh.RepStep(s, e):
  Equal.cong(LhView, Bool, v => lh.v_rep(v), lh.view(S.next(s, e), S.does(s, e), S.is_on(S.phase(s)), S.body(s)), LhView{S.cond(s), S.deadline(s), S.left(s), True{}, S.body(s), S.body(s)}, lh.view_step(s, e, u))

# an unattended event keeps the prompt, unless it leaves a quiet state
def lh.keep_un(+s: Lp.St, +e: Lp.Ev, u: {Bool.not(S.is_user(e)) == True{} : Bool}) -> {lh.keep(lh.quiet(S.phase(S.next(s, e))), S.body(S.next(s, e)), S.body(s)) == S.body(s) : String}:
  Equal.cong(LhView, String, v => lh.v_body(v), lh.view(S.next(s, e), S.does(s, e), S.is_on(S.phase(s)), S.body(s)), LhView{S.cond(s), S.deadline(s), S.left(s), True{}, S.body(s), S.body(s)}, lh.view_step(s, e, u))

# the text sent at an unattended event is the prompt
def lh.text_un(+s: Lp.St, +e: Lp.Ev, u: {Bool.not(S.is_user(e)) == True{} : Bool}) -> {lh.text(S.does(s, e), S.body(s)) == S.body(s) : String}:
  Equal.cong(LhView, String, v => lh.v_text(v), lh.view(S.next(s, e), S.does(s, e), S.is_on(S.phase(s)), S.body(s)), LhView{S.cond(s), S.deadline(s), S.left(s), True{}, S.body(s), S.body(s)}, lh.view_step(s, e, u))

# ---- the condition is kept ----

def lh.cond_prompt(s: Lp.St, -t: String) -> {S.cond(S.next(s, Lp.Prompt{t})) == S.cond(s) : Lp.Cond}:
  match s:
    case Lp.St{Lp.Off{}, i, l, d, c, b, f, x}:
      {==}
    case Lp.St{Lp.Armed{}, i, l, d, c, b, f, x}:
      {==}
    case Lp.St{Lp.Turn{}, i, l, d, c, b, f, x}:
      {==}
    case Lp.St{Lp.Judging{}, i, l, d, c, b, f, x}:
      {==}
    case Lp.St{Lp.Paused{}, i, l, d, c, b, f, x}:
      {==}
    case Lp.St{Lp.Ended{w}, i, l, d, c, b, f, x}:
      {==}

# every event but Enter keeps the condition
def lh.cond_step(+s: Lp.St, e: Lp.Ev, ne: {Bool.not(S.is_enter(e)) == True{} : Bool}) -> {S.cond(S.next(s, e)) == S.cond(s) : Lp.Cond}:
  match e:
    case Lp.Enter{lim, c2, pr, now}:
      lh.absurd_ft({S.cond(S.next(s, Lp.Enter{lim, c2, pr, now})) == S.cond(s) : Lp.Cond}, ne)
    case Lp.Stop{}:
      lh.cond_un(s, Lp.Stop{}, {==})
    case Lp.Abort{}:
      lh.cond_un(s, Lp.Abort{}, {==})
    case Lp.Prompt{t}:
      lh.cond_prompt(s, t)
    case Lp.Settled{k, out, blocked, now, funded}:
      lh.cond_un(s, Lp.Settled{k, out, blocked, now, funded}, {==})
    case Lp.Judged{k, ev, blocked, now, funded}:
      lh.cond_un(s, Lp.Judged{k, ev, blocked, now, funded}, {==})
    case Lp.Restart{}:
      lh.cond_un(s, Lp.Restart{}, {==})

def lh.cond_hist(h: List<&2, Lp.Ev>, +s: Lp.St, ne: {S.no_enter(h) == True{} : Bool}) -> {S.cond(S.after(h, s)) == S.cond(s) : Lp.Cond}:
  match h:
    case Nil{}:
      {==}
    case Con{+e, t}:
      +nn = ne
      Equal.trans(Lp.Cond, S.cond(S.after(t, S.next(s, e))), S.cond(S.next(s, e)), S.cond(s),
        lh.cond_hist(t, S.next(s, e), lh.and_r(Bool.not(S.is_enter(e)), S.no_enter(t), nn)),
        lh.cond_step(s, e, lh.and_l(Bool.not(S.is_enter(e)), S.no_enter(t), nn)))

# ---- the deadline is kept ----

def lh.dl_prompt(s: Lp.St, -t: String) -> {S.deadline(S.next(s, Lp.Prompt{t})) == S.deadline(s) : Maybe<&2, Nat>}:
  match s:
    case Lp.St{Lp.Off{}, i, l, d, c, b, f, x}:
      {==}
    case Lp.St{Lp.Armed{}, i, l, d, c, b, f, x}:
      {==}
    case Lp.St{Lp.Turn{}, i, l, d, c, b, f, x}:
      {==}
    case Lp.St{Lp.Judging{}, i, l, d, c, b, f, x}:
      {==}
    case Lp.St{Lp.Paused{}, i, l, d, c, b, f, x}:
      {==}
    case Lp.St{Lp.Ended{w}, i, l, d, c, b, f, x}:
      {==}

# every event but Enter keeps the deadline
def lh.dl_step(+s: Lp.St, e: Lp.Ev, ne: {Bool.not(S.is_enter(e)) == True{} : Bool}) -> {S.deadline(S.next(s, e)) == S.deadline(s) : Maybe<&2, Nat>}:
  match e:
    case Lp.Enter{lim, c2, pr, now}:
      lh.absurd_ft({S.deadline(S.next(s, Lp.Enter{lim, c2, pr, now})) == S.deadline(s) : Maybe<&2, Nat>}, ne)
    case Lp.Stop{}:
      lh.dl_un(s, Lp.Stop{}, {==})
    case Lp.Abort{}:
      lh.dl_un(s, Lp.Abort{}, {==})
    case Lp.Prompt{t}:
      lh.dl_prompt(s, t)
    case Lp.Settled{k, out, blocked, now, funded}:
      lh.dl_un(s, Lp.Settled{k, out, blocked, now, funded}, {==})
    case Lp.Judged{k, ev, blocked, now, funded}:
      lh.dl_un(s, Lp.Judged{k, ev, blocked, now, funded}, {==})
    case Lp.Restart{}:
      lh.dl_un(s, Lp.Restart{}, {==})

def lh.dl_hist(h: List<&2, Lp.Ev>, +s: Lp.St, ne: {S.no_enter(h) == True{} : Bool}) -> {S.deadline(S.after(h, s)) == S.deadline(s) : Maybe<&2, Nat>}:
  match h:
    case Nil{}:
      {==}
    case Con{+e, t}:
      +nn = ne
      Equal.trans(Maybe<&2, Nat>, S.deadline(S.after(t, S.next(s, e))), S.deadline(S.next(s, e)), S.deadline(s),
        lh.dl_hist(t, S.next(s, e), lh.and_r(Bool.not(S.is_enter(e)), S.no_enter(t), nn)),
        lh.dl_step(s, e, lh.and_l(Bool.not(S.is_enter(e)), S.no_enter(t), nn)))

# ---- one report ----

def lh.rep_prompt(s: Lp.St, -t: String) -> lh.RepStep(s, Lp.Prompt{t}):
  match s:
    case Lp.St{Lp.Off{}, i, l, d, c, b, f, x}:
      {==}
    case Lp.St{Lp.Armed{}, i, l, d, c, b, f, x}:
      {==}
    case Lp.St{Lp.Turn{}, i, l, d, c, b, f, x}:
      {==}
    case Lp.St{Lp.Judging{}, i, l, d, c, b, f, x}:
      {==}
    case Lp.St{Lp.Paused{}, i, l, d, c, b, f, x}:
      {==}
    case Lp.St{Lp.Ended{w}, i, l, d, c, b, f, x}:
      {==}

# at every event but Enter: a report ends the loop, and no loop starts
def lh.rep_step(+s: Lp.St, e: Lp.Ev, ne: {Bool.not(S.is_enter(e)) == True{} : Bool}) -> lh.RepStep(s, e):
  match e:
    case Lp.Enter{lim, c2, pr, now}:
      lh.absurd_ft(lh.RepStep(s, Lp.Enter{lim, c2, pr, now}), ne)
    case Lp.Stop{}:
      lh.rep_un(s, Lp.Stop{}, {==})
    case Lp.Abort{}:
      lh.rep_un(s, Lp.Abort{}, {==})
    case Lp.Prompt{t}:
      lh.rep_prompt(s, t)
    case Lp.Settled{k, out, blocked, now, funded}:
      lh.rep_un(s, Lp.Settled{k, out, blocked, now, funded}, {==})
    case Lp.Judged{k, ev, blocked, now, funded}:
      lh.rep_un(s, Lp.Judged{k, ev, blocked, now, funded}, {==})
    case Lp.Restart{}:
      lh.rep_un(s, Lp.Restart{}, {==})

# the reports are at most one from a loop that is on, none from one that
# is off
def lh.rep_hist(h: List<&2, Lp.Ev>, +s: Lp.St, ne: {S.no_enter(h) == True{} : Bool}) -> {Nat.is_le(S.reports(S.acts(h, s)), S.one_if(S.is_on(S.phase(s)))) == True{} : Bool}:
  match h:
    case Nil{}:
      lh.le_zero(S.one_if(S.is_on(S.phase(s))))
    case Con{+e, +t}:
      +nn = ne
      lh.le_bump(S.is_report(S.does(s, e)), S.reports(S.acts(t, S.next(s, e))), S.one_if(S.is_on(S.phase(S.next(s, e)))), S.one_if(S.is_on(S.phase(s))),
        lh.rep_hist(t, S.next(s, e), lh.and_r(Bool.not(S.is_enter(e)), S.no_enter(t), nn)),
        lh.rep_step(s, e, lh.and_l(Bool.not(S.is_enter(e)), S.no_enter(t), nn)))

# ---- the count ----

# k iterations fit in the count l
def lh.fits(k: Nat, l: Maybe<&2, Nat>) -> Bool:
  match l:
    case None{}:
      True{}
    case Some{n}:
      Nat.is_le(k, n)

def lh.fits_zero(l: Maybe<&2, Nat>) -> {lh.fits(0n, l) == True{} : Bool}:
  match l:
    case None{}:
      {==}
    case Some{n}:
      lh.le_zero(n)

def lh.fits_bump(sb: Bool, l: Maybe<&2, Nat>, -x: Nat, ih: {lh.fits(x, l) == True{} : Bool}) -> {lh.fits(Nat.add(S.one_if(sb), x), lh.bump(sb, l)) == True{} : Bool}:
  match sb l:
    case False{} _:
      ih
    case True{} None{}:
      {==}
    case True{} Some{n}:
      ih

# the automatic iterations of an unattended history fit in the count
def lh.cnt_hist(h: List<&2, Lp.Ev>, +s: Lp.St, u: {S.unattended(h) == True{} : Bool}) -> {lh.fits(S.submits(S.acts(h, s)), S.left(s)) == True{} : Bool}:
  match h:
    case Nil{}:
      lh.fits_zero(S.left(s))
    case Con{+e, +t}:
      +uu = u
      %lh.left_un(s, e, lh.and_l(Bool.not(S.is_user(e)), S.unattended(t), uu)) : {lh.fits(Nat.add(S.one_if(S.is_submit(S.does(s, e))), S.submits(S.acts(t, S.next(s, e)))), _) == True{} : Bool}
      lh.fits_bump(S.is_submit(S.does(s, e)), S.left(S.next(s, e)), S.submits(S.acts(t, S.next(s, e))), lh.cnt_hist(t, S.next(s, e), lh.and_r(Bool.not(S.is_user(e)), S.unattended(t), uu)))

# ---- the count is conserved ----

# the count l less k iterations
def lh.spend(k: Nat, l: Maybe<&2, Nat>) -> Maybe<&2, Nat>:
  match l:
    case None{}:
      None{}
    case Some{n}:
      Some{Nat.sub(n, k)}

def lh.spend_zero(l: Maybe<&2, Nat>) -> {l == lh.spend(0n, l) : Maybe<&2, Nat>}:
  match l:
    case None{}:
      {==}
    case Some{0n}:
      {==}
    case Some{1n+p}:
      {==}

# an iteration started (sb) spends one of the count it was started from
def lh.spend_bump(sb: Bool, l: Maybe<&2, Nat>, -x: Nat) -> {lh.spend(x, l) == lh.spend(Nat.add(S.one_if(sb), x), lh.bump(sb, l)) : Maybe<&2, Nat>}:
  match sb l:
    case False{} _:
      {==}
    case True{} None{}:
      {==}
    case True{} Some{m}:
      {==}

def lh.left_prompt(s: Lp.St, -t: String) -> {lh.bump(S.is_submit(S.does(s, Lp.Prompt{t})), S.left(S.next(s, Lp.Prompt{t}))) == S.left(s) : Maybe<&2, Nat>}:
  match s:
    case Lp.St{Lp.Off{}, i, l, d, c, b, f, x}:
      {==}
    case Lp.St{Lp.Armed{}, i, l, d, c, b, f, x}:
      {==}
    case Lp.St{Lp.Turn{}, i, l, d, c, b, f, x}:
      {==}
    case Lp.St{Lp.Judging{}, i, l, d, c, b, f, x}:
      {==}
    case Lp.St{Lp.Paused{}, i, l, d, c, b, f, x}:
      {==}
    case Lp.St{Lp.Ended{w}, i, l, d, c, b, f, x}:
      {==}

# at every event but Enter: the count after it, and one more if it started
# an iteration, is the count before it
def lh.left_step(+s: Lp.St, e: Lp.Ev, ne: {Bool.not(S.is_enter(e)) == True{} : Bool}) -> {lh.bump(S.is_submit(S.does(s, e)), S.left(S.next(s, e))) == S.left(s) : Maybe<&2, Nat>}:
  match e:
    case Lp.Enter{lim, c2, pr, now}:
      lh.absurd_ft({lh.bump(S.is_submit(S.does(s, Lp.Enter{lim, c2, pr, now})), S.left(S.next(s, Lp.Enter{lim, c2, pr, now}))) == S.left(s) : Maybe<&2, Nat>}, ne)
    case Lp.Stop{}:
      lh.left_un(s, Lp.Stop{}, {==})
    case Lp.Abort{}:
      lh.left_un(s, Lp.Abort{}, {==})
    case Lp.Prompt{t}:
      lh.left_prompt(s, t)
    case Lp.Settled{k, out, blocked, now, funded}:
      lh.left_un(s, Lp.Settled{k, out, blocked, now, funded}, {==})
    case Lp.Judged{k, ev, blocked, now, funded}:
      lh.left_un(s, Lp.Judged{k, ev, blocked, now, funded}, {==})
    case Lp.Restart{}:
      lh.left_un(s, Lp.Restart{}, {==})

# the count after a history with no Enter is the count before it less the
# automatic iterations started (none: no count)
def lh.left_hist(h: List<&2, Lp.Ev>, +s: Lp.St, ne: {S.no_enter(h) == True{} : Bool}) -> {S.left(S.after(h, s)) == lh.spend(S.submits(S.acts(h, s)), S.left(s)) : Maybe<&2, Nat>}:
  match h:
    case Nil{}:
      lh.spend_zero(S.left(s))
    case Con{+e, +t}:
      +nn = ne
      %lh.left_step(s, e, lh.and_l(Bool.not(S.is_enter(e)), S.no_enter(t), nn)) : {S.left(S.after(t, S.next(s, e))) == lh.spend(Nat.add(S.one_if(S.is_submit(S.does(s, e))), S.submits(S.acts(t, S.next(s, e)))), _) : Maybe<&2, Nat>}
      Equal.trans(Maybe<&2, Nat>, S.left(S.after(t, S.next(s, e))), lh.spend(S.submits(S.acts(t, S.next(s, e))), S.left(S.next(s, e))), lh.spend(Nat.add(S.one_if(S.is_submit(S.does(s, e))), S.submits(S.acts(t, S.next(s, e)))), lh.bump(S.is_submit(S.does(s, e)), S.left(S.next(s, e)))),
        lh.left_hist(t, S.next(s, e), lh.and_r(Bool.not(S.is_enter(e)), S.no_enter(t), nn)),
        lh.spend_bump(S.is_submit(S.does(s, e)), S.left(S.next(s, e)), S.submits(S.acts(t, S.next(s, e)))))

# ---- the texts ----

def lh.text_is(a: Lp.Act, -b: String, eq: {lh.text(a, b) == b : String}) -> S.TextIs(a, b):
  match a:
    case Lp.Rest{}:
      Unit{}
    case Lp.Submit{i, t}:
      eq
    case Lp.Adopt{i}:
      Unit{}
    case Lp.Judge{i}:
      Unit{}
    case Lp.Resume{i, t}:
      eq
    case Lp.Report{w}:
      Unit{}
    case Lp.Defer{}:
      Unit{}

def lh.text_none(a: Lp.Act, -b: String, ns: {Bool.not(S.starts(a)) == True{} : Bool}) -> S.TextIs(a, b):
  match a:
    case Lp.Rest{}:
      Unit{}
    case Lp.Submit{i, t}:
      lh.absurd_ft({t == b : String}, ns)
    case Lp.Adopt{i}:
      Unit{}
    case Lp.Judge{i}:
      Unit{}
    case Lp.Resume{i, t}:
      lh.absurd_ft({t == b : String}, ns)
    case Lp.Report{w}:
      Unit{}
    case Lp.Defer{}:
      Unit{}

# acts that start nothing send no text
def lh.texts_any(xs: List<&2, Lp.Act>, -b: String, ns: {S.none_starts(xs) == True{} : Bool}) -> S.TextsAre(xs, b):
  match xs:
    case Nil{}:
      Unit{}
    case Con{+a, r}:
      +nn = ns
      (lh.text_none(a, b, lh.and_l(Bool.not(S.starts(a)), S.none_starts(r), nn)), lh.texts_any(r, b, lh.and_r(Bool.not(S.starts(a)), S.none_starts(r), nn)))

# the texts after a step: none from a quiet state (q), else those of the
# prompt the step kept
def lh.same_tail(q: Bool, +t: List<&2, Lp.Ev>, +s2: Lp.St, -b: String, eq: {lh.quiet(S.phase(s2)) == q : Bool}, u: {S.unattended(t) == True{} : Bool}, k: {lh.keep(q, S.body(s2), b) == b : String}, ih: S.TextsAre(S.acts(t, s2), S.body(s2))) -> S.TextsAre(S.acts(t, s2), b):
  match q:
    case True{}:
      lh.texts_any(S.acts(t, s2), b, lh.quiet_hist(t, s2, eq, u))
    case False{}:
      %k : S.TextsAre(S.acts(t, s2), _)
      ih

def lh.same_hist(h: List<&2, Lp.Ev>, +s: Lp.St, u: {S.unattended(h) == True{} : Bool}) -> S.TextsAre(S.acts(h, s), S.body(s)):
  match h:
    case Nil{}:
      Unit{}
    case Con{+e, +t}:
      +uu = u
      +ue = lh.and_l(Bool.not(S.is_user(e)), S.unattended(t), uu)
      +ut = lh.and_r(Bool.not(S.is_user(e)), S.unattended(t), uu)
      (lh.text_is(S.does(s, e), S.body(s), lh.text_un(s, e, ue)), lh.same_tail(lh.quiet(S.phase(S.next(s, e))), t, S.next(s, e), S.body(s), {==}, ut, lh.keep_un(s, e, ue), lh.same_hist(t, S.next(s, e), ut)))

# ---- a failing run ----

# the automatic iterations a run in which no turn runs to its end can
# still start, with f turns failed in a row: 3 - f while judging; one
# fewer in a turn (the turn must fail first); none otherwise
def lh.pot(p: Lp.Phase, f: Nat) -> Nat:
  match p:
    case Lp.Off{}:
      0n
    case Lp.Armed{}:
      0n
    case Lp.Turn{}:
      Nat.sub(2n, f)
    case Lp.Judging{}:
      Nat.sub(3n, f)
    case Lp.Paused{}:
      0n
    case Lp.Ended{w}:
      0n

def lh.cost(a: Lp.Act, +s2: Lp.St) -> Nat:
  Nat.add(S.one_if(S.is_submit(a)), lh.pot(S.phase(s2), S.fails(s2)))

def lh.PotLe(r: Lp.St & Lp.Act, q: Nat) -> Type:
  {Nat.is_le(lh.cost(S.act(r), S.state(r)), q) == True{} : Bool}

def lh.PotStep(+s: Lp.St, e: Lp.Ev) -> Type:
  lh.PotLe(Lp.step(s, e), lh.pot(S.phase(s), S.fails(s)))

def lh.pot_adv(h: Maybe<&2, Lp.End>, f: Nat, -i: Nat, -l: Maybe<&2, Nat>, -d: Maybe<&2, Nat>, -c: Lp.Cond, -b: String, -x: Lp.Last, nt: {lh.none_if(Lp.tired(f), h) == False{} : Bool}) -> lh.PotLe(Lp.advance.on(h, i, l, d, c, b, f, x), Nat.sub(3n, f)):
  match h f:
    case Some{why} _:
      lh.le_zero(Nat.sub(3n, f))
    case None{} 0n:
      {==}
    case None{} 1n:
      {==}
    case None{} 2n:
      {==}
    case None{} 3n+k:
      lh.absurd_tf(lh.PotLe(Lp.advance.on(None{}, i, l, d, c, b, 3n+k, x), Nat.sub(3n, 3n+k)), nt)

def lh.pot_settled(m: Bool, blocked: Bool, out: Lp.Out, c: Lp.Cond, +f: Nat, -i: Nat, +l: Maybe<&2, Nat>, +d: Maybe<&2, Nat>, -b: String, -x: Lp.Last, +now: Nat, +funded: Bool, nr: {Bool.not(S.out_ran(out)) == True{} : Bool}) -> lh.PotLe(Lp.settled(m, Lp.Turn{}, i, l, d, c, b, f, x, out, blocked, now, funded), Nat.sub(2n, f)):
  match m blocked out c:
    case False{} _ _ _:
      lh.le_refl(Nat.sub(2n, f))
    case True{} True{} _ _:
      lh.le_refl(Nat.sub(2n, f))
    case True{} False{} Lp.Halted{} _:
      lh.le_zero(Nat.sub(2n, f))
    case True{} False{} Lp.Ran{} _:
      lh.absurd_ft(lh.PotLe(Lp.settled(True{}, Lp.Turn{}, i, l, d, c, b, f, x, Lp.Ran{}, False{}, now, funded), Nat.sub(2n, f)), nr)
    case True{} False{} Lp.Errored{} Lp.NoCond{}:
      lh.pot_adv(Lp.halt(1n+f, funded, l, d, now), 1n+f, i, l, d, Lp.NoCond{}, b, x, lh.halt_tired(Lp.tired(1n+f), funded, Lp.spent(l), Lp.late(d, now)))
    case True{} False{} Lp.Errored{} Lp.Until{cmd}:
      lh.le_refl(Nat.sub(2n, f))
    case True{} False{} Lp.Errored{} Lp.While{cmd}:
      lh.le_refl(Nat.sub(2n, f))

def lh.pot_verdict(v: Lp.Verdict, +f: Nat, -i: Nat, +l: Maybe<&2, Nat>, +d: Maybe<&2, Nat>, -c: Lp.Cond, -b: String, -x: Lp.Last, -ev: Lp.Evid, +now: Nat, +funded: Bool) -> lh.PotLe(Lp.judged.verdict(v, i, l, d, c, b, f, x, ev, now, funded), Nat.sub(3n, f)):
  match v:
    case Lp.Confirmed{}:
      lh.le_zero(Nat.sub(3n, f))
    case Lp.Refuted{}:
      lh.pot_adv(Lp.halt(f, funded, l, d, now), f, i, l, d, c, b, Lp.Check{i, ev}, lh.halt_tired(Lp.tired(f), funded, Lp.spent(l), Lp.late(d, now)))
    case Lp.Broken{}:
      lh.le_zero(Nat.sub(3n, f))
    case Lp.Unjudged{}:
      lh.le_refl(Nat.sub(3n, f))

def lh.pot_judged(m: Bool, blocked: Bool, c: Lp.Cond, +f: Nat, -i: Nat, +l: Maybe<&2, Nat>, +d: Maybe<&2, Nat>, -b: String, -x: Lp.Last, ev: Lp.Evid, +now: Nat, +funded: Bool) -> lh.PotLe(Lp.judged(m, Lp.Judging{}, i, l, d, c, b, f, x, ev, blocked, now, funded), Nat.sub(3n, f)):
  match m blocked c:
    case False{} _ _:
      lh.le_refl(Nat.sub(3n, f))
    case True{} True{} _:
      lh.le_refl(Nat.sub(3n, f))
    case True{} False{} Lp.NoCond{}:
      lh.pot_adv(Lp.halt(f, funded, l, d, now), f, i, l, d, Lp.NoCond{}, b, x, lh.halt_tired(Lp.tired(f), funded, Lp.spent(l), Lp.late(d, now)))
    case True{} False{} Lp.Until{cmd}:
      lh.pot_verdict(Lp.judge(True{}, ev), f, i, l, d, Lp.Until{cmd}, b, x, ev, now, funded)
    case True{} False{} Lp.While{cmd}:
      lh.pot_verdict(Lp.judge(False{}, ev), f, i, l, d, Lp.While{cmd}, b, x, ev, now, funded)

# an unattended event that is no turn run to its end: the iteration it
# starts, and those still possible after it, were possible before it
def lh.pot_step(s: Lp.St, e: Lp.Ev, u: {Bool.not(S.is_user(e)) == True{} : Bool}, nr: {Bool.not(S.is_ran(e)) == True{} : Bool}) -> lh.PotStep(s, e):
  match s e:
    case Lp.St{p, i, l, d, c, b, f, x} Lp.Enter{lim, c2, pr, now}:
      lh.absurd_ft(lh.PotStep(Lp.St{p, i, l, d, c, b, f, x}, Lp.Enter{lim, c2, pr, now}), u)
    case Lp.St{p, i, l, d, c, b, f, x} Lp.Prompt{t}:
      lh.absurd_ft(lh.PotStep(Lp.St{p, i, l, d, c, b, f, x}, Lp.Prompt{t}), u)
    case Lp.St{Lp.Off{}, i, l, d, c, b, f, x} Lp.Stop{}:
      {==}
    case Lp.St{Lp.Off{}, i, l, d, c, b, f, x} Lp.Abort{}:
      {==}
    case Lp.St{Lp.Off{}, i, l, d, c, b, f, x} Lp.Settled{k, out, blocked, now, funded}:
      {==}
    case Lp.St{Lp.Off{}, i, l, d, c, b, f, x} Lp.Judged{k, ev, blocked, now, funded}:
      {==}
    case Lp.St{Lp.Off{}, i, l, d, c, b, f, x} Lp.Restart{}:
      {==}
    case Lp.St{Lp.Armed{}, i, l, d, c, b, f, x} Lp.Stop{}:
      {==}
    case Lp.St{Lp.Armed{}, i, l, d, c, b, f, x} Lp.Abort{}:
      {==}
    case Lp.St{Lp.Armed{}, i, l, d, c, b, f, x} Lp.Settled{k, out, blocked, now, funded}:
      {==}
    case Lp.St{Lp.Armed{}, i, l, d, c, b, f, x} Lp.Judged{k, ev, blocked, now, funded}:
      {==}
    case Lp.St{Lp.Armed{}, i, l, d, c, b, f, x} Lp.Restart{}:
      {==}
    case Lp.St{Lp.Turn{}, i, l, d, c, b, f, x} Lp.Stop{}:
      lh.le_zero(Nat.sub(2n, f))
    case Lp.St{Lp.Turn{}, i, l, d, c, b, f, x} Lp.Abort{}:
      lh.le_zero(Nat.sub(2n, f))
    case Lp.St{Lp.Turn{}, i, l, d, c, b, f, x} Lp.Settled{k, out, blocked, now, funded}:
      lh.pot_settled(Nat.is_eq(k, i), blocked, out, c, f, i, l, d, b, x, now, funded, nr)
    case Lp.St{Lp.Turn{}, i, l, d, c, b, f, x} Lp.Judged{k, ev, blocked, now, funded}:
      lh.le_refl(Nat.sub(2n, f))
    case Lp.St{Lp.Turn{}, i, l, d, c, b, f, x} Lp.Restart{}:
      lh.le_refl(Nat.sub(2n, f))
    case Lp.St{Lp.Judging{}, i, l, d, c, b, f, x} Lp.Stop{}:
      lh.le_zero(Nat.sub(3n, f))
    case Lp.St{Lp.Judging{}, i, l, d, c, b, f, x} Lp.Abort{}:
      lh.le_zero(Nat.sub(3n, f))
    case Lp.St{Lp.Judging{}, i, l, d, c, b, f, x} Lp.Settled{k, out, blocked, now, funded}:
      lh.le_refl(Nat.sub(3n, f))
    case Lp.St{Lp.Judging{}, i, l, d, c, b, f, x} Lp.Judged{k, ev, blocked, now, funded}:
      lh.pot_judged(Nat.is_eq(k, i), blocked, c, f, i, l, d, b, x, ev, now, funded)
    case Lp.St{Lp.Judging{}, i, l, d, c, b, f, x} Lp.Restart{}:
      lh.le_refl(Nat.sub(3n, f))
    case Lp.St{Lp.Paused{}, i, l, d, c, b, f, x} Lp.Stop{}:
      {==}
    case Lp.St{Lp.Paused{}, i, l, d, c, b, f, x} Lp.Abort{}:
      {==}
    case Lp.St{Lp.Paused{}, i, l, d, c, b, f, x} Lp.Settled{k, out, blocked, now, funded}:
      {==}
    case Lp.St{Lp.Paused{}, i, l, d, c, b, f, x} Lp.Judged{k, ev, blocked, now, funded}:
      {==}
    case Lp.St{Lp.Paused{}, i, l, d, c, b, f, x} Lp.Restart{}:
      {==}
    case Lp.St{Lp.Ended{w}, i, l, d, c, b, f, x} Lp.Stop{}:
      {==}
    case Lp.St{Lp.Ended{w}, i, l, d, c, b, f, x} Lp.Abort{}:
      {==}
    case Lp.St{Lp.Ended{w}, i, l, d, c, b, f, x} Lp.Settled{k, out, blocked, now, funded}:
      {==}
    case Lp.St{Lp.Ended{w}, i, l, d, c, b, f, x} Lp.Judged{k, ev, blocked, now, funded}:
      {==}
    case Lp.St{Lp.Ended{w}, i, l, d, c, b, f, x} Lp.Restart{}:
      {==}

def lh.fail_hist(h: List<&2, Lp.Ev>, +s: Lp.St, u: {S.unattended(h) == True{} : Bool}, nr: {S.none_ran(h) == True{} : Bool}) -> {Nat.is_le(S.submits(S.acts(h, s)), lh.pot(S.phase(s), S.fails(s))) == True{} : Bool}:
  match h:
    case Nil{}:
      lh.le_zero(lh.pot(S.phase(s), S.fails(s)))
    case Con{+e, +t}:
      +uu = u
      +nn = nr
      lh.le_bump(S.is_submit(S.does(s, e)), S.submits(S.acts(t, S.next(s, e))), lh.pot(S.phase(S.next(s, e)), S.fails(S.next(s, e))), lh.pot(S.phase(s), S.fails(s)),
        lh.fail_hist(t, S.next(s, e), lh.and_r(Bool.not(S.is_user(e)), S.unattended(t), uu), lh.and_r(Bool.not(S.is_ran(e)), S.none_ran(t), nn)),
        lh.pot_step(s, e, lh.and_l(Bool.not(S.is_user(e)), S.unattended(t), uu), lh.and_l(Bool.not(S.is_ran(e)), S.none_ran(t), nn)))

def lh.sub23(f: Nat) -> {Nat.is_le(Nat.sub(2n, f), Nat.sub(3n, f)) == True{} : Bool}:
  match f:
    case 0n:
      {==}
    case 1n:
      {==}
    case 2n:
      {==}
    case 3n+k:
      {==}

# what is still possible is at most 3 - f
def lh.pot_le(p: Lp.Phase, f: Nat) -> {Nat.is_le(lh.pot(p, f), Nat.sub(3n, f)) == True{} : Bool}:
  match p:
    case Lp.Off{}:
      lh.le_zero(Nat.sub(3n, f))
    case Lp.Armed{}:
      lh.le_zero(Nat.sub(3n, f))
    case Lp.Turn{}:
      lh.sub23(f)
    case Lp.Judging{}:
      lh.le_refl(Nat.sub(3n, f))
    case Lp.Paused{}:
      lh.le_zero(Nat.sub(3n, f))
    case Lp.Ended{w}:
      lh.le_zero(Nat.sub(3n, f))
