# eukhe: the proof of LAW loop_enter_sets_bounds
#
# PROOF: the state is opened; lb.enter_bounds splits the phase under the
# premise (lb.Unless): off or ended, `/loop` is Lp.start, whose state has
# Lp.turns and Lp.until of the limit with or without an inline prompt
# (lb.start_bounds); for a count and no limit these compute to the
# claims; for a span, Lp.until cuts the clock plus the span with
# Lp.until.cut, which is the law's cut (lf.cut_eq).

import Base
import ../../bend/loop.bend as Lp
import ../../spec/loop/loop.bend as S
import ../../laws/loop/model.bend as Loop
import ./base/bounds.bend as LALoopBounds
import ./base/fits.bend as LALoopFits

def lsb.span(p: Lp.Phase, pr: Maybe<&2, String>, -i: Nat, -l: Maybe<&2, Nat>, -d: Maybe<&2, Nat>, -c0: Lp.Cond, -b: String, -f: Nat, -x: Lp.Last, +ms: Nat, -c: Lp.Cond, +now: Nat, off: {S.is_on(p) == False{} : Bool}) -> {(S.left(S.next(Lp.St{p, i, l, d, c0, b, f, x}, Lp.Enter{Lp.Span{ms}, c, pr, now})), S.deadline(S.next(Lp.St{p, i, l, d, c0, b, f, x}, Lp.Enter{Lp.Span{ms}, c, pr, now}))) == (None{}, Loop.lp_cut(Nat.add(now, ms))) : Maybe<&2, Nat> & Maybe<&2, Nat>}:
  %LALoopFits.lf.cut_eq(Nat.add(now, ms)) : {(S.left(S.next(Lp.St{p, i, l, d, c0, b, f, x}, Lp.Enter{Lp.Span{ms}, c, pr, now})), S.deadline(S.next(Lp.St{p, i, l, d, c0, b, f, x}, Lp.Enter{Lp.Span{ms}, c, pr, now}))) == (None{}, _) : Maybe<&2, Nat> & Maybe<&2, Nat>}
  LALoopBounds.lb.enter_bounds(p, pr, i, l, d, c0, b, f, x, Lp.Span{ms}, c, now, off)

def Loop.loop_enter_sets_bounds(s, n, ms, c, pr, now, off):
  match s:
    case Lp.St{p, i, l, d, c0, b, f, x}:
      +q = pr
      +o = off
      (LALoopBounds.lb.enter_bounds(p, q, i, l, d, c0, b, f, x, Lp.Count{n}, c, now, o),
       lsb.span(p, q, i, l, d, c0, b, f, x, ms, c, now, o),
       LALoopBounds.lb.enter_bounds(p, q, i, l, d, c0, b, f, x, Lp.NoLimit{}, c, now, o))
