# eukhe: the proof of LAW budget_not_low_funds_next
#
# PROOF: the grant says (br.res_is) that the work c fit what was free
# with the reserves, that two steps did too, amount and time (not low),
# and the account after it. Settled, its hold is free again and the spend
# is taken: what is free is what was free less the spend (nl.room_in,
# through bs.open and bs.at_free; the hold of the id just granted is the
# one held). A spend within one step leaves one more step and the
# reserves (nl.room); asked by now and one step's time, one step and the
# reserves end by the deadline (nl.time). So the last offer, within one
# step, fits (nl.fits_next), not none fits (nl.last_some), and the
# request is granted as in budget_grant_when_fits.

import Base
import ../../laws/budget.bend as Budget
import ../../bend/budget.bend as B
import ../../spec/budget/ledger.bend as S
import ./base/reserve.bend as BR
import ./base/settle.bend as BS
import ./base/amt.bend as BA

# n is n
def nl.eq_refl(n: Nat) -> {Nat.is_eq(n, n) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+m:
      nl.eq_refl(m)

# not True is not False
def nl.true_of_not(b: Bool, e: {False{} == Bool.not(b) : Bool}) -> {b == True{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      e

def nl.and_false(b: Bool, -r: Bool, e: {r == False{} : Bool}) -> {Bool.and(b, r) == False{} : Bool}:
  match b:
    case True{}:
      e
    case False{}:
      {==}

# the last offer fits: not none fits
def nl.last_some(less: List<&2, B.Ask>, +x: B.Ask, +u: B.Use, +base: B.Ask, +keep: B.Ask, +f: B.Amt, +now: Nat, +un: Nat, e: {S.fits(u, base, keep, S.last(less, x), f, now, un) == True{} : Bool}) -> {S.none_fit(u, base, keep, x <> less, f, now, un) == False{} : Bool}:
  match less:
    case Nil{}:
      BR.br.nf_single(S.fits(u, base, keep, x, f, now, un), e)
    case Con{y, t}:
      nl.and_false(Bool.not(S.fits(u, base, keep, x, f, now, un)), S.none_fit(u, base, keep, y <> t, f, now, un), nl.last_some(t, y, u, base, keep, f, now, un, e))

# the hold just granted is held
def nl.open(+id: Nat, -x: B.Amt, -h: List<&2, B.Hold>) -> {S.has(id, B.Hold{id, x} <> h) == True{} : Bool}:
  %Equal.sym(Bool, Nat.is_eq(id, id), True{}, nl.eq_refl(id)) : {Bool.or(_, S.has(id, h)) == True{} : Bool}
  {==}

# (s + s) + bk within F: s + (s + bk) within F
def nl.two_steps(+s: Nat, +bk: Nat, +F: Nat, e2: {Nat.is_le(Nat.add(Nat.add(s, s), bk), F) == True{} : Bool}) -> {Nat.is_le(Nat.add(s, Nat.add(s, bk)), F) == True{} : Bool}:
  %BR.br.add_assoc(s, s, bk) : {Nat.is_le(_, F) == True{} : Bool}
  e2

# two steps and the reserves within F: the spend act of at most one step
# and one more step and the reserves within F + ho
def nl.after_act(+s: Nat, +act: Nat, +bk: Nat, +F: Nat, +ho: Nat, eA: {Nat.is_le(act, s) == True{} : Bool}, e2: {Nat.is_le(Nat.add(Nat.add(s, s), bk), F) == True{} : Bool}) -> {Nat.is_le(Nat.add(act, Nat.add(s, bk)), Nat.add(F, ho)) == True{} : Bool}:
  BR.br.le_trans(Nat.add(act, Nat.add(s, bk)), F, Nat.add(F, ho), BR.br.le_trans(Nat.add(act, Nat.add(s, bk)), Nat.add(s, Nat.add(s, bk)), F, BR.br.mono_l(act, s, Nat.add(s, bk), eA), nl.two_steps(s, bk, F, e2)), BR.br.le_self(F, ho))

# in one spent dimension: the work x (with the reserves bk) fit F, two
# steps s did, the spend act and the next offer L are within a step; then
# L and the reserves fit what is free after the settlement: F less x, the
# hold x and what else the id held (ho), less the spend
def nl.room(+L: Nat, +s: Nat, +x: Nat, +act: Nat, +bk: Nat, +F: Nat, +ho: Nat, eL: {Nat.is_le(L, s) == True{} : Bool}, eA: {Nat.is_le(act, s) == True{} : Bool}, ex: {Nat.is_le(Nat.add(x, bk), F) == True{} : Bool}, e2: {Nat.is_le(Nat.add(Nat.add(s, s), bk), F) == True{} : Bool}) -> {Nat.is_le(Nat.add(L, bk), Nat.sub(Nat.add(Nat.sub(F, x), Nat.add(x, ho)), act)) == True{} : Bool}:
  %BR.br.add_assoc(Nat.sub(F, x), x, ho) : {Nat.is_le(Nat.add(L, bk), Nat.sub(_, act)) == True{} : Bool}
  %Equal.sym(Nat, Nat.add(Nat.sub(F, x), x), F, BR.br.take(x, bk, F, ex)) : {Nat.is_le(Nat.add(L, bk), Nat.sub(Nat.add(_, ho), act)) == True{} : Bool}
  BR.br.le_trans(Nat.add(L, bk), Nat.add(s, bk), Nat.sub(Nat.add(F, ho), act), BR.br.mono_l(L, s, bk, eL), BR.br.le_sub(act, Nat.add(F, ho), Nat.add(s, bk), nl.after_act(s, act, bk, F, ho, eA, e2)))

# (now + s) + (s + bk) <= un when now + ((s + s) + bk) <= un
def nl.time_end(+now: Nat, +s: Nat, +bk: Nat, +un: Nat, w: {Nat.is_le(Nat.add(now, Nat.add(Nat.add(s, s), bk)), un) == True{} : Bool}) -> {Nat.is_le(Nat.add(Nat.add(now, s), Nat.add(s, bk)), un) == True{} : Bool}:
  %Equal.sym(Nat, Nat.add(Nat.add(now, s), Nat.add(s, bk)), Nat.add(now, Nat.add(s, Nat.add(s, bk))), BR.br.add_assoc(now, s, Nat.add(s, bk))) : {Nat.is_le(_, un) == True{} : Bool}
  %BR.br.add_assoc(s, s, bk) : {Nat.is_le(Nat.add(now, _), un) == True{} : Bool}
  w

# two steps s and the reserves bk ended by un from now: asked by now + s,
# an offer of at most s with the reserves ends by un
def nl.time(+now: Nat, +now2: Nat, +s: Nat, +Lm: Nat, +bk: Nat, +un: Nat, soon: {Nat.is_le(now2, Nat.add(now, s)) == True{} : Bool}, eL: {Nat.is_le(Lm, s) == True{} : Bool}, w: {Nat.is_le(Nat.add(now, Nat.add(Nat.add(s, s), bk)), un) == True{} : Bool}) -> {Nat.is_le(Nat.add(now2, Nat.add(Lm, bk)), un) == True{} : Bool}:
  BR.br.le_trans(Nat.add(now2, Nat.add(Lm, bk)), Nat.add(Nat.add(now, s), Nat.add(Lm, bk)), un, BR.br.mono_l(now2, Nat.add(now, s), Nat.add(Lm, bk), soon), BR.br.le_trans(Nat.add(Nat.add(now, s), Nat.add(Lm, bk)), Nat.add(Nat.add(now, s), Nat.add(s, bk)), un, BR.br.mono_r(Nat.add(now, s), Nat.add(Lm, bk), Nat.add(s, bk), BR.br.mono_l(Lm, s, bk, eL)), nl.time_end(now, s, bk, un, w)))

# a settlement keeps the deadline
def nl.until_of(+id: Nat, -act: B.Amt, -f: B.Amt, -s: B.Amt, -l: B.Amt, -o: B.Amt, +hs: List<&2, B.Hold>, -u: Nat, open: {S.has(id, hs) == True{} : Bool}) -> {S.until(B.settle(id, act, B.Acct{f, s, l, o, hs, u})) == u : Nat}:
  %BS.bs.open(id, act, f, s, l, o, hs, u, open) : {S.until(_) == u : Nat}
  {==}

# in spent dimension d, the offer x within a step fits, with the
# reserves, what is free after the work c, granted on f, settled at act
def nl.room_in(+d: B.Dim, +id: Nat, +act: B.Amt, +f: B.Amt, +c: B.Ask, +s: B.Amt, +l: B.Amt, +o: B.Amt, +h: List<&2, B.Hold>, +u: Nat, +base: B.Ask, +keep: B.Ask, +x: B.Ask, +st: B.Ask, eL: {Nat.is_le(S.at(d, S.amt(x)), S.at(d, S.amt(st))) == True{} : Bool}, eA: {Nat.is_le(S.at(d, act), S.at(d, S.amt(st))) == True{} : Bool}, ex: {S.fits_in(B.Work{}, base, keep, c, f, d) == True{} : Bool}, e2: {Nat.is_le(Nat.add(Nat.add(S.at(d, S.amt(st)), S.at(d, S.amt(st))), Nat.add(S.at(d, S.amt(base)), S.at(d, S.amt(keep)))), S.at(d, f)) == True{} : Bool}) -> {S.fits_in(B.Work{}, base, keep, x, S.free(B.settle(id, act, B.Acct{B.sub4(f, S.amt(c)), s, l, o, B.Hold{id, S.amt(c)} <> h, u})), d) == True{} : Bool}:
  %BS.bs.open(id, act, B.sub4(f, S.amt(c)), s, l, o, B.Hold{id, S.amt(c)} <> h, u, nl.open(id, S.amt(c), h)) : {Nat.is_le(Nat.add(S.at(d, S.amt(x)), Nat.add(S.at(d, S.amt(base)), S.at(d, S.amt(keep)))), S.at(d, S.free(_))) == True{} : Bool}
  %BS.bs.at_free(d, id, B.sub4(f, S.amt(c)), B.Hold{id, S.amt(c)} <> h, act) : {Nat.is_le(Nat.add(S.at(d, S.amt(x)), Nat.add(S.at(d, S.amt(base)), S.at(d, S.amt(keep)))), _) == True{} : Bool}
  %Equal.sym(Nat, S.at(d, B.sub4(f, S.amt(c))), Nat.sub(S.at(d, f), S.at(d, S.amt(c))), BA.ba.at_sub4(d, f, S.amt(c))) : {Nat.is_le(Nat.add(S.at(d, S.amt(x)), Nat.add(S.at(d, S.amt(base)), S.at(d, S.amt(keep)))), Nat.sub(Nat.add(_, S.held_of(id, d, B.Hold{id, S.amt(c)} <> h)), S.at(d, act))) == True{} : Bool}
  %Equal.sym(Bool, Nat.is_eq(id, id), True{}, nl.eq_refl(id)) : {Nat.is_le(Nat.add(S.at(d, S.amt(x)), Nat.add(S.at(d, S.amt(base)), S.at(d, S.amt(keep)))), Nat.sub(Nat.add(Nat.sub(S.at(d, f), S.at(d, S.amt(c))), S.held_of.one(_, S.at(d, S.amt(c)), S.held_of(id, d, h))), S.at(d, act))) == True{} : Bool}
  nl.room(S.at(d, S.amt(x)), S.at(d, S.amt(st)), S.at(d, S.amt(c)), S.at(d, act), Nat.add(S.at(d, S.amt(base)), S.at(d, S.amt(keep))), S.at(d, f), S.held_of(id, d, h), eL, eA, ex, e2)

# the offer x within a step, asked by now and a step's time, fits what
# the work c, granted not low on f by u, left once settled at act
def nl.fits_next(+id: Nat, +act: B.Amt, +f: B.Amt, +c: B.Ask, +s: B.Amt, +l: B.Amt, +o: B.Amt, +h: List<&2, B.Hold>, +u: Nat, +now: Nat, +now2: Nat, +base: B.Ask, +keep: B.Ask, +x: B.Ask, +st: B.Ask, +spent: {S.le(B.Ask{act, 0n}, st) == True{} : Bool}, soon: {Nat.is_le(now2, Nat.add(now, S.ms(st))) == True{} : Bool}, +small: {S.le(x, st) == True{} : Bool}, +rf: {S.fits(B.Work{}, base, keep, c, f, now, u) == True{} : Bool}, +two: {S.fits(B.Work{}, base, keep, S.plus(st, st), f, now, u) == True{} : Bool}) -> {S.fits(B.Work{}, base, keep, x, S.free(B.settle(id, act, B.Acct{B.sub4(f, S.amt(c)), s, l, o, B.Hold{id, S.amt(c)} <> h, u})), now2, S.until(B.settle(id, act, B.Acct{B.sub4(f, S.amt(c)), s, l, o, B.Hold{id, S.amt(c)} <> h, u}))) == True{} : Bool}:
  %Equal.sym(Nat, S.until(B.settle(id, act, B.Acct{B.sub4(f, S.amt(c)), s, l, o, B.Hold{id, S.amt(c)} <> h, u})), u, nl.until_of(id, act, B.sub4(f, S.amt(c)), s, l, o, B.Hold{id, S.amt(c)} <> h, u, nl.open(id, S.amt(c), h))) : {S.fits(B.Work{}, base, keep, x, S.free(B.settle(id, act, B.Acct{B.sub4(f, S.amt(c)), s, l, o, B.Hold{id, S.amt(c)} <> h, u})), now2, _) == True{} : Bool}
  BR.br.and5(S.fits_in(B.Work{}, base, keep, x, S.free(B.settle(id, act, B.Acct{B.sub4(f, S.amt(c)), s, l, o, B.Hold{id, S.amt(c)} <> h, u})), B.Cost{}), S.fits_in(B.Work{}, base, keep, x, S.free(B.settle(id, act, B.Acct{B.sub4(f, S.amt(c)), s, l, o, B.Hold{id, S.amt(c)} <> h, u})), B.Tok{}), S.on_time(B.Work{}, base, keep, x, now2, u), S.fits_in(B.Work{}, base, keep, x, S.free(B.settle(id, act, B.Acct{B.sub4(f, S.amt(c)), s, l, o, B.Hold{id, S.amt(c)} <> h, u})), B.Calls{}), S.fits_in(B.Work{}, base, keep, x, S.free(B.settle(id, act, B.Acct{B.sub4(f, S.amt(c)), s, l, o, B.Hold{id, S.amt(c)} <> h, u})), B.Reqs{}), nl.room_in(B.Cost{}, id, act, f, c, s, l, o, h, u, base, keep, x, st, BR.br.le_at(B.Cost{}, x, st, small), BR.br.le_at(B.Cost{}, B.Ask{act, 0n}, st, spent), BR.br.fits_at(B.Cost{}, B.Work{}, base, keep, c, f, now, u, rf), BR.br.fits_at(B.Cost{}, B.Work{}, base, keep, S.plus(st, st), f, now, u, two)), nl.room_in(B.Tok{}, id, act, f, c, s, l, o, h, u, base, keep, x, st, BR.br.le_at(B.Tok{}, x, st, small), BR.br.le_at(B.Tok{}, B.Ask{act, 0n}, st, spent), BR.br.fits_at(B.Tok{}, B.Work{}, base, keep, c, f, now, u, rf), BR.br.fits_at(B.Tok{}, B.Work{}, base, keep, S.plus(st, st), f, now, u, two)), nl.time(now, now2, S.ms(st), S.ms(x), Nat.add(S.ms(base), S.ms(keep)), u, soon, BR.br.le_ms(x, st, small), BR.br.on_time_of(B.Work{}, base, keep, S.plus(st, st), f, now, u, two)), nl.room_in(B.Calls{}, id, act, f, c, s, l, o, h, u, base, keep, x, st, BR.br.le_at(B.Calls{}, x, st, small), BR.br.le_at(B.Calls{}, B.Ask{act, 0n}, st, spent), BR.br.fits_at(B.Calls{}, B.Work{}, base, keep, c, f, now, u, rf), BR.br.fits_at(B.Calls{}, B.Work{}, base, keep, S.plus(st, st), f, now, u, two)), nl.room_in(B.Reqs{}, id, act, f, c, s, l, o, h, u, base, keep, x, st, BR.br.le_at(B.Reqs{}, x, st, small), BR.br.le_at(B.Reqs{}, B.Ask{act, 0n}, st, spent), BR.br.fits_at(B.Reqs{}, B.Work{}, base, keep, c, f, now, u, rf), BR.br.fits_at(B.Reqs{}, B.Work{}, base, keep, S.plus(st, st), f, now, u, two)))

# what the grant says, its account written out: not none of the next
# offers fits
def nl.some(+p: B.Phase, +id: Nat, +now: Nat, +base: B.Ask, +keep: B.Ask, +step: B.Ask, +want: B.Ask, +less: List<&2, B.Ask>, +a: B.Acct, +i: Nat, +c: B.Ask, +a2: B.Acct, +act: B.Amt, +now2: Nat, +want2: B.Ask, +less2: List<&2, B.Ask>, r: BR.br.ResA(B.Granted{i, c, a2, False{}}, B.Work{}, p, id, now, base, keep, step, want, less, a), spent: {S.le(B.Ask{act, 0n}, step) == True{} : Bool}, soon: {Nat.is_le(now2, Nat.add(now, S.ms(step))) == True{} : Bool}, small: {S.le(S.last(less2, want2), step) == True{} : Bool}) -> {S.none_fit(B.Work{}, base, keep, want2 <> less2, S.free(B.settle(id, act, a2)), now2, S.until(B.settle(id, act, a2))) == False{} : Bool}:
  (rn, (rb, (rf, (ra, rl)))) = r
  %ra : {S.none_fit(B.Work{}, base, keep, want2 <> less2, S.free(B.settle(id, act, _)), now2, S.until(B.settle(id, act, _))) == False{} : Bool}
  nl.last_some(less2, want2, B.Work{}, base, keep, S.free(B.settle(id, act, B.Acct{B.sub4(S.free(a), S.amt(c)), S.spent(a), S.lent(a), S.over(a), B.Hold{id, S.amt(c)} <> S.holds(a), S.until(a)})), now2, S.until(B.settle(id, act, B.Acct{B.sub4(S.free(a), S.amt(c)), S.spent(a), S.lent(a), S.over(a), B.Hold{id, S.amt(c)} <> S.holds(a), S.until(a)})), nl.fits_next(id, act, S.free(a), c, S.spent(a), S.lent(a), S.over(a), S.holds(a), S.until(a), now, now2, base, keep, S.last(less2, want2), step, spent, soon, small, rf, nl.true_of_not(S.fits(B.Work{}, base, keep, S.plus(step, step), S.free(a), now, S.until(a)), rl)))

def Budget.budget_not_low_funds_next(p, id, now, base, keep, step, want, less, a, i, c, a2, act, p2, id2, now2, step2, want2, less2, g, spent, ok, fresh, soon, small):
  BR.br.when_fits(B.settle(id, act, a2), B.Work{}, p2, id2, now2, base, keep, step2, want2, less2, ok, fresh, nl.some(p, id, now, base, keep, step, want, less, a, i, c, a2, act, now2, want2, less2, BR.br.res_is(B.Work{}, p, id, now, base, keep, step, want, less, a, B.Granted{i, c, a2, False{}}, g), spent, soon, small))
