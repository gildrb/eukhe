# eukhe: lemmas of the proof of LAW budget_share_refuses_alike: a
# reservation from an offer that fits, with any offers after it, is
# granted exactly when one from the wanted offer is (the phase, the id and
# a fitting offer decide both: bsr.alike2), and its grant holds that offer
# (bsr.holds_c0); with no offer that fits, a grant is impossible
# (bsr.holds_none)

import Base
import ../../../bend/budget.bend as B
import ../../../bend/budget_share.bend as Bs
import ../../../spec/budget/ledger.bend as S
import ../../../laws/budget_share.bend as BudgetShare
import ../../budget/base/reserve.bend as BR

# an offer c0 that fits, then rest: some offer fits
def bsr.some2(+u: B.Use, +base: B.Ask, +keep: B.Ask, +c0: B.Ask, +rest: List<&2, B.Ask>, +f: B.Amt, +now: Nat, +un: Nat, fc: {S.fits(u, base, keep, c0, f, now, un) == True{} : Bool}) -> {S.none_fit(u, base, keep, c0 <> rest, f, now, un) == False{} : Bool}:
  %Equal.sym(Bool, S.fits(u, base, keep, c0, f, now, un), True{}, fc) : {Bool.and(Bool.not(_), S.none_fit(u, base, keep, rest, f, now, un)) == False{} : Bool}
  {==}

# a grant from c0 and then rest, c0 fitting, is of c0, at place 0
def bsr.first_is_c0(i: Nat, +u: B.Use, +base: B.Ask, +keep: B.Ask, +c0: B.Ask, +rest: List<&2, B.Ask>, +f: B.Amt, +now: Nat, +un: Nat, -c: B.Ask, fr: {S.nth(i, c0 <> rest) == Some{c} : Maybe<&2, B.Ask>} & {S.none_fit(u, base, keep, S.before(i, c0 <> rest), f, now, un) == True{} : Bool}, fc: {S.fits(u, base, keep, c0, f, now, un) == True{} : Bool}) -> {Some{c0} == Some{c} : Maybe<&2, B.Ask>}:
  match i:
    case 0n:
      (rn, rb) = fr
      rn
    case 1n+k:
      (rn, rb) = fr
      +x = S.none_fit(u, base, keep, S.before(k, rest), f, now, un)
      BR.br.absurd({Some{c0} == Some{c} : Maybe<&2, B.Ask>}, Equal.trans(Bool, Bool.and(Bool.not(True{}), x), Bool.and(Bool.not(S.fits(u, base, keep, c0, f, now, un)), x), True{}, Equal.cong(Bool, Bool, z => Bool.and(Bool.not(z), x), True{}, S.fits(u, base, keep, c0, f, now, un), Equal.sym(Bool, S.fits(u, base, keep, c0, f, now, un), True{}, fc)), rb))

# a grant of the reservation from c0 and then rest, c0 fitting, holds c0
def bsr.holds_c0(g: B.Grant, +u: B.Use, +p: B.Phase, +id: Nat, +now: Nat, +base: B.Ask, +keep: B.Ask, +step: B.Ask, +c0: B.Ask, +rest: List<&2, B.Ask>, +a: B.Acct, eg: {B.reserve(u, p, id, now, base, keep, step, c0, rest, a) == g : B.Grant}, fc: {S.fits(u, base, keep, c0, S.free(a), now, S.until(a)) == True{} : Bool}) -> BudgetShare.ss_holds_offer(g, Some{c0}):
  match g:
    case B.Granted{+i, +c, +a2, +lo}:
      bsr.first_is_c0(i, u, base, keep, c0, rest, S.free(a), now, S.until(a), c, BR.br.first(u, p, id, now, base, keep, step, c0, rest, a, i, c, a2, lo, BR.br.res_is(u, p, id, now, base, keep, step, c0, rest, a, B.Granted{i, c, a2, lo}, eg)), fc)
    case B.Refused{w, p2}:
      Unit{}

# with no offer that fits, a grant is impossible
def bsr.holds_none.g(+u: B.Use, +p: B.Phase, +id: Nat, +now: Nat, +base: B.Ask, +keep: B.Ask, +step: B.Ask, +want: B.Ask, +less: List<&2, B.Ask>, +a: B.Acct, +i: Nat, +c: B.Ask, +a2: B.Acct, +lo: Bool, -m: Maybe<&2, B.Ask>, r: BR.br.ResA(B.Granted{i, c, a2, lo}, u, p, id, now, base, keep, step, want, less, a), nf: {S.none_fit(u, base, keep, want <> less, S.free(a), now, S.until(a)) == True{} : Bool}) -> {m == Some{c} : Maybe<&2, B.Ask>}:
  (rn, (rb, (rf, (ra, rl)))) = r
  BR.br.absurd({m == Some{c} : Maybe<&2, B.Ask>}, Equal.trans(Bool, False{}, S.fits(u, base, keep, c, S.free(a), now, S.until(a)), True{}, Equal.sym(Bool, S.fits(u, base, keep, c, S.free(a), now, S.until(a)), False{}, BR.br.nf_nth(i, want <> less, u, base, keep, S.free(a), now, S.until(a), c, rn, nf)), rf))

# with no offer that fits, a reservation grants nothing: what it answers
# holds any offer
def bsr.holds_none(g: B.Grant, +u: B.Use, +p: B.Phase, +id: Nat, +now: Nat, +base: B.Ask, +keep: B.Ask, +step: B.Ask, +want: B.Ask, +less: List<&2, B.Ask>, +a: B.Acct, -m: Maybe<&2, B.Ask>, eg: {B.reserve(u, p, id, now, base, keep, step, want, less, a) == g : B.Grant}, nf: {S.none_fit(u, base, keep, want <> less, S.free(a), now, S.until(a)) == True{} : Bool}) -> BudgetShare.ss_holds_offer(g, m):
  match g:
    case B.Granted{+i, +c, +a2, +lo}:
      bsr.holds_none.g(u, p, id, now, base, keep, step, want, less, a, i, c, a2, lo, m, BR.br.res_is(u, p, id, now, base, keep, step, want, less, a, B.Granted{i, c, a2, lo}, eg), nf)
    case B.Refused{w, p2}:
      Unit{}

# a reservation the phase does not admit is refused alike from any offers
def bsr.alike_stopped(+u: B.Use, +p: B.Phase, +id: Nat, +now: Nat, +base: B.Ask, +keep: B.Ask, +step: B.Ask, +want: B.Ask, +less: List<&2, B.Ask>, +a: B.Acct, +c0: B.Ask, +rest: List<&2, B.Ask>, no: {S.allows(p, u) == False{} : Bool}) -> {S.granted(B.reserve(u, p, id, now, base, keep, step, c0, rest, a)) == S.granted(B.reserve(u, p, id, now, base, keep, step, want, less, a)) : Bool}:
  +no0 = no
  Equal.trans(Bool, S.granted(B.reserve(u, p, id, now, base, keep, step, c0, rest, a)), S.granted(B.Refused{B.Stopped{}, p}), S.granted(B.reserve(u, p, id, now, base, keep, step, want, less, a)), Equal.cong(B.Grant, Bool, z => S.granted(z), B.reserve(u, p, id, now, base, keep, step, c0, rest, a), B.Refused{B.Stopped{}, p}, BR.br.stopped(a, u, p, id, now, base, keep, step, c0, rest, no0)), Equal.sym(Bool, S.granted(B.reserve(u, p, id, now, base, keep, step, want, less, a)), S.granted(B.Refused{B.Stopped{}, p}), Equal.cong(B.Grant, Bool, z => S.granted(z), B.reserve(u, p, id, now, base, keep, step, want, less, a), B.Refused{B.Stopped{}, p}, BR.br.stopped(a, u, p, id, now, base, keep, step, want, less, no0))))

# a reservation under an id already held is refused alike from any offers
def bsr.alike_held(+u: B.Use, +p: B.Phase, +id: Nat, +now: Nat, +base: B.Ask, +keep: B.Ask, +step: B.Ask, +want: B.Ask, +less: List<&2, B.Ask>, +a: B.Acct, +c0: B.Ask, +rest: List<&2, B.Ask>, ok: {S.allows(p, u) == True{} : Bool}, dup: {S.has(id, S.holds(a)) == True{} : Bool}) -> {S.granted(B.reserve(u, p, id, now, base, keep, step, c0, rest, a)) == S.granted(B.reserve(u, p, id, now, base, keep, step, want, less, a)) : Bool}:
  +ok0 = ok
  +dup0 = dup
  Equal.trans(Bool, S.granted(B.reserve(u, p, id, now, base, keep, step, c0, rest, a)), S.granted(B.Refused{B.Held{}, p}), S.granted(B.reserve(u, p, id, now, base, keep, step, want, less, a)), Equal.cong(B.Grant, Bool, z => S.granted(z), B.reserve(u, p, id, now, base, keep, step, c0, rest, a), B.Refused{B.Held{}, p}, BR.br.dup(a, u, p, id, now, base, keep, step, c0, rest, ok0, dup0)), Equal.sym(Bool, S.granted(B.reserve(u, p, id, now, base, keep, step, want, less, a)), S.granted(B.Refused{B.Held{}, p}), Equal.cong(B.Grant, Bool, z => S.granted(z), B.reserve(u, p, id, now, base, keep, step, want, less, a), B.Refused{B.Held{}, p}, BR.br.dup(a, u, p, id, now, base, keep, step, want, less, ok0, dup0))))

def bsr.alike_has(h: Bool, +u: B.Use, +p: B.Phase, +id: Nat, +now: Nat, +base: B.Ask, +keep: B.Ask, +step: B.Ask, +want: B.Ask, +less: List<&2, B.Ask>, +a: B.Acct, +c0: B.Ask, +rest: List<&2, B.Ask>, eh: {S.has(id, S.holds(a)) == h : Bool}, ok: {S.allows(p, u) == True{} : Bool}, fc: {S.fits(u, base, keep, c0, S.free(a), now, S.until(a)) == True{} : Bool}, some: {S.none_fit(u, base, keep, want <> less, S.free(a), now, S.until(a)) == False{} : Bool}) -> {S.granted(B.reserve(u, p, id, now, base, keep, step, c0, rest, a)) == S.granted(B.reserve(u, p, id, now, base, keep, step, want, less, a)) : Bool}:
  match h:
    case True{}:
      bsr.alike_held(u, p, id, now, base, keep, step, want, less, a, c0, rest, ok, eh)
    case False{}:
      +ok0 = ok
      +eh0 = eh
      Equal.trans(Bool, S.granted(B.reserve(u, p, id, now, base, keep, step, c0, rest, a)), True{}, S.granted(B.reserve(u, p, id, now, base, keep, step, want, less, a)), BR.br.when_fits(a, u, p, id, now, base, keep, step, c0, rest, ok0, eh0, bsr.some2(u, base, keep, c0, rest, S.free(a), now, S.until(a), fc)), Equal.sym(Bool, S.granted(B.reserve(u, p, id, now, base, keep, step, want, less, a)), True{}, BR.br.when_fits(a, u, p, id, now, base, keep, step, want, less, ok0, eh0, some)))

def bsr.alike_allows(b: Bool, +u: B.Use, +p: B.Phase, +id: Nat, +now: Nat, +base: B.Ask, +keep: B.Ask, +step: B.Ask, +want: B.Ask, +less: List<&2, B.Ask>, +a: B.Acct, +c0: B.Ask, +rest: List<&2, B.Ask>, eb: {S.allows(p, u) == b : Bool}, fc: {S.fits(u, base, keep, c0, S.free(a), now, S.until(a)) == True{} : Bool}, some: {S.none_fit(u, base, keep, want <> less, S.free(a), now, S.until(a)) == False{} : Bool}) -> {S.granted(B.reserve(u, p, id, now, base, keep, step, c0, rest, a)) == S.granted(B.reserve(u, p, id, now, base, keep, step, want, less, a)) : Bool}:
  match b:
    case True{}:
      bsr.alike_has(S.has(id, S.holds(a)), u, p, id, now, base, keep, step, want, less, a, c0, rest, {==}, eb, fc, some)
    case False{}:
      bsr.alike_stopped(u, p, id, now, base, keep, step, want, less, a, c0, rest, eb)

# from an offer c0 that fits, with any offers after it: granted exactly
# when from the wanted offer, and a grant holds c0
def bsr.alike2(+u: B.Use, +p: B.Phase, +id: Nat, +now: Nat, +base: B.Ask, +keep: B.Ask, +step: B.Ask, +want: B.Ask, +less: List<&2, B.Ask>, +a: B.Acct, +c0: B.Ask, +rest: List<&2, B.Ask>, fc: {S.fits(u, base, keep, c0, S.free(a), now, S.until(a)) == True{} : Bool}, some: {S.none_fit(u, base, keep, want <> less, S.free(a), now, S.until(a)) == False{} : Bool}) -> {S.granted(B.reserve(u, p, id, now, base, keep, step, c0, rest, a)) == S.granted(B.reserve(u, p, id, now, base, keep, step, want, less, a)) : Bool} & BudgetShare.ss_holds_offer(B.reserve(u, p, id, now, base, keep, step, c0, rest, a), Some{c0}):
  +fc0 = fc
  (bsr.alike_allows(S.allows(p, u), u, p, id, now, base, keep, step, want, less, a, c0, rest, {==}, fc0, some), bsr.holds_c0(B.reserve(u, p, id, now, base, keep, step, c0, rest, a), u, p, id, now, base, keep, step, c0, rest, a, {==}, fc0))

# the claim of budget_share_refuses_alike from place j of want and then
# less
def bsr.Alike(+j: Nat, +u: B.Use, +p: B.Phase, +id: Nat, +now: Nat, +base: B.Ask, +keep: B.Ask, +step: B.Ask, +want: B.Ask, +less: List<&2, B.Ask>, +a: B.Acct) -> Type:
  {S.granted(B.reserve(u, p, id, now, base, keep, step, BudgetShare.ss_offer(j, want, less), BudgetShare.ss_after(j, want <> less), a)) == S.granted(B.reserve(u, p, id, now, base, keep, step, want, less, a)) : Bool} & BudgetShare.ss_holds_offer(B.reserve(u, p, id, now, base, keep, step, BudgetShare.ss_offer(j, want, less), BudgetShare.ss_after(j, want <> less), a), S.nth(j, want <> less))

# the offer m at place j fits: the claim from place j
def bsr.alike_m(m: Maybe<&2, B.Ask>, +j: Nat, +u: B.Use, +p: B.Phase, +id: Nat, +now: Nat, +base: B.Ask, +keep: B.Ask, +step: B.Ask, +want: B.Ask, +less: List<&2, B.Ask>, +a: B.Acct, em: {S.nth(j, want <> less) == m : Maybe<&2, B.Ask>}, mf: {BudgetShare.ss_mfits(u, base, keep, m, S.free(a), now, S.until(a)) == True{} : Bool}, some: {S.none_fit(u, base, keep, want <> less, S.free(a), now, S.until(a)) == False{} : Bool}) -> bsr.Alike(j, u, p, id, now, base, keep, step, want, less, a):
  match m:
    case None{}:
      BR.br.absurd(bsr.Alike(j, u, p, id, now, base, keep, step, want, less, a), mf)
    case Some{+c0}:
      %Equal.sym(Maybe<&2, B.Ask>, S.nth(j, want <> less), Some{c0}, em) : {S.granted(B.reserve(u, p, id, now, base, keep, step, BudgetShare.ss_offer.of(_, want), BudgetShare.ss_after(j, want <> less), a)) == S.granted(B.reserve(u, p, id, now, base, keep, step, want, less, a)) : Bool} & BudgetShare.ss_holds_offer(B.reserve(u, p, id, now, base, keep, step, BudgetShare.ss_offer.of(_, want), BudgetShare.ss_after(j, want <> less), a), _)
      bsr.alike2(u, p, id, now, base, keep, step, want, less, a, c0, BudgetShare.ss_after(j, want <> less), mf, some)
