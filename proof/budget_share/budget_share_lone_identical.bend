# eukhe: the proof of LAW budget_share_lone_identical
#
# PROOF: when no offer fits, the start is 0 (bsm.nf0) and both
# reservations are one (bsl.shift0). When one fits, the start is the place
# j of the first offer c0 that fits (bsm.ff). Then the phase and the id
# refuse both alike; else reserve picks, of c0 and the offers after it,
# c0 at place 0 (bsl.pick_c0), and of all the offers c0 at place j (the
# pick is the first that fits: br.pick_ok; two first places are one:
# bsl.uniq): the same grant, its place j later (bsl.grant_eq).

import Base
import ../../bend/budget.bend as B
import ../../bend/budget_share.bend as Bs
import ../../spec/budget/ledger.bend as S
import ../../laws/budget_share.bend as BudgetShare
import ./base/model.bend as BSM
import ../budget/base/reserve.bend as BR

# the answer from place 0 is itself
def bsl.shift0(g: B.Grant) -> {BudgetShare.ss_shift(0n, g) == g : B.Grant}:
  match g:
    case B.Granted{+i, +c, +a2, +lo}:
      Equal.cong(Nat, B.Grant, z => B.Granted{z, c, a2, lo}, Nat.add(i, 0n), i, BR.br.add_zero(i))
    case B.Refused{w, p}:
      {==}

# the offer m is some x that fits: m fits
def bsl.mf(+u: B.Use, +base: B.Ask, +keep: B.Ask, +f: B.Amt, +now: Nat, +un: Nat, -m: Maybe<&2, B.Ask>, -x: B.Ask, em: {m == Some{x} : Maybe<&2, B.Ask>}, fx: {S.fits(u, base, keep, x, f, now, un) == True{} : Bool}) -> {BudgetShare.ss_mfits(u, base, keep, m, f, now, un) == True{} : Bool}:
  %Equal.sym(Maybe<&2, B.Ask>, m, Some{x}, em) : {BudgetShare.ss_mfits(u, base, keep, _, f, now, un) == True{} : Bool}
  fx

# two places, each fitting with none before it fitting, are one
def bsl.uniq(j: Nat, k: Nat, xs: List<&2, B.Ask>, +u: B.Use, +base: B.Ask, +keep: B.Ask, +f: B.Amt, +now: Nat, +un: Nat, bj: {S.none_fit(u, base, keep, S.before(j, xs), f, now, un) == True{} : Bool}, fj: {BudgetShare.ss_mfits(u, base, keep, S.nth(j, xs), f, now, un) == True{} : Bool}, bk: {S.none_fit(u, base, keep, S.before(k, xs), f, now, un) == True{} : Bool}, fk: {BudgetShare.ss_mfits(u, base, keep, S.nth(k, xs), f, now, un) == True{} : Bool}) -> {j == k : Nat}:
  match j k xs:
    case 0n 0n ys:
      {==}
    case 0n 1n+k2 Nil{}:
      BR.br.absurd({0n == 1n+k2 : Nat}, fj)
    case 0n 1n+k2 Con{+y, +t}:
      BR.br.absurd({0n == 1n+k2 : Nat}, BSM.bsm.false_true(S.fits(u, base, keep, y, f, now, un), BR.br.not_true(S.fits(u, base, keep, y, f, now, un), BR.br.and_l(Bool.not(S.fits(u, base, keep, y, f, now, un)), S.none_fit(u, base, keep, S.before(k2, t), f, now, un), bk)), fj))
    case 1n+j2 0n Nil{}:
      BR.br.absurd({1n+j2 == 0n : Nat}, fk)
    case 1n+j2 0n Con{+y, +t}:
      BR.br.absurd({1n+j2 == 0n : Nat}, BSM.bsm.false_true(S.fits(u, base, keep, y, f, now, un), BR.br.not_true(S.fits(u, base, keep, y, f, now, un), BR.br.and_l(Bool.not(S.fits(u, base, keep, y, f, now, un)), S.none_fit(u, base, keep, S.before(j2, t), f, now, un), bj)), fk))
    case 1n+j2 1n+k2 Nil{}:
      BR.br.absurd({1n+j2 == 1n+k2 : Nat}, fj)
    case 1n+j2 1n+k2 Con{+y, +t}:
      Equal.cong(Nat, Nat, z => 1n+z, j2, k2, bsl.uniq(j2, k2, t, u, base, keep, f, now, un, BR.br.and_r(Bool.not(S.fits(u, base, keep, y, f, now, un)), S.none_fit(u, base, keep, S.before(j2, t), f, now, un), bj), fj, BR.br.and_r(Bool.not(S.fits(u, base, keep, y, f, now, un)), S.none_fit(u, base, keep, S.before(k2, t), f, now, un), bk), fk))

# the pick of all the offers is the first that fits: c0 at place j
def bsl.pick_eq(pk: B.Pick, +u: B.Use, +base: B.Ask, +keep: B.Ask, +f: B.Amt, +now: Nat, +un: Nat, +want: B.Ask, +less: List<&2, B.Ask>, +j: Nat, +c0: B.Ask, po: BR.br.PickOk(pk, u, base, keep, f, now, un, want, less), e: {S.nth(j, want <> less) == Some{c0} : Maybe<&2, B.Ask>}, nb: {S.none_fit(u, base, keep, S.before(j, want <> less), f, now, un) == True{} : Bool}, fc: {S.fits(u, base, keep, c0, f, now, un) == True{} : Bool}) -> {pk == B.Fit{j, c0} : B.Pick}:
  match pk:
    case B.Fit{+j2, +x}:
      (pn, (pb, pf)) = po
      +pn0 = pn
      +e0 = e
      +ej = bsl.uniq(j2, j, want <> less, u, base, keep, f, now, un, pb, bsl.mf(u, base, keep, f, now, un, S.nth(j2, want <> less), x, pn0, pf), nb, bsl.mf(u, base, keep, f, now, un, S.nth(j, want <> less), c0, e0, fc))
      +ss = Equal.trans(Maybe<&2, B.Ask>, Some{x}, S.nth(j2, want <> less), Some{c0}, Equal.sym(Maybe<&2, B.Ask>, S.nth(j2, want <> less), Some{x}, pn0), Equal.trans(Maybe<&2, B.Ask>, S.nth(j2, want <> less), S.nth(j, want <> less), Some{c0}, Equal.cong(Nat, Maybe<&2, B.Ask>, z => S.nth(z, want <> less), j2, j, ej), e0))
      +ex = Equal.cong(Maybe<&2, B.Ask>, B.Ask, z => BudgetShare.ss_offer.of(z, x), Some{x}, Some{c0}, ss)
      Equal.trans(B.Pick, B.Fit{j2, x}, B.Fit{j, x}, B.Fit{j, c0}, Equal.cong(Nat, B.Pick, z => B.Fit{z, x}, j2, j, ej), Equal.cong(B.Ask, B.Pick, z => B.Fit{j, z}, x, c0, ex))
    case B.NoFit{+d}:
      (pa, pl) = po
      BR.br.absurd({B.NoFit{d} == B.Fit{j, c0} : B.Pick}, BSM.bsm.false_true(S.fits(u, base, keep, c0, f, now, un), BR.br.nf_nth(j, want <> less, u, base, keep, f, now, un, c0, e, pa), fc))

# an offer that fits lacks nothing
def bsl.lack_none(l: Maybe<&2, B.Dim>, +u: B.Use, +base: B.Ask, +keep: B.Ask, +c0: B.Ask, +f: B.Amt, +now: Nat, +un: Nat, lo: BR.br.LackOk(l, u, base, keep, c0, f, now, un), fc: {S.fits(u, base, keep, c0, f, now, un) == True{} : Bool}) -> {l == None{} : Maybe<&2, B.Dim>}:
  match l:
    case None{}:
      {==}
    case Some{d}:
      (na, ns) = lo
      BR.br.absurd({Some{d} == None{} : Maybe<&2, B.Dim>}, BSM.bsm.false_true(S.fits(u, base, keep, c0, f, now, un), na, fc))

# the pick of c0, which fits, and then rest is c0 at place 0
def bsl.pick_c0(rest: List<&2, B.Ask>, +u: B.Use, +base: B.Ask, +keep: B.Ask, +f: B.Amt, +now: Nat, +un: Nat, +c0: B.Ask, fc: {S.fits(u, base, keep, c0, f, now, un) == True{} : Bool}) -> {B.pick(rest, u, base, keep, f, now, un, c0, 0n) == B.Fit{0n, c0} : B.Pick}:
  match rest:
    case Nil{}:
      %Equal.sym(Maybe<&2, B.Dim>, B.lack(B.need(u, base, keep, c0), f, now, un), None{}, bsl.lack_none(B.lack(B.need(u, base, keep, c0), f, now, un), u, base, keep, c0, f, now, un, BR.br.lack_ok(u, base, keep, c0, f, now, un), fc)) : {B.pick.one(_, 0n, c0) == B.Fit{0n, c0} : B.Pick}
      {==}
    case Con{h, t}:
      %Equal.sym(Maybe<&2, B.Dim>, B.lack(B.need(u, base, keep, c0), f, now, un), None{}, bsl.lack_none(B.lack(B.need(u, base, keep, c0), f, now, un), u, base, keep, c0, f, now, un, BR.br.lack_ok(u, base, keep, c0, f, now, un), fc)) : {B.pick.or(_, 0n, c0, B.pick(t, u, base, keep, f, now, un, h, 1n)) == B.Fit{0n, c0} : B.Pick}
      {==}

# c0 granted at place 0, read j later, is c0 granted at place j
def bsl.grant_eq(c0: B.Ask, +j: Nat, +u: B.Use, +p: B.Phase, +id: Nat, +now: Nat, +base: B.Ask, +keep: B.Ask, +step: B.Ask, +f: B.Amt, +s: B.Amt, +l: B.Amt, +o: B.Amt, +h: List<&2, B.Hold>, +un: Nat) -> {BudgetShare.ss_shift(j, B.reserve.pick(B.Fit{0n, c0}, u, p, id, now, base, keep, step, f, s, l, o, h, un)) == B.reserve.pick(B.Fit{j, c0}, u, p, id, now, base, keep, step, f, s, l, o, h, un) : B.Grant}:
  match c0:
    case B.Ask{x, m}:
      {==}

def bsl.held(hd: Bool, +u: B.Use, +p: B.Phase, +id: Nat, +now: Nat, +base: B.Ask, +keep: B.Ask, +step: B.Ask, +want: B.Ask, +less: List<&2, B.Ask>, +f: B.Amt, +s: B.Amt, +l: B.Amt, +o: B.Amt, +h: List<&2, B.Hold>, +un: Nat, +c0: B.Ask, +rest: List<&2, B.Ask>, +j: Nat, e: {S.nth(j, want <> less) == Some{c0} : Maybe<&2, B.Ask>}, nb: {S.none_fit(u, base, keep, S.before(j, want <> less), f, now, un) == True{} : Bool}, fc: {S.fits(u, base, keep, c0, f, now, un) == True{} : Bool}) -> {BudgetShare.ss_shift(j, B.reserve.held(hd, u, p, id, now, base, keep, step, c0, rest, f, s, l, o, h, un)) == B.reserve.held(hd, u, p, id, now, base, keep, step, want, less, f, s, l, o, h, un) : B.Grant}:
  match hd:
    case True{}:
      {==}
    case False{}:
      +fc0 = fc
      %Equal.sym(B.Pick, B.pick(rest, u, base, keep, f, now, un, c0, 0n), B.Fit{0n, c0}, bsl.pick_c0(rest, u, base, keep, f, now, un, c0, fc0)) : {BudgetShare.ss_shift(j, B.reserve.pick(_, u, p, id, now, base, keep, step, f, s, l, o, h, un)) == B.reserve.pick(B.pick(less, u, base, keep, f, now, un, want, 0n), u, p, id, now, base, keep, step, f, s, l, o, h, un) : B.Grant}
      %Equal.sym(B.Pick, B.pick(less, u, base, keep, f, now, un, want, 0n), B.Fit{j, c0}, bsl.pick_eq(B.pick(less, u, base, keep, f, now, un, want, 0n), u, base, keep, f, now, un, want, less, j, c0, BR.br.pick_ok(less, u, base, keep, f, now, un, want), e, nb, fc0)) : {BudgetShare.ss_shift(j, B.reserve.pick(B.Fit{0n, c0}, u, p, id, now, base, keep, step, f, s, l, o, h, un)) == B.reserve.pick(_, u, p, id, now, base, keep, step, f, s, l, o, h, un) : B.Grant}
      bsl.grant_eq(c0, j, u, p, id, now, base, keep, step, f, s, l, o, h, un)

def bsl.open(okb: Bool, +u: B.Use, +p: B.Phase, +id: Nat, +now: Nat, +base: B.Ask, +keep: B.Ask, +step: B.Ask, +want: B.Ask, +less: List<&2, B.Ask>, +f: B.Amt, +s: B.Amt, +l: B.Amt, +o: B.Amt, +h: List<&2, B.Hold>, +un: Nat, +c0: B.Ask, +rest: List<&2, B.Ask>, +j: Nat, e: {S.nth(j, want <> less) == Some{c0} : Maybe<&2, B.Ask>}, nb: {S.none_fit(u, base, keep, S.before(j, want <> less), f, now, un) == True{} : Bool}, fc: {S.fits(u, base, keep, c0, f, now, un) == True{} : Bool}) -> {BudgetShare.ss_shift(j, B.reserve.open(okb, u, p, id, now, base, keep, step, c0, rest, f, s, l, o, h, un)) == B.reserve.open(okb, u, p, id, now, base, keep, step, want, less, f, s, l, o, h, un) : B.Grant}:
  match okb:
    case True{}:
      bsl.held(B.held(id, h), u, p, id, now, base, keep, step, want, less, f, s, l, o, h, un, c0, rest, j, e, nb, fc)
    case False{}:
      {==}

# from c0, the first offer that fits, at place j: the same answer
def bsl.acct(a: B.Acct, +u: B.Use, +p: B.Phase, +id: Nat, +now: Nat, +base: B.Ask, +keep: B.Ask, +step: B.Ask, +want: B.Ask, +less: List<&2, B.Ask>, +c0: B.Ask, +rest: List<&2, B.Ask>, +j: Nat, e: {S.nth(j, want <> less) == Some{c0} : Maybe<&2, B.Ask>}, nb: {S.none_fit(u, base, keep, S.before(j, want <> less), S.free(a), now, S.until(a)) == True{} : Bool}, fc: {S.fits(u, base, keep, c0, S.free(a), now, S.until(a)) == True{} : Bool}) -> {BudgetShare.ss_shift(j, B.reserve(u, p, id, now, base, keep, step, c0, rest, a)) == B.reserve(u, p, id, now, base, keep, step, want, less, a) : B.Grant}:
  match a:
    case B.Acct{+f, +s, +l, +o, +h, +un}:
      bsl.open(B.allows(p, u), u, p, id, now, base, keep, step, want, less, f, s, l, o, h, un, c0, rest, j, e, nb, fc)

# the claim from place j
def bsl.Same(+j: Nat, +u: B.Use, +p: B.Phase, +id: Nat, +now: Nat, +base: B.Ask, +keep: B.Ask, +step: B.Ask, +want: B.Ask, +less: List<&2, B.Ask>, +a: B.Acct) -> Type:
  {BudgetShare.ss_shift(j, B.reserve(u, p, id, now, base, keep, step, BudgetShare.ss_offer(j, want, less), BudgetShare.ss_after(j, want <> less), a)) == B.reserve(u, p, id, now, base, keep, step, want, less, a) : B.Grant}

def bsl.m(m: Maybe<&2, B.Ask>, +j: Nat, +u: B.Use, +p: B.Phase, +id: Nat, +now: Nat, +base: B.Ask, +keep: B.Ask, +step: B.Ask, +want: B.Ask, +less: List<&2, B.Ask>, +a: B.Acct, em: {S.nth(j, want <> less) == m : Maybe<&2, B.Ask>}, ff: {BudgetShare.ss_mfits(u, base, keep, m, S.free(a), now, S.until(a)) == True{} : Bool} & {S.none_fit(u, base, keep, S.before(j, want <> less), S.free(a), now, S.until(a)) == True{} : Bool}) -> bsl.Same(j, u, p, id, now, base, keep, step, want, less, a):
  match m:
    case None{}:
      (fa, fb) = ff
      BR.br.absurd(bsl.Same(j, u, p, id, now, base, keep, step, want, less, a), fa)
    case Some{+c0}:
      (fa, fb) = ff
      +em0 = em
      %Equal.sym(Maybe<&2, B.Ask>, S.nth(j, want <> less), Some{c0}, em0) : {BudgetShare.ss_shift(j, B.reserve(u, p, id, now, base, keep, step, BudgetShare.ss_offer.of(_, want), BudgetShare.ss_after(j, want <> less), a)) == B.reserve(u, p, id, now, base, keep, step, want, less, a) : B.Grant}
      bsl.acct(a, u, p, id, now, base, keep, step, want, less, c0, BudgetShare.ss_after(j, want <> less), j, em0, fb, fa)

def bsl.top(b: Bool, +n: Nat, +use: B.Use, +p: B.Phase, +id: Nat, +now: Nat, +base: B.Ask, +keep: B.Ask, +step: B.Ask, +want: B.Ask, +less: List<&2, B.Ask>, +a: B.Acct, plain: {BudgetShare.ss_unshared(n, use) == True{} : Bool}, eb: {S.none_fit(use, base, keep, want <> less, S.free(a), now, S.until(a)) == b : Bool}) -> bsl.Same(Bs.start(n, use, base, keep, want, less, S.free(a), now, S.until(a)), use, p, id, now, base, keep, step, want, less, a):
  match b:
    case True{}:
      +e0 = eb
      +z = BSM.bsm.nf0(Bs.first(want <> less, n, use, base, keep, S.free(a), now, S.until(a)), Bs.last(want <> less, use, base, keep, S.free(a), now, S.until(a)), n, use, base, keep, S.free(a), now, S.until(a), want <> less, BSM.bsm.first_ok(want <> less, n, use, base, keep, S.free(a), now, S.until(a)), BSM.bsm.last_ok(want <> less, use, base, keep, S.free(a), now, S.until(a)), e0)
      %Equal.sym(Nat, Bs.start(n, use, base, keep, want, less, S.free(a), now, S.until(a)), 0n, z) : bsl.Same(_, use, p, id, now, base, keep, step, want, less, a)
      bsl.shift0(B.reserve(use, p, id, now, base, keep, step, want, less, a))
    case False{}:
      bsl.m(S.nth(Bs.start(n, use, base, keep, want, less, S.free(a), now, S.until(a)), want <> less), Bs.start(n, use, base, keep, want, less, S.free(a), now, S.until(a)), use, p, id, now, base, keep, step, want, less, a, {==}, BSM.bsm.ff(Bs.first(want <> less, n, use, base, keep, S.free(a), now, S.until(a)), Bs.last(want <> less, use, base, keep, S.free(a), now, S.until(a)), n, use, base, keep, S.free(a), now, S.until(a), want <> less, BSM.bsm.first_ok(want <> less, n, use, base, keep, S.free(a), now, S.until(a)), plain, eb))

def BudgetShare.budget_share_lone_identical(n, use, p, id, now, base, keep, step, want, less, a, plain):
  bsl.top(S.none_fit(use, base, keep, want <> less, S.free(a), now, S.until(a)), n, use, p, id, now, base, keep, step, want, less, a, plain, {==})
