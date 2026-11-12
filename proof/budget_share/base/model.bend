# eukhe: lemmas of the proofs of area budget_share (bend/budget_share.bend
# against laws/budget_share.bend and spec/budget/ledger.bend): the code's
# fit, share and test are the spec's (bsm.fits, bsm.within, bsm.ok), the
# first and the last scans find what the spec says (bsm.first_ok,
# bsm.last_ok), and what the start is in each case (bsm.fw, bsm.sf,
# bsm.nf0, bsm.ff, bsm.start_fits)

import Base
import ../../../bend/budget.bend as B
import ../../../bend/budget_share.bend as Bs
import ../../../spec/budget/ledger.bend as S
import ../../../laws/budget_share.bend as BudgetShare
import ../../budget/base/reserve.bend as BR
import ./arith.bend as BSA

# Logic
# -----

# b is False and True: False is True
def bsm.false_true(-b: Bool, e1: {b == False{} : Bool}, e2: {b == True{} : Bool}) -> {False{} == True{} : Bool}:
  Equal.trans(Bool, False{}, b, True{}, Equal.sym(Bool, b, False{}, e1), e2)

def bsm.not_not(b: Bool) -> {Bool.not(Bool.not(b)) == b : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

# The test of one offer
# ---------------------

def bsm.fits_of(l: Maybe<&2, B.Dim>) -> {Bs.fits.of(l) == Bool.not(B.low.of(l)) : Bool}:
  match l:
    case None{}:
      {==}
    case Some{d}:
      {==}

# the code's fit is the spec's
def bsm.fits(+u: B.Use, +base: B.Ask, +keep: B.Ask, +c: B.Ask, +f: B.Amt, +now: Nat, +un: Nat) -> {Bs.fits(u, base, keep, c, f, now, un) == S.fits(u, base, keep, c, f, now, un) : Bool}:
  +l = B.lack(B.need(u, base, keep, c), f, now, un)
  +sf = S.fits(u, base, keep, c, f, now, un)
  Equal.trans(Bool, Bs.fits.of(l), Bool.not(B.low.of(l)), sf, bsm.fits_of(l), Equal.trans(Bool, Bool.not(B.low.of(l)), Bool.not(Bool.not(sf)), sf, Equal.cong(Bool, Bool, z => Bool.not(z), B.low.of(l), Bool.not(sf), BR.br.low_fits(u, base, keep, c, f, now, un)), bsm.not_not(sf)))

# the code's share of a shared use is the spec's, in money and in tokens
def bsm.share(u: B.Use, base: B.Ask, keep: B.Ask, c: B.Ask, f: B.Amt, n: Nat, w: {BudgetShare.ss_shared(u) == True{} : Bool}) -> {Bs.share(n, u, base, keep, c, f) == Bool.and(BudgetShare.ss_share_in(n, B.Cost{}, base, keep, f, c), BudgetShare.ss_share_in(n, B.Tok{}, base, keep, f, c)) : Bool}:
  match u:
    case B.Work{}:
      match base:
        case B.Ask{bx, bm}:
          match bx:
            case B.Amt{b1, b2, b3, b4}:
              match keep:
                case B.Ask{kx, km}:
                  match kx:
                    case B.Amt{k1, k2, k3, k4}:
                      match c:
                        case B.Ask{cx, cm}:
                          match cx:
                            case B.Amt{c1, c2, c3, c4}:
                              match f:
                                case B.Amt{f1, f2, f3, f4}:
                                  match n:
                                    case 0n:
                                      {==}
                                    case 1n+p:
                                      match p:
                                        case 0n:
                                          {==}
                                        case 1n+q:
                                          {==}
    case B.Final{}:
      BR.br.absurd({Bs.share(n, B.Final{}, base, keep, c, f) == Bool.and(BudgetShare.ss_share_in(n, B.Cost{}, base, keep, f, c), BudgetShare.ss_share_in(n, B.Tok{}, base, keep, f, c)) : Bool}, w)
    case B.Side{}:
      match base:
        case B.Ask{bx, bm}:
          match bx:
            case B.Amt{b1, b2, b3, b4}:
              match keep:
                case B.Ask{kx, km}:
                  match kx:
                    case B.Amt{k1, k2, k3, k4}:
                      match c:
                        case B.Ask{cx, cm}:
                          match cx:
                            case B.Amt{c1, c2, c3, c4}:
                              match f:
                                case B.Amt{f1, f2, f3, f4}:
                                  match n:
                                    case 0n:
                                      {==}
                                    case 1n+p:
                                      match p:
                                        case 0n:
                                          {==}
                                        case 1n+q:
                                          {==}

# the code's within is the spec's
def bsm.within(+n: Nat, u: B.Use, +base: B.Ask, +keep: B.Ask, +c: B.Ask, +f: B.Amt) -> {Bs.within(n, u, base, keep, c, f) == BudgetShare.ss_within(n, u, base, keep, f, c) : Bool}:
  match u:
    case B.Work{}:
      bsm.share(B.Work{}, base, keep, c, f, n, {==})
    case B.Final{}:
      {==}
    case B.Side{}:
      bsm.share(B.Side{}, base, keep, c, f, n, {==})

# the code's test of an offer is the spec's
def bsm.ok(+n: Nat, +u: B.Use, +base: B.Ask, +keep: B.Ask, +c: B.Ask, +f: B.Amt, +now: Nat, +un: Nat) -> {Bs.ok(n, u, base, keep, c, f, now, un) == BudgetShare.ss_ok(n, u, base, keep, c, f, now, un) : Bool}:
  %Equal.sym(Bool, Bs.fits(u, base, keep, c, f, now, un), S.fits(u, base, keep, c, f, now, un), bsm.fits(u, base, keep, c, f, now, un)) : {Bool.and(_, Bs.within(n, u, base, keep, c, f)) == BudgetShare.ss_ok(n, u, base, keep, c, f, now, un) : Bool}
  %Equal.sym(Bool, Bs.within(n, u, base, keep, c, f), BudgetShare.ss_within(n, u, base, keep, f, c), bsm.within(n, u, base, keep, c, f)) : {Bool.and(S.fits(u, base, keep, c, f, now, un), _) == BudgetShare.ss_ok(n, u, base, keep, c, f, now, un) : Bool}
  {==}

# The scans
# ---------

# what the first scan's answer m says of the offers xs
def bsm.FirstP(m: Maybe<&2, Nat>, +n: Nat, +u: B.Use, +base: B.Ask, +keep: B.Ask, +f: B.Amt, +now: Nat, +un: Nat, +xs: List<&2, B.Ask>) -> Type:
  match m:
    case Some{+j}:
      {BudgetShare.ss_mok(n, u, base, keep, S.nth(j, xs), f, now, un) == True{} : Bool} & {BudgetShare.ss_none_ok(n, u, base, keep, S.before(j, xs), f, now, un) == True{} : Bool}
    case None{}:
      {BudgetShare.ss_none_ok(n, u, base, keep, xs, f, now, un) == True{} : Bool}

def bsm.first_or(b: Bool, r: Maybe<&2, Nat>, +n: Nat, +u: B.Use, +base: B.Ask, +keep: B.Ask, +f: B.Amt, +now: Nat, +un: Nat, +c: B.Ask, +t: List<&2, B.Ask>, eb: {BudgetShare.ss_ok(n, u, base, keep, c, f, now, un) == b : Bool}, ih: bsm.FirstP(r, n, u, base, keep, f, now, un, t)) -> bsm.FirstP(Bs.first.or(b, r), n, u, base, keep, f, now, un, c <> t):
  match b:
    case True{}:
      (eb, {==})
    case False{}:
      match r:
        case Some{+j}:
          (fa, fb) = ih
          (fa, BR.br.nf_cons(BudgetShare.ss_ok(n, u, base, keep, c, f, now, un), BudgetShare.ss_none_ok(n, u, base, keep, S.before(j, t), f, now, un), eb, fb))
        case None{}:
          BR.br.nf_cons(BudgetShare.ss_ok(n, u, base, keep, c, f, now, un), BudgetShare.ss_none_ok(n, u, base, keep, t, f, now, un), eb, ih)

# the first scan finds the first offer that fits and is within the share
def bsm.first_ok(xs: List<&2, B.Ask>, +n: Nat, +u: B.Use, +base: B.Ask, +keep: B.Ask, +f: B.Amt, +now: Nat, +un: Nat) -> bsm.FirstP(Bs.first(xs, n, u, base, keep, f, now, un), n, u, base, keep, f, now, un, xs):
  match xs:
    case Nil{}:
      {==}
    case Con{+c, +t}:
      bsm.first_or(Bs.ok(n, u, base, keep, c, f, now, un), Bs.first(t, n, u, base, keep, f, now, un), n, u, base, keep, f, now, un, c, t, Equal.sym(Bool, Bs.ok(n, u, base, keep, c, f, now, un), BudgetShare.ss_ok(n, u, base, keep, c, f, now, un), bsm.ok(n, u, base, keep, c, f, now, un)), bsm.first_ok(t, n, u, base, keep, f, now, un))

# what the last scan's answer m says of the offers xs
def bsm.LastP(m: Maybe<&2, Nat>, +u: B.Use, +base: B.Ask, +keep: B.Ask, +f: B.Amt, +now: Nat, +un: Nat, +xs: List<&2, B.Ask>) -> Type:
  match m:
    case Some{+j}:
      {BudgetShare.ss_mfits(u, base, keep, S.nth(j, xs), f, now, un) == True{} : Bool} & {S.none_fit(u, base, keep, BudgetShare.ss_after(j, xs), f, now, un) == True{} : Bool}
    case None{}:
      {S.none_fit(u, base, keep, xs, f, now, un) == True{} : Bool}

def bsm.last_or(r: Maybe<&2, Nat>, b: Bool, +u: B.Use, +base: B.Ask, +keep: B.Ask, +f: B.Amt, +now: Nat, +un: Nat, +c: B.Ask, +t: List<&2, B.Ask>, eb: {S.fits(u, base, keep, c, f, now, un) == b : Bool}, ih: bsm.LastP(r, u, base, keep, f, now, un, t)) -> bsm.LastP(Bs.last.or(r, b), u, base, keep, f, now, un, c <> t):
  match r:
    case Some{j}:
      ih
    case None{}:
      match b:
        case True{}:
          (eb, ih)
        case False{}:
          BR.br.nf_cons(S.fits(u, base, keep, c, f, now, un), S.none_fit(u, base, keep, t, f, now, un), eb, ih)

# the last scan finds the last offer that fits
def bsm.last_ok(xs: List<&2, B.Ask>, +u: B.Use, +base: B.Ask, +keep: B.Ask, +f: B.Amt, +now: Nat, +un: Nat) -> bsm.LastP(Bs.last(xs, u, base, keep, f, now, un), u, base, keep, f, now, un, xs):
  match xs:
    case Nil{}:
      {==}
    case Con{+c, +t}:
      bsm.last_or(Bs.last(t, u, base, keep, f, now, un), Bs.fits(u, base, keep, c, f, now, un), u, base, keep, f, now, un, c, t, Equal.sym(Bool, Bs.fits(u, base, keep, c, f, now, un), S.fits(u, base, keep, c, f, now, un), bsm.fits(u, base, keep, c, f, now, un)), bsm.last_ok(t, u, base, keep, f, now, un))

# Places
# ------

# no offer is ok: the offer at any place is not
def bsm.no_mok(j: Nat, xs: List<&2, B.Ask>, +n: Nat, +u: B.Use, +base: B.Ask, +keep: B.Ask, +f: B.Amt, +now: Nat, +un: Nat, h: {BudgetShare.ss_none_ok(n, u, base, keep, xs, f, now, un) == True{} : Bool}) -> {BudgetShare.ss_mok(n, u, base, keep, S.nth(j, xs), f, now, un) == False{} : Bool}:
  match j:
    case 0n:
      match xs:
        case Nil{}:
          {==}
        case Con{+y, +t}:
          BR.br.not_true(BudgetShare.ss_ok(n, u, base, keep, y, f, now, un), BR.br.and_l(Bool.not(BudgetShare.ss_ok(n, u, base, keep, y, f, now, un)), BudgetShare.ss_none_ok(n, u, base, keep, t, f, now, un), h))
    case 1n+k:
      match xs:
        case Nil{}:
          {==}
        case Con{+y, +t}:
          bsm.no_mok(k, t, n, u, base, keep, f, now, un, BR.br.and_r(Bool.not(BudgetShare.ss_ok(n, u, base, keep, y, f, now, un)), BudgetShare.ss_none_ok(n, u, base, keep, t, f, now, un), h))

# no offer fits: the offer at any place does not
def bsm.no_mfits(j: Nat, xs: List<&2, B.Ask>, +u: B.Use, +base: B.Ask, +keep: B.Ask, +f: B.Amt, +now: Nat, +un: Nat, h: {S.none_fit(u, base, keep, xs, f, now, un) == True{} : Bool}) -> {BudgetShare.ss_mfits(u, base, keep, S.nth(j, xs), f, now, un) == False{} : Bool}:
  match j:
    case 0n:
      match xs:
        case Nil{}:
          {==}
        case Con{+y, +t}:
          BR.br.not_true(S.fits(u, base, keep, y, f, now, un), BR.br.and_l(Bool.not(S.fits(u, base, keep, y, f, now, un)), S.none_fit(u, base, keep, t, f, now, un), h))
    case 1n+k:
      match xs:
        case Nil{}:
          {==}
        case Con{+y, +t}:
          bsm.no_mfits(k, t, u, base, keep, f, now, un, BR.br.and_r(Bool.not(S.fits(u, base, keep, y, f, now, un)), S.none_fit(u, base, keep, t, f, now, un), h))

# an offer that is ok fits
def bsm.mok_mfits(m: Maybe<&2, B.Ask>, +n: Nat, +u: B.Use, +base: B.Ask, +keep: B.Ask, +f: B.Amt, +now: Nat, +un: Nat, h: {BudgetShare.ss_mok(n, u, base, keep, m, f, now, un) == True{} : Bool}) -> {BudgetShare.ss_mfits(u, base, keep, m, f, now, un) == True{} : Bool}:
  match m:
    case None{}:
      h
    case Some{+x}:
      BR.br.and_l(S.fits(u, base, keep, x, f, now, un), BudgetShare.ss_within(n, u, base, keep, f, x), h)

# The start
# ---------

# some offer is ok: the start's is, and none before it
def bsm.fw(fm: Maybe<&2, Nat>, lm: Maybe<&2, Nat>, +n: Nat, +u: B.Use, +base: B.Ask, +keep: B.Ask, +f: B.Amt, +now: Nat, +un: Nat, +xs: List<&2, B.Ask>, fp: bsm.FirstP(fm, n, u, base, keep, f, now, un, xs), some: {BudgetShare.ss_none_ok(n, u, base, keep, xs, f, now, un) == False{} : Bool}) -> {BudgetShare.ss_mok(n, u, base, keep, S.nth(Bs.start.pick(fm, lm), xs), f, now, un) == True{} : Bool} & {BudgetShare.ss_none_ok(n, u, base, keep, S.before(Bs.start.pick(fm, lm), xs), f, now, un) == True{} : Bool}:
  match fm:
    case Some{j}:
      fp
    case None{}:
      BR.br.absurd({BudgetShare.ss_mok(n, u, base, keep, S.nth(Bs.start.pick(None{}, lm), xs), f, now, un) == True{} : Bool} & {BudgetShare.ss_none_ok(n, u, base, keep, S.before(Bs.start.pick(None{}, lm), xs), f, now, un) == True{} : Bool}, bsm.false_true(BudgetShare.ss_none_ok(n, u, base, keep, xs, f, now, un), some, fp))

# none is ok, some fits: the start's fits, and none after it
def bsm.sf(fm: Maybe<&2, Nat>, lm: Maybe<&2, Nat>, +n: Nat, +u: B.Use, +base: B.Ask, +keep: B.Ask, +f: B.Amt, +now: Nat, +un: Nat, +xs: List<&2, B.Ask>, fp: bsm.FirstP(fm, n, u, base, keep, f, now, un, xs), lp: bsm.LastP(lm, u, base, keep, f, now, un, xs), none: {BudgetShare.ss_none_ok(n, u, base, keep, xs, f, now, un) == True{} : Bool}, some: {S.none_fit(u, base, keep, xs, f, now, un) == False{} : Bool}) -> {BudgetShare.ss_mfits(u, base, keep, S.nth(Bs.start.pick(fm, lm), xs), f, now, un) == True{} : Bool} & {S.none_fit(u, base, keep, BudgetShare.ss_after(Bs.start.pick(fm, lm), xs), f, now, un) == True{} : Bool}:
  match fm:
    case Some{+j}:
      (fa, fb) = fp
      BR.br.absurd({BudgetShare.ss_mfits(u, base, keep, S.nth(j, xs), f, now, un) == True{} : Bool} & {S.none_fit(u, base, keep, BudgetShare.ss_after(j, xs), f, now, un) == True{} : Bool}, bsm.false_true(BudgetShare.ss_mok(n, u, base, keep, S.nth(j, xs), f, now, un), bsm.no_mok(j, xs, n, u, base, keep, f, now, un, none), fa))
    case None{}:
      match lm:
        case Some{j}:
          lp
        case None{}:
          BR.br.absurd({BudgetShare.ss_mfits(u, base, keep, S.nth(0n, xs), f, now, un) == True{} : Bool} & {S.none_fit(u, base, keep, BudgetShare.ss_after(0n, xs), f, now, un) == True{} : Bool}, bsm.false_true(S.none_fit(u, base, keep, xs, f, now, un), some, lp))

# none fits: the start is 0
def bsm.nf0(fm: Maybe<&2, Nat>, lm: Maybe<&2, Nat>, +n: Nat, +u: B.Use, +base: B.Ask, +keep: B.Ask, +f: B.Amt, +now: Nat, +un: Nat, +xs: List<&2, B.Ask>, fp: bsm.FirstP(fm, n, u, base, keep, f, now, un, xs), lp: bsm.LastP(lm, u, base, keep, f, now, un, xs), none: {S.none_fit(u, base, keep, xs, f, now, un) == True{} : Bool}) -> {Bs.start.pick(fm, lm) == 0n : Nat}:
  match fm:
    case Some{+j}:
      (fa, fb) = fp
      BR.br.absurd({j == 0n : Nat}, bsm.false_true(BudgetShare.ss_mfits(u, base, keep, S.nth(j, xs), f, now, un), bsm.no_mfits(j, xs, u, base, keep, f, now, un, none), bsm.mok_mfits(S.nth(j, xs), n, u, base, keep, f, now, un, fa)))
    case None{}:
      match lm:
        case Some{+j}:
          (la, lb) = lp
          BR.br.absurd({j == 0n : Nat}, bsm.false_true(BudgetShare.ss_mfits(u, base, keep, S.nth(j, xs), f, now, un), bsm.no_mfits(j, xs, u, base, keep, f, now, un, none), la))
        case None{}:
          {==}

# some fits: the start's offer fits
def bsm.start_fits(fm: Maybe<&2, Nat>, lm: Maybe<&2, Nat>, +n: Nat, +u: B.Use, +base: B.Ask, +keep: B.Ask, +f: B.Amt, +now: Nat, +un: Nat, +xs: List<&2, B.Ask>, fp: bsm.FirstP(fm, n, u, base, keep, f, now, un, xs), lp: bsm.LastP(lm, u, base, keep, f, now, un, xs), some: {S.none_fit(u, base, keep, xs, f, now, un) == False{} : Bool}) -> {BudgetShare.ss_mfits(u, base, keep, S.nth(Bs.start.pick(fm, lm), xs), f, now, un) == True{} : Bool}:
  match fm:
    case Some{+j}:
      (fa, fb) = fp
      bsm.mok_mfits(S.nth(j, xs), n, u, base, keep, f, now, un, fa)
    case None{}:
      match lm:
        case Some{j}:
          (la, lb) = lp
          la
        case None{}:
          BR.br.absurd({BudgetShare.ss_mfits(u, base, keep, S.nth(0n, xs), f, now, un) == True{} : Bool}, bsm.false_true(S.none_fit(u, base, keep, xs, f, now, un), some, lp))

# A lone agent, a final answer
# ----------------------------

def bsm.plain_one(u: B.Use) -> {BudgetShare.ss_unshared(1n, u) == True{} : Bool}:
  match u:
    case B.Work{}:
      {==}
    case B.Final{}:
      {==}
    case B.Side{}:
      {==}

# max(1 + m, 1) = 1 + m
def bsm.max_succ(m: Nat) -> {Nat.max(1n+m, 1n) == 1n+m : Nat}:
  match m:
    case 0n:
      {==}
    case 1n+q:
      {==}

# an ask that fits, alone, is within the whole of what is free past the
# reserves in dimension d
def bsm.share_one(+d: B.Dim, +base: B.Ask, +keep: B.Ask, +f: B.Amt, +x: B.Ask, fd: {S.fits_in(B.Work{}, base, keep, x, f, d) == True{} : Bool}) -> {BudgetShare.ss_share_in(1n, d, base, keep, f, x) == True{} : Bool}:
  +xa = S.at(d, S.amt(x))
  +bk = Nat.add(S.at(d, S.amt(base)), S.at(d, S.amt(keep)))
  +fa = S.at(d, f)
  %Equal.sym(Nat, Nat.div(Nat.sub(fa, bk), 1n), Nat.sub(fa, bk), BSA.bsa.div_one(Nat.sub(fa, bk))) : {Nat.is_le(xa, _) == True{} : Bool}
  BR.br.le_sub(bk, fa, xa, Equal.trans(Bool, Nat.is_le(Nat.add(bk, xa), fa), Nat.is_le(Nat.add(xa, bk), fa), True{}, Equal.cong(Nat, Bool, z => Nat.is_le(z, fa), Nat.add(bk, xa), Nat.add(xa, bk), BR.br.add_comm(bk, xa)), fd))

# a plain test: an offer that fits is within the share
def bsm.within_plain(n: Nat, u: B.Use, +base: B.Ask, +keep: B.Ask, +x: B.Ask, +f: B.Amt, +now: Nat, +un: Nat, h: {BudgetShare.ss_unshared(n, u) == True{} : Bool}, fx: {S.fits(u, base, keep, x, f, now, un) == True{} : Bool}) -> {BudgetShare.ss_within(n, u, base, keep, f, x) == True{} : Bool}:
  match n:
    case 0n:
      match u:
        case B.Work{}:
          BR.br.absurd({BudgetShare.ss_within(0n, B.Work{}, base, keep, f, x) == True{} : Bool}, h)
        case B.Final{}:
          {==}
        case B.Side{}:
          BR.br.absurd({BudgetShare.ss_within(0n, B.Side{}, base, keep, f, x) == True{} : Bool}, h)
    case 1n+p:
      match p:
        case 0n:
          match u:
            case B.Work{}:
              +fx0 = fx
              BR.br.and_t(BudgetShare.ss_share_in(1n, B.Cost{}, base, keep, f, x), BudgetShare.ss_share_in(1n, B.Tok{}, base, keep, f, x), bsm.share_one(B.Cost{}, base, keep, f, x, BR.br.fits_at(B.Cost{}, B.Work{}, base, keep, x, f, now, un, fx0)), bsm.share_one(B.Tok{}, base, keep, f, x, BR.br.fits_at(B.Tok{}, B.Work{}, base, keep, x, f, now, un, fx0)))
            case B.Final{}:
              {==}
            case B.Side{}:
              +fx0 = fx
              BR.br.and_t(BudgetShare.ss_share_in(1n, B.Cost{}, base, keep, f, x), BudgetShare.ss_share_in(1n, B.Tok{}, base, keep, f, x), bsm.share_one(B.Cost{}, base, keep, f, x, BR.br.fits_at(B.Cost{}, B.Side{}, base, keep, x, f, now, un, fx0)), bsm.share_one(B.Tok{}, base, keep, f, x, BR.br.fits_at(B.Tok{}, B.Side{}, base, keep, x, f, now, un, fx0)))
        case 1n+q:
          match u:
            case B.Work{}:
              BR.br.absurd({BudgetShare.ss_within(2n+q, B.Work{}, base, keep, f, x) == True{} : Bool}, h)
            case B.Final{}:
              {==}
            case B.Side{}:
              BR.br.absurd({BudgetShare.ss_within(2n+q, B.Side{}, base, keep, f, x) == True{} : Bool}, h)

def bsm.ok_plain.at(b: Bool, +n: Nat, +u: B.Use, +base: B.Ask, +keep: B.Ask, +x: B.Ask, +f: B.Amt, +now: Nat, +un: Nat, h: {BudgetShare.ss_unshared(n, u) == True{} : Bool}, eb: {S.fits(u, base, keep, x, f, now, un) == b : Bool}) -> {Bool.and(S.fits(u, base, keep, x, f, now, un), BudgetShare.ss_within(n, u, base, keep, f, x)) == S.fits(u, base, keep, x, f, now, un) : Bool}:
  match b:
    case True{}:
      +e0 = eb
      %Equal.sym(Bool, S.fits(u, base, keep, x, f, now, un), True{}, e0) : {Bool.and(_, BudgetShare.ss_within(n, u, base, keep, f, x)) == _ : Bool}
      bsm.within_plain(n, u, base, keep, x, f, now, un, h, e0)
    case False{}:
      %Equal.sym(Bool, S.fits(u, base, keep, x, f, now, un), False{}, eb) : {Bool.and(_, BudgetShare.ss_within(n, u, base, keep, f, x)) == _ : Bool}
      {==}

# a plain test of an offer is its fit
def bsm.ok_plain(+n: Nat, +u: B.Use, +base: B.Ask, +keep: B.Ask, +x: B.Ask, +f: B.Amt, +now: Nat, +un: Nat, h: {BudgetShare.ss_unshared(n, u) == True{} : Bool}) -> {BudgetShare.ss_ok(n, u, base, keep, x, f, now, un) == S.fits(u, base, keep, x, f, now, un) : Bool}:
  bsm.ok_plain.at(S.fits(u, base, keep, x, f, now, un), n, u, base, keep, x, f, now, un, h, {==})

def bsm.none_ok_plain(xs: List<&2, B.Ask>, +n: Nat, +u: B.Use, +base: B.Ask, +keep: B.Ask, +f: B.Amt, +now: Nat, +un: Nat, h: {BudgetShare.ss_unshared(n, u) == True{} : Bool}) -> {BudgetShare.ss_none_ok(n, u, base, keep, xs, f, now, un) == S.none_fit(u, base, keep, xs, f, now, un) : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+y, +t}:
      +h0 = h
      %Equal.sym(Bool, BudgetShare.ss_ok(n, u, base, keep, y, f, now, un), S.fits(u, base, keep, y, f, now, un), bsm.ok_plain(n, u, base, keep, y, f, now, un, h0)) : {Bool.and(Bool.not(_), BudgetShare.ss_none_ok(n, u, base, keep, t, f, now, un)) == Bool.and(Bool.not(S.fits(u, base, keep, y, f, now, un)), S.none_fit(u, base, keep, t, f, now, un)) : Bool}
      Equal.cong(Bool, Bool, z => Bool.and(Bool.not(S.fits(u, base, keep, y, f, now, un)), z), BudgetShare.ss_none_ok(n, u, base, keep, t, f, now, un), S.none_fit(u, base, keep, t, f, now, un), bsm.none_ok_plain(t, n, u, base, keep, f, now, un, h0))

def bsm.mok_plain(m: Maybe<&2, B.Ask>, +n: Nat, +u: B.Use, +base: B.Ask, +keep: B.Ask, +f: B.Amt, +now: Nat, +un: Nat, h: {BudgetShare.ss_unshared(n, u) == True{} : Bool}) -> {BudgetShare.ss_mok(n, u, base, keep, m, f, now, un) == BudgetShare.ss_mfits(u, base, keep, m, f, now, un) : Bool}:
  match m:
    case None{}:
      {==}
    case Some{+x}:
      bsm.ok_plain(n, u, base, keep, x, f, now, un, h)

# a plain test, some fits: the start is the first that fits
def bsm.ff(fm: Maybe<&2, Nat>, lm: Maybe<&2, Nat>, +n: Nat, +u: B.Use, +base: B.Ask, +keep: B.Ask, +f: B.Amt, +now: Nat, +un: Nat, +xs: List<&2, B.Ask>, fp: bsm.FirstP(fm, n, u, base, keep, f, now, un, xs), h: {BudgetShare.ss_unshared(n, u) == True{} : Bool}, some: {S.none_fit(u, base, keep, xs, f, now, un) == False{} : Bool}) -> {BudgetShare.ss_mfits(u, base, keep, S.nth(Bs.start.pick(fm, lm), xs), f, now, un) == True{} : Bool} & {S.none_fit(u, base, keep, S.before(Bs.start.pick(fm, lm), xs), f, now, un) == True{} : Bool}:
  match fm:
    case Some{+j}:
      (fa, fb) = fp
      +h0 = h
      (Equal.trans(Bool, BudgetShare.ss_mfits(u, base, keep, S.nth(j, xs), f, now, un), BudgetShare.ss_mok(n, u, base, keep, S.nth(j, xs), f, now, un), True{}, Equal.sym(Bool, BudgetShare.ss_mok(n, u, base, keep, S.nth(j, xs), f, now, un), BudgetShare.ss_mfits(u, base, keep, S.nth(j, xs), f, now, un), bsm.mok_plain(S.nth(j, xs), n, u, base, keep, f, now, un, h0)), fa), Equal.trans(Bool, S.none_fit(u, base, keep, S.before(j, xs), f, now, un), BudgetShare.ss_none_ok(n, u, base, keep, S.before(j, xs), f, now, un), True{}, Equal.sym(Bool, BudgetShare.ss_none_ok(n, u, base, keep, S.before(j, xs), f, now, un), S.none_fit(u, base, keep, S.before(j, xs), f, now, un), bsm.none_ok_plain(S.before(j, xs), n, u, base, keep, f, now, un, h0)), fb))
    case None{}:
      BR.br.absurd({BudgetShare.ss_mfits(u, base, keep, S.nth(Bs.start.pick(None{}, lm), xs), f, now, un) == True{} : Bool} & {S.none_fit(u, base, keep, S.before(Bs.start.pick(None{}, lm), xs), f, now, un) == True{} : Bool}, bsm.false_true(S.none_fit(u, base, keep, xs, f, now, un), some, Equal.trans(Bool, S.none_fit(u, base, keep, xs, f, now, un), BudgetShare.ss_none_ok(n, u, base, keep, xs, f, now, un), True{}, Equal.sym(Bool, BudgetShare.ss_none_ok(n, u, base, keep, xs, f, now, un), S.none_fit(u, base, keep, xs, f, now, un), bsm.none_ok_plain(xs, n, u, base, keep, f, now, un, h)), fp)))
