# eukhe: lemmas the proofs of area facts share

import Base
import ../../bend/facts.bend as Fx
import ../../bend/ffi_facts.bend as FFx
import ../../bend/wire.bend as Wr
import ../../laws/facts.bend as Facts
import ../../laws/base.bend as LawsBase
import ../base/bool/and.bend as LBoolAnd
import ../base/bool/misc.bend as LBoolMisc
import ../base/nat/is_le.bend as LNatIsLe
import ../base/wire.bend as LWire

# ---- facts ----

# proof_facts: proofs of LAWS.bend section model_facts (the model in
# bend/facts.bend). PROOF.bend proves each law as Laws.<law> with the
# pf.<law> of this file. The rulebook laws reuse the lookup lemmas of
# PROOF.bend section quirks.

# Nat order
# ---------

def facts.pf.le_refl(+n: Nat) -> {Nat.is_le(n, n) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      facts.pf.le_refl(p)

def facts.pf.le_succ(+n: Nat) -> {Nat.is_le(n, 1n+n) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      facts.pf.le_succ(p)

# a not below b: b is at most a
def pf.not_lt_le(+a: Nat, +b: Nat, h: {Nat.is_lt(a, b) == False{} : Bool}) -> {Nat.is_le(b, a) == True{} : Bool}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      LBoolMisc.pq.absurd({Nat.is_le(1n+q, 0n) == True{} : Bool}, h)
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      pf.not_lt_le(p, q, h)

def pf.le_trans(+a: Nat, +b: Nat, +c: Nat, ab: {Nat.is_le(a, b) == True{} : Bool}, bc: {Nat.is_le(b, c) == True{} : Bool}) -> {Nat.is_le(a, c) == True{} : Bool}:
  match a b c:
    case 0n b c:
      LNatIsLe.pq.le0(c)
    case 1n+p 0n c:
      LBoolMisc.pq.absurdF({Nat.is_le(1n+p, c) == True{} : Bool}, ab)
    case 1n+p 1n+q 0n:
      LBoolMisc.pq.absurdF({Nat.is_le(1n+p, 0n) == True{} : Bool}, bc)
    case 1n+p 1n+q 1n+r:
      pf.le_trans(p, q, r, ab, bc)

def pf.min_le_r(+x: Nat, +y: Nat) -> {Nat.is_le(Nat.min(x, y), y) == True{} : Bool}:
  match x y:
    case 0n y:
      LNatIsLe.pq.le0(y)
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      pf.min_le_r(p, q)

def pf.sub_le(+m: Nat, +a: Nat) -> {Nat.is_le(Nat.sub(m, a), m) == True{} : Bool}:
  match m a:
    case 0n a:
      {==}
    case 1n+p 0n:
      facts.pf.le_refl(1n+p)
    case 1n+p 1n+q:
      pf.le_trans(Nat.sub(p, q), p, 1n+p, pf.sub_le(p, q), facts.pf.le_succ(p))

# Budgets
# -------

# Budgets of the shipped core (fit, aux, Google)
# ---------------------------------------------

# the ceiling with a caller's cap is the sum, never above mm
def w2.cap_succ(c: Bool, +x: Nat, +q: Nat, +b: Nat) -> {Fx.fit.cap.add(c, 1n+x, 1n+q, b) == 1n+Fx.fit.cap.add(c, x, q, b) : Nat}:
  match c:
    case True{}:
      {==}
    case False{}:
      {==}

def w2.cap_succ0(c: Bool, +q: Nat, +p: Nat) -> {Fx.fit.cap.add(c, 0n, 1n+q, 1n+p) == 1n+Fx.fit.cap.add(c, 0n, q, p) : Nat}:
  match c:
    case True{}:
      {==}
    case False{}:
      {==}

def w2.cap_zero(+b: Nat, +mm: Nat) -> {Fx.fit.cap.add(Nat.is_lt(b, mm), 0n, mm, b) == Nat.min(b, mm) : Nat}:
  match b mm:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      %w2.cap_zero(p, q) : {Fx.fit.cap.add(Nat.is_lt(p, q), 0n, 1n+q, 1n+p) == 1n+_ : Nat}
      w2.cap_succ0(Nat.is_lt(p, q), q, p)

def w2.cap_sum(+x: Nat, +mm: Nat, +b: Nat) -> {Fx.fit.cap(Some{x}, mm, b) == Nat.min(Nat.add(x, b), mm) : Nat}:
  match x mm:
    case 0n mm:
      match mm:
        case 0n:
          w2.cap_zero(b, 0n)
        case 1n+q:
          w2.cap_zero(b, 1n+q)
    case 1n+p 0n:
      match b:
        case 0n:
          {==}
        case 1n+r:
          {==}
    case 1n+p 1n+q:
      %w2.cap_sum(p, q, b) : {Fx.fit.cap.add(Nat.is_lt(b, Nat.sub(q, p)), 1n+p, 1n+q, b) == 1n+_ : Nat}
      w2.cap_succ(Nat.is_lt(b, Nat.sub(q, p)), p, q, b)

def w2.fit_at(c: Bool, +m: Nat, +b: Nat, +a: Nat) -> {Fx.fit.at(c, m, b, a) == Facts.budgets.fit.at(c, m, b, a) : Fx.Fit}:
  match c:
    case True{}:
      {==}
    case False{}:
      {==}

def w2.lt_zero(+b: Nat) -> {Nat.is_lt(b, 0n) == False{} : Bool}:
  match b:
    case 0n:
      {==}
    case 1n+p:
      {==}

def w2.min_r(+b: Nat, +y: Nat, h: {Nat.is_le(y, b) == True{} : Bool}) -> {Nat.min(b, y) == y : Nat}:
  match b y:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      LBoolMisc.pq.absurdF({0n == 1n+q : Nat}, h)
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      %w2.min_r(p, q, h) : {1n+Nat.min(p, q) == 1n+_ : Nat}
      {==}

# the minimal budget of an ordered rule is at most its high budget
def pf.ord_mh(+b: Fx.Budgets, +ordered: {Fx.Budgets.ordered(b) == True{} : Bool}) -> {Nat.is_le(Fx.Budgets.minimal(b), Fx.Budgets.high(b)) == True{} : Bool}:
  match b:
    case Fx.Budgets{+mi, +lo, +me, +hi}:
      +ml = LBoolAnd.pq.and_l(Nat.is_le(mi, lo), Bool.and(Nat.is_le(lo, me), Nat.is_le(me, hi)), ordered)
      +rest = LBoolAnd.pq.and_r(Nat.is_le(mi, lo), Bool.and(Nat.is_le(lo, me), Nat.is_le(me, hi)), ordered)
      +lm = LBoolAnd.pq.and_l(Nat.is_le(lo, me), Nat.is_le(me, hi), rest)
      +mh = LBoolAnd.pq.and_r(Nat.is_le(lo, me), Nat.is_le(me, hi), rest)
      pf.le_trans(mi, lo, hi, ml, pf.le_trans(lo, me, hi, lm, mh))

def pc.f_mnat(+m: Maybe<&2, Nat>, +rest: String, h: {LawsBase.core_mfits(m) == True{} : Bool}) -> {Wr.Got{m, rest} == FFx.get_mnat(FFx.put_mnat(m, rest)) : Wr.Dec<Maybe<&2, Nat>>}:
  match m:
    case None{}:
      {==}
    case Some{+x}:
      %LWire.pc.nat(x, rest, h) : {Wr.Got{Some{x}, rest} == FFx.get_mnat.some(_) : Wr.Dec<Maybe<&2, Nat>>}
      {==}

# (facts)
# -------

# the seq of FFx reads back a then b (the two decoders in turn)
def pc.seqFFx(~A: Data, ~B: Data, ~get: String -> Wr.Dec<B>, +a: A, +r: String, +b: B, +r2: String, d: Wr.Dec<A>,
  h1: {Wr.Got{a, r} == d : Wr.Dec<A>}, h2: {Wr.Got{b, r2} == get(r) : Wr.Dec<B>}) ->
  {Wr.Got{FFx.P2{a, b}, r2} == FFx.seq(~A, ~B, ~get, d) : Wr.Dec<FFx.P2<A, B>>}:
  %h1 : {Wr.Got{FFx.P2{a, b}, r2} == FFx.seq(~A, ~B, ~get, _) : Wr.Dec<FFx.P2<A, B>>}
  %h2 : {Wr.Got{FFx.P2{a, b}, r2} == FFx.seq.fin(~A, ~B, a, _) : Wr.Dec<FFx.P2<A, B>>}
  {==}

# a Fx.ELv reads back
def pc.f_elv(+x: Fx.ELv, +rest: String) -> {Wr.Got{x, rest} == FFx.get_elv(FFx.put_elv(x, rest)) : Wr.Dec<Fx.ELv>}:
  match x:
    case Fx.EMinimal{}:
      {==}
    case Fx.ELow{}:
      {==}
    case Fx.EMedium{}:
      {==}
    case Fx.EHigh{}:
      {==}
    case Fx.EXhigh{}:
      {==}
    case Fx.EMax{}:
      {==}

# a Fx.Lv reads back
def pc.f_lv(+x: Fx.Lv, +rest: String) -> {Wr.Got{x, rest} == FFx.get_lv(FFx.put_lv(x, rest)) : Wr.Dec<Fx.Lv>}:
  match x:
    case Fx.Minimal{}:
      {==}
    case Fx.Low{}:
      {==}
    case Fx.Medium{}:
      {==}
    case Fx.High{}:
      {==}

# the user's budgets that fit read back
def pc.f_customs(+c: Fx.Customs, +rest: String, h: {Facts.core_customs_fit(c) == True{} : Bool}) -> {Wr.Got{c, rest} == FFx.get_customs(FFx.put_customs(c, rest)) : Wr.Dec<Fx.Customs>}:
  match c:
    case Fx.Customs{+mi, +lo, +me, +hi}:
      +hhh = h
      +hh0 = LBoolAnd.wr_and_r(LawsBase.core_mfits(mi), Bool.and(LawsBase.core_mfits(lo), Bool.and(LawsBase.core_mfits(me), LawsBase.core_mfits(hi))), hhh)
      +hh1 = LBoolAnd.wr_and_r(LawsBase.core_mfits(lo), Bool.and(LawsBase.core_mfits(me), LawsBase.core_mfits(hi)), hh0)
      +hh2 = LBoolAnd.wr_and_r(LawsBase.core_mfits(me), LawsBase.core_mfits(hi), hh1)
      +r3 = FFx.put_mnat(hi, rest)
      +r2 = FFx.put_mnat(me, r3)
      +r1 = FFx.put_mnat(lo, r2)
      +r0 = FFx.put_mnat(mi, r1)
      +d0 = FFx.get_mnat(r0)
      +e0 = pc.f_mnat(mi, r1, LBoolAnd.wr_and_l(LawsBase.core_mfits(mi), Bool.and(LawsBase.core_mfits(lo), Bool.and(LawsBase.core_mfits(me), LawsBase.core_mfits(hi))), hhh))
      +d1 = FFx.seq(~Maybe<&2, Nat>, ~Maybe<&2, Nat>, ~FFx.get_mnat, d0)
      +e1 = pc.seqFFx(~Maybe<&2, Nat>, ~Maybe<&2, Nat>, ~FFx.get_mnat, mi, r1, lo, r2, d0, e0, pc.f_mnat(lo, r2, LBoolAnd.wr_and_l(LawsBase.core_mfits(lo), Bool.and(LawsBase.core_mfits(me), LawsBase.core_mfits(hi)), hh0)))
      +d2 = FFx.seq(~FFx.P2<Maybe<&2, Nat>, Maybe<&2, Nat>>, ~Maybe<&2, Nat>, ~FFx.get_mnat, d1)
      +e2 = pc.seqFFx(~FFx.P2<Maybe<&2, Nat>, Maybe<&2, Nat>>, ~Maybe<&2, Nat>, ~FFx.get_mnat, FFx.P2{mi, lo}, r2, me, r3, d1, e1, pc.f_mnat(me, r3, LBoolAnd.wr_and_l(LawsBase.core_mfits(me), LawsBase.core_mfits(hi), hh1)))
      +d3 = FFx.seq(~FFx.P2<FFx.P2<Maybe<&2, Nat>, Maybe<&2, Nat>>, Maybe<&2, Nat>>, ~Maybe<&2, Nat>, ~FFx.get_mnat, d2)
      +e3 = pc.seqFFx(~FFx.P2<FFx.P2<Maybe<&2, Nat>, Maybe<&2, Nat>>, Maybe<&2, Nat>>, ~Maybe<&2, Nat>, ~FFx.get_mnat, FFx.P2{FFx.P2{mi, lo}, me}, r3, hi, rest, d2, e2, pc.f_mnat(hi, rest, hh2))
      %e3 : {Wr.Got{Fx.Customs{mi, lo, me, hi}, rest} == FFx.get_customs.of(_) : Wr.Dec<Fx.Customs>}
      {==}

# a budget table that fits reads back
def pc.f_budgets(+b: Fx.Budgets, +rest: String, h: {Facts.core_budgets_fit(b) == True{} : Bool}) -> {Wr.Got{b, rest} == FFx.get_budgets(FFx.put_budgets(b, rest)) : Wr.Dec<Fx.Budgets>}:
  match b:
    case Fx.Budgets{+mi, +lo, +me, +hi}:
      +hhh = h
      +hh0 = LBoolAnd.wr_and_r(LawsBase.wire_fits(mi), Bool.and(LawsBase.wire_fits(lo), Bool.and(LawsBase.wire_fits(me), LawsBase.wire_fits(hi))), hhh)
      +hh1 = LBoolAnd.wr_and_r(LawsBase.wire_fits(lo), Bool.and(LawsBase.wire_fits(me), LawsBase.wire_fits(hi)), hh0)
      +hh2 = LBoolAnd.wr_and_r(LawsBase.wire_fits(me), LawsBase.wire_fits(hi), hh1)
      +r3 = Wr.put_nat(hi, rest)
      +r2 = Wr.put_nat(me, r3)
      +r1 = Wr.put_nat(lo, r2)
      +r0 = Wr.put_nat(mi, r1)
      +d0 = Wr.get_nat(r0)
      +e0 = LWire.pc.nat(mi, r1, LBoolAnd.wr_and_l(LawsBase.wire_fits(mi), Bool.and(LawsBase.wire_fits(lo), Bool.and(LawsBase.wire_fits(me), LawsBase.wire_fits(hi))), hhh))
      +d1 = FFx.seq(~Nat, ~Nat, ~Wr.get_nat, d0)
      +e1 = pc.seqFFx(~Nat, ~Nat, ~Wr.get_nat, mi, r1, lo, r2, d0, e0, LWire.pc.nat(lo, r2, LBoolAnd.wr_and_l(LawsBase.wire_fits(lo), Bool.and(LawsBase.wire_fits(me), LawsBase.wire_fits(hi)), hh0)))
      +d2 = FFx.seq(~FFx.P2<Nat, Nat>, ~Nat, ~Wr.get_nat, d1)
      +e2 = pc.seqFFx(~FFx.P2<Nat, Nat>, ~Nat, ~Wr.get_nat, FFx.P2{mi, lo}, r2, me, r3, d1, e1, LWire.pc.nat(me, r3, LBoolAnd.wr_and_l(LawsBase.wire_fits(me), LawsBase.wire_fits(hi), hh1)))
      +d3 = FFx.seq(~FFx.P2<FFx.P2<Nat, Nat>, Nat>, ~Nat, ~Wr.get_nat, d2)
      +e3 = pc.seqFFx(~FFx.P2<FFx.P2<Nat, Nat>, Nat>, ~Nat, ~Wr.get_nat, FFx.P2{FFx.P2{mi, lo}, me}, r3, hi, rest, d2, e2, LWire.pc.nat(hi, rest, hh2))
      %e3 : {Wr.Got{Fx.Budgets{mi, lo, me, hi}, rest} == FFx.get_budgets.of(_) : Wr.Dec<Fx.Budgets>}
      {==}

# a Maybe<Budgets> that fits reads back
def pc.f_mbudgets(+m: Maybe<&2, Fx.Budgets>, +rest: String, h: {Facts.core_mbudgets_fit(m) == True{} : Bool}) -> {Wr.Got{m, rest} == FFx.get_mbudgets(FFx.put_mbudgets(m, rest)) : Wr.Dec<Maybe<&2, Fx.Budgets>>}:
  match m:
    case None{}:
      {==}
    case Some{+b}:
      %pc.f_budgets(b, rest, h) : {Wr.Got{Some{b}, rest} == FFx.get_mbudgets.some(_) : Wr.Dec<Maybe<&2, Fx.Budgets>>}
      {==}

# a budget request that fits reads back
def pc.f_req(+q: FFx.Req, +rest: String, h: {Facts.core_facts_req_fits(q) == True{} : Bool}) -> {Wr.Got{q, rest} == FFx.get_req(FFx.put_req(q, rest)) : Wr.Dec<FFx.Req>}:
  match q:
    case FFx.Level{+l, +c, +d}:
      +hhh = h
      +hh0 = LBoolAnd.wr_and_r(Facts.core_customs_fit(c), Facts.core_budgets_fit(d), hhh)
      +r2 = FFx.put_budgets(d, rest)
      +r1 = FFx.put_customs(c, r2)
      +r0 = FFx.put_elv(l, r1)
      +d0 = FFx.get_elv(r0)
      +e0 = pc.f_elv(l, r1)
      +d1 = FFx.seq(~Fx.ELv, ~Fx.Customs, ~FFx.get_customs, d0)
      +e1 = pc.seqFFx(~Fx.ELv, ~Fx.Customs, ~FFx.get_customs, l, r1, c, r2, d0, e0, pc.f_customs(c, r2, LBoolAnd.wr_and_l(Facts.core_customs_fit(c), Facts.core_budgets_fit(d), hhh)))
      +d2 = FFx.seq(~FFx.P2<Fx.ELv, Fx.Customs>, ~Fx.Budgets, ~FFx.get_budgets, d1)
      +e2 = pc.seqFFx(~FFx.P2<Fx.ELv, Fx.Customs>, ~Fx.Budgets, ~FFx.get_budgets, FFx.P2{l, c}, r2, d, rest, d1, e1, pc.f_budgets(d, rest, hh0))
      %e2 : {Wr.Got{FFx.Level{l, c, d}, rest} == FFx.get_level.of(_) : Wr.Dec<FFx.Req>}
      {==}
    case FFx.Room{+b, +m, +a}:
      +hhh = h
      +hh0 = LBoolAnd.wr_and_r(LawsBase.wire_fits(b), Bool.and(LawsBase.wire_fits(m), LawsBase.wire_fits(a)), hhh)
      +hh1 = LBoolAnd.wr_and_r(LawsBase.wire_fits(m), LawsBase.wire_fits(a), hh0)
      +r2 = Wr.put_nat(a, rest)
      +r1 = Wr.put_nat(m, r2)
      +r0 = Wr.put_nat(b, r1)
      +d0 = Wr.get_nat(r0)
      +e0 = LWire.pc.nat(b, r1, LBoolAnd.wr_and_l(LawsBase.wire_fits(b), Bool.and(LawsBase.wire_fits(m), LawsBase.wire_fits(a)), hhh))
      +d1 = FFx.seq(~Nat, ~Nat, ~Wr.get_nat, d0)
      +e1 = pc.seqFFx(~Nat, ~Nat, ~Wr.get_nat, b, r1, m, r2, d0, e0, LWire.pc.nat(m, r2, LBoolAnd.wr_and_l(LawsBase.wire_fits(m), LawsBase.wire_fits(a), hh0)))
      +d2 = FFx.seq(~FFx.P2<Nat, Nat>, ~Nat, ~Wr.get_nat, d1)
      +e2 = pc.seqFFx(~FFx.P2<Nat, Nat>, ~Nat, ~Wr.get_nat, FFx.P2{b, m}, r2, a, rest, d1, e1, LWire.pc.nat(a, rest, hh1))
      %e2 : {Wr.Got{FFx.Room{b, m, a}, rest} == FFx.get_room.of(_) : Wr.Dec<FFx.Req>}
      {==}
    case FFx.Adjust{+base, +mm, +l, +c, +d, +a}:
      +hhh = h
      +hh0 = LBoolAnd.wr_and_r(LawsBase.core_mfits(base), Bool.and(LawsBase.wire_fits(mm), Bool.and(Facts.core_customs_fit(c), Bool.and(Facts.core_budgets_fit(d), LawsBase.wire_fits(a)))), hhh)
      +hh1 = LBoolAnd.wr_and_r(LawsBase.wire_fits(mm), Bool.and(Facts.core_customs_fit(c), Bool.and(Facts.core_budgets_fit(d), LawsBase.wire_fits(a))), hh0)
      +hh2 = LBoolAnd.wr_and_r(Facts.core_customs_fit(c), Bool.and(Facts.core_budgets_fit(d), LawsBase.wire_fits(a)), hh1)
      +hh3 = LBoolAnd.wr_and_r(Facts.core_budgets_fit(d), LawsBase.wire_fits(a), hh2)
      +r5 = Wr.put_nat(a, rest)
      +r4 = FFx.put_budgets(d, r5)
      +r3 = FFx.put_customs(c, r4)
      +r2 = FFx.put_elv(l, r3)
      +r1 = Wr.put_nat(mm, r2)
      +r0 = FFx.put_mnat(base, r1)
      +d0 = FFx.get_mnat(r0)
      +e0 = pc.f_mnat(base, r1, LBoolAnd.wr_and_l(LawsBase.core_mfits(base), Bool.and(LawsBase.wire_fits(mm), Bool.and(Facts.core_customs_fit(c), Bool.and(Facts.core_budgets_fit(d), LawsBase.wire_fits(a)))), hhh))
      +d1 = FFx.seq(~Maybe<&2, Nat>, ~Nat, ~Wr.get_nat, d0)
      +e1 = pc.seqFFx(~Maybe<&2, Nat>, ~Nat, ~Wr.get_nat, base, r1, mm, r2, d0, e0, LWire.pc.nat(mm, r2, LBoolAnd.wr_and_l(LawsBase.wire_fits(mm), Bool.and(Facts.core_customs_fit(c), Bool.and(Facts.core_budgets_fit(d), LawsBase.wire_fits(a))), hh0)))
      +d2 = FFx.seq(~FFx.P2<Maybe<&2, Nat>, Nat>, ~Fx.ELv, ~FFx.get_elv, d1)
      +e2 = pc.seqFFx(~FFx.P2<Maybe<&2, Nat>, Nat>, ~Fx.ELv, ~FFx.get_elv, FFx.P2{base, mm}, r2, l, r3, d1, e1, pc.f_elv(l, r3))
      +d3 = FFx.seq(~FFx.P2<FFx.P2<Maybe<&2, Nat>, Nat>, Fx.ELv>, ~Fx.Customs, ~FFx.get_customs, d2)
      +e3 = pc.seqFFx(~FFx.P2<FFx.P2<Maybe<&2, Nat>, Nat>, Fx.ELv>, ~Fx.Customs, ~FFx.get_customs, FFx.P2{FFx.P2{base, mm}, l}, r3, c, r4, d2, e2, pc.f_customs(c, r4, LBoolAnd.wr_and_l(Facts.core_customs_fit(c), Bool.and(Facts.core_budgets_fit(d), LawsBase.wire_fits(a)), hh1)))
      +d4 = FFx.seq(~FFx.P2<FFx.P2<FFx.P2<Maybe<&2, Nat>, Nat>, Fx.ELv>, Fx.Customs>, ~Fx.Budgets, ~FFx.get_budgets, d3)
      +e4 = pc.seqFFx(~FFx.P2<FFx.P2<FFx.P2<Maybe<&2, Nat>, Nat>, Fx.ELv>, Fx.Customs>, ~Fx.Budgets, ~FFx.get_budgets, FFx.P2{FFx.P2{FFx.P2{base, mm}, l}, c}, r4, d, r5, d3, e3, pc.f_budgets(d, r5, LBoolAnd.wr_and_l(Facts.core_budgets_fit(d), LawsBase.wire_fits(a), hh2)))
      +d5 = FFx.seq(~FFx.P2<FFx.P2<FFx.P2<FFx.P2<Maybe<&2, Nat>, Nat>, Fx.ELv>, Fx.Customs>, Fx.Budgets>, ~Nat, ~Wr.get_nat, d4)
      +e5 = pc.seqFFx(~FFx.P2<FFx.P2<FFx.P2<FFx.P2<Maybe<&2, Nat>, Nat>, Fx.ELv>, Fx.Customs>, Fx.Budgets>, ~Nat, ~Wr.get_nat, FFx.P2{FFx.P2{FFx.P2{FFx.P2{base, mm}, l}, c}, d}, r5, a, rest, d4, e4, LWire.pc.nat(a, rest, hh3))
      %e5 : {Wr.Got{FFx.Adjust{base, mm, l, c, d, a}, rest} == FFx.get_adjust.of(_) : Wr.Dec<FFx.Req>}
      {==}
    case FFx.Google{+rule, +c, +l}:
      +hhh = h
      +hh0 = LBoolAnd.wr_and_r(Facts.core_mbudgets_fit(rule), Facts.core_customs_fit(c), hhh)
      +r2 = FFx.put_lv(l, rest)
      +r1 = FFx.put_customs(c, r2)
      +r0 = FFx.put_mbudgets(rule, r1)
      +d0 = FFx.get_mbudgets(r0)
      +e0 = pc.f_mbudgets(rule, r1, LBoolAnd.wr_and_l(Facts.core_mbudgets_fit(rule), Facts.core_customs_fit(c), hhh))
      +d1 = FFx.seq(~Maybe<&2, Fx.Budgets>, ~Fx.Customs, ~FFx.get_customs, d0)
      +e1 = pc.seqFFx(~Maybe<&2, Fx.Budgets>, ~Fx.Customs, ~FFx.get_customs, rule, r1, c, r2, d0, e0, pc.f_customs(c, r2, hh0))
      +d2 = FFx.seq(~FFx.P2<Maybe<&2, Fx.Budgets>, Fx.Customs>, ~Fx.Lv, ~FFx.get_lv, d1)
      +e2 = pc.seqFFx(~FFx.P2<Maybe<&2, Fx.Budgets>, Fx.Customs>, ~Fx.Lv, ~FFx.get_lv, FFx.P2{rule, c}, r2, l, rest, d1, e1, pc.f_lv(l, rest))
      %e2 : {Wr.Got{FFx.Google{rule, c, l}, rest} == FFx.get_google.of(_) : Wr.Dec<FFx.Req>}
      {==}
    case FFx.Aux{+c, +d, +a, +top}:
      +hhh = h
      +hh0 = LBoolAnd.wr_and_r(Facts.core_customs_fit(c), Bool.and(Facts.core_budgets_fit(d), Bool.and(LawsBase.wire_fits(a), LawsBase.wire_fits(top))), hhh)
      +hh1 = LBoolAnd.wr_and_r(Facts.core_budgets_fit(d), Bool.and(LawsBase.wire_fits(a), LawsBase.wire_fits(top)), hh0)
      +hh2 = LBoolAnd.wr_and_r(LawsBase.wire_fits(a), LawsBase.wire_fits(top), hh1)
      +r3 = Wr.put_nat(top, rest)
      +r2 = Wr.put_nat(a, r3)
      +r1 = FFx.put_budgets(d, r2)
      +r0 = FFx.put_customs(c, r1)
      +d0 = FFx.get_customs(r0)
      +e0 = pc.f_customs(c, r1, LBoolAnd.wr_and_l(Facts.core_customs_fit(c), Bool.and(Facts.core_budgets_fit(d), Bool.and(LawsBase.wire_fits(a), LawsBase.wire_fits(top))), hhh))
      +d1 = FFx.seq(~Fx.Customs, ~Fx.Budgets, ~FFx.get_budgets, d0)
      +e1 = pc.seqFFx(~Fx.Customs, ~Fx.Budgets, ~FFx.get_budgets, c, r1, d, r2, d0, e0, pc.f_budgets(d, r2, LBoolAnd.wr_and_l(Facts.core_budgets_fit(d), Bool.and(LawsBase.wire_fits(a), LawsBase.wire_fits(top)), hh0)))
      +d2 = FFx.seq(~FFx.P2<Fx.Customs, Fx.Budgets>, ~Nat, ~Wr.get_nat, d1)
      +e2 = pc.seqFFx(~FFx.P2<Fx.Customs, Fx.Budgets>, ~Nat, ~Wr.get_nat, FFx.P2{c, d}, r2, a, r3, d1, e1, LWire.pc.nat(a, r3, LBoolAnd.wr_and_l(LawsBase.wire_fits(a), LawsBase.wire_fits(top), hh1)))
      +d3 = FFx.seq(~FFx.P2<FFx.P2<Fx.Customs, Fx.Budgets>, Nat>, ~Nat, ~Wr.get_nat, d2)
      +e3 = pc.seqFFx(~FFx.P2<FFx.P2<Fx.Customs, Fx.Budgets>, Nat>, ~Nat, ~Wr.get_nat, FFx.P2{FFx.P2{c, d}, a}, r3, top, rest, d2, e2, LWire.pc.nat(top, rest, hh2))
      %e3 : {Wr.Got{FFx.Aux{c, d, a, top}, rest} == FFx.get_aux.of(_) : Wr.Dec<FFx.Req>}
      {==}
