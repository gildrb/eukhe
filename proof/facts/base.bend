# eukhe: lemmas the proofs of area facts share

import Base
import ../../bend/facts.bend as Fx
import ../../bend/ffi_facts.bend as FFx
import ../../bend/wire.bend as Wr
import ../../laws/facts/budgets.bend as FactsBudgets
import ../../laws/facts/model.bend as Facts
import ../../laws/base.bend as LawsBase
import ../base/logic/bool.bend as LLogicBool
import ../base/logic/logic.bend as LLogicLogic
import ../base/nat.bend as LNat
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
      LLogicLogic.pq.absurd({Nat.is_le(1n+q, 0n) == True{} : Bool}, h)
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      pf.not_lt_le(p, q, h)

def pf.le_trans(+a: Nat, +b: Nat, +c: Nat, ab: {Nat.is_le(a, b) == True{} : Bool}, bc: {Nat.is_le(b, c) == True{} : Bool}) -> {Nat.is_le(a, c) == True{} : Bool}:
  match a b c:
    case 0n b c:
      LNat.pq.le0(c)
    case 1n+p 0n c:
      LLogicLogic.pq.absurdF({Nat.is_le(1n+p, c) == True{} : Bool}, ab)
    case 1n+p 1n+q 0n:
      LLogicLogic.pq.absurdF({Nat.is_le(1n+p, 0n) == True{} : Bool}, bc)
    case 1n+p 1n+q 1n+r:
      pf.le_trans(p, q, r, ab, bc)

def pf.min_le_r(+x: Nat, +y: Nat) -> {Nat.is_le(Nat.min(x, y), y) == True{} : Bool}:
  match x y:
    case 0n y:
      LNat.pq.le0(y)
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

# The output cap
# --------------

# p + q past w: p past w, or q past what is left of w after p
def pf.lt_add(+w: Nat, +p: Nat, +q: Nat) -> {Bool.or(Nat.is_lt(w, p), Nat.is_lt(Nat.sub(w, p), q)) == Nat.is_lt(w, Nat.add(p, q)) : Bool}:
  match w p:
    case 0n 0n:
      {==}
    case 0n 1n+b:
      {==}
    case 1n+a 0n:
      {==}
    case 1n+a 1n+b:
      pf.lt_add(a, b, q)

# (w - p) - s is w - (p + s)
def pf.sub_sub(+w: Nat, +p: Nat, +s: Nat) -> {Nat.sub(Nat.sub(w, p), s) == Nat.sub(w, Nat.add(p, s)) : Nat}:
  match w p:
    case 0n p:
      {==}
    case 1n+a 0n:
      {==}
    case 1n+a 1n+b:
      pf.sub_sub(a, b, s)

# the conflict decided without the sum is the conflict of the sum
def pf.over(+w: Nat, +p: Nat, +s: Nat, +x: Nat) -> {Fx.cap.over(w, p, s, x) == Nat.is_lt(w, Nat.add(Nat.add(p, s), x)) : Bool}:
  %pf.lt_add(w, Nat.add(p, s), x) : {Fx.cap.over(w, p, s, x) == _ : Bool}
  %pf.lt_add(w, p, s) : {Fx.cap.over(w, p, s, x) == Bool.or(_, Nat.is_lt(Nat.sub(w, Nat.add(p, s)), x)) : Bool}
  %pf.sub_sub(w, p, s) : {Fx.cap.over(w, p, s, x) == Bool.or(Bool.or(Nat.is_lt(w, p), Nat.is_lt(Nat.sub(w, p), s)), Nat.is_lt(_, x)) : Bool}
  {==}

# the window shrink is the shrink of the conflict the laws state
def pf.shrink(+x: Nat, +w: Nat, +p: Nat, +s: Nat, +f: Nat, +st: Bool) -> {Fx.cap.fit(Facts.cap_conflict(x, Fx.Win{w, p, s, f, st}), x, w, p, s, f) == Fx.cap.shrink(x, Fx.Win{w, p, s, f, st}) : Nat}:
  %pf.over(w, p, s, x) : {Fx.cap.fit(Bool.and(Bool.not(st), Bool.and(Nat.is_lt(0n, w), _)), x, w, p, s, f) == Fx.cap.shrink(x, Fx.Win{w, p, s, f, st}) : Nat}
  {==}

# a below b: a at most b
def pf.lt_le(+a: Nat, +b: Nat, h: {Nat.is_lt(a, b) == True{} : Bool}) -> {Nat.is_le(a, b) == True{} : Bool}:
  match a b:
    case 0n b:
      LNat.pq.le0(b)
    case 1n+p 0n:
      LLogicLogic.pq.absurdF({Nat.is_le(1n+p, 0n) == True{} : Bool}, h)
    case 1n+p 1n+q:
      pf.lt_le(p, q, h)

# w below q + x: what is left of w after q is at most x
def pf.lt_sub_le(+w: Nat, +q: Nat, +x: Nat, h: {Nat.is_lt(w, Nat.add(q, x)) == True{} : Bool}) -> {Nat.is_le(Nat.sub(w, q), x) == True{} : Bool}:
  match w q:
    case 0n q:
      LNat.pq.le0(x)
    case 1n+a 0n:
      pf.lt_le(1n+a, x, h)
    case 1n+a 1n+b:
      pf.lt_sub_le(a, b, x, h)

# a below b: a - b is 0
def pf.sub_zero_lt(+a: Nat, +b: Nat, h: {Nat.is_lt(a, b) == True{} : Bool}) -> {Nat.sub(a, b) == 0n : Nat}:
  match a b:
    case 0n b:
      {==}
    case 1n+p 0n:
      LLogicLogic.pq.absurdF({1n+p == 0n : Nat}, h)
    case 1n+p 1n+q:
      pf.sub_zero_lt(p, q, h)

def pf.min_zero(+b: Nat) -> {Nat.min(b, 0n) == 0n : Nat}:
  match b:
    case 0n:
      {==}
    case 1n+p:
      {==}

def pf.le_max_l(+f: Nat, +y: Nat) -> {Nat.is_le(f, Nat.max(f, y)) == True{} : Bool}:
  match f y:
    case 0n y:
      LNat.pq.le0(y)
    case 1n+p 0n:
      facts.pf.le_refl(1n+p)
    case 1n+p 1n+q:
      pf.le_max_l(p, q)

def pf.le_max_r(+f: Nat, +x: Nat) -> {Nat.is_le(x, Nat.max(f, x)) == True{} : Bool}:
  match f x:
    case 0n x:
      facts.pf.le_refl(x)
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      pf.le_max_r(p, q)

def pf.max_mono_r(+f: Nat, +y: Nat, +x: Nat, h: {Nat.is_le(y, x) == True{} : Bool}) -> {Nat.is_le(Nat.max(f, y), Nat.max(f, x)) == True{} : Bool}:
  match f y x:
    case 0n y x:
      h
    case 1n+p 0n x:
      pf.le_max_l(1n+p, x)
    case 1n+p 1n+q 0n:
      LLogicLogic.pq.absurdF({Nat.is_le(Nat.max(1n+p, 1n+q), Nat.max(1n+p, 0n)) == True{} : Bool}, h)
    case 1n+p 1n+q 1n+r:
      pf.max_mono_r(p, q, r, h)

def pf.max_le(+f: Nat, +y: Nat, +x: Nat, hf: {Nat.is_le(f, x) == True{} : Bool}, hy: {Nat.is_le(y, x) == True{} : Bool}) -> {Nat.is_le(Nat.max(f, y), x) == True{} : Bool}:
  match f y x:
    case 0n y x:
      hy
    case 1n+p 0n x:
      hf
    case 1n+p 1n+q 0n:
      LLogicLogic.pq.absurdF({Nat.is_le(Nat.max(1n+p, 1n+q), 0n) == True{} : Bool}, hf)
    case 1n+p 1n+q 1n+r:
      pf.max_le(p, q, r, hf, hy)

# the shrunk cap at c (the shrink's condition, e its evidence) is at most
# the floor or the wish
def pf.fit_le(c: Bool, +x: Nat, +w: Nat, +p: Nat, +s: Nat, +f: Nat, +st: Bool, e: {Bool.and(Bool.not(st), Bool.and(Nat.is_lt(0n, w), Fx.cap.over(w, p, s, x))) == c : Bool}) -> {Nat.is_le(Fx.cap.fit(c, x, w, p, s, f), Nat.max(f, x)) == True{} : Bool}:
  match c:
    case True{}:
      +o1 = LLogicBool.wr_and_r(Bool.not(st), Bool.and(Nat.is_lt(0n, w), Fx.cap.over(w, p, s, x)), e)
      +o2 = LLogicBool.wr_and_r(Nat.is_lt(0n, w), Fx.cap.over(w, p, s, x), o1)
      +lt = Equal.trans(Bool, Nat.is_lt(w, Nat.add(Nat.add(p, s), x)), Fx.cap.over(w, p, s, x), True{}, Equal.sym(Bool, Fx.cap.over(w, p, s, x), Nat.is_lt(w, Nat.add(Nat.add(p, s), x)), pf.over(w, p, s, x)), o2)
      %Equal.sym(Nat, Nat.sub(Nat.sub(w, p), s), Nat.sub(w, Nat.add(p, s)), pf.sub_sub(w, p, s)) : {Nat.is_le(Nat.max(f, _), Nat.max(f, x)) == True{} : Bool}
      pf.max_mono_r(f, Nat.sub(w, Nat.add(p, s)), x, pf.lt_sub_le(w, Nat.add(p, s), x, lt))
    case False{}:
      pf.le_max_r(f, x)

# a shrunk cap is at most the floor or the wish
def pf.shrink_le(+x: Nat, +w: Nat, +p: Nat, +s: Nat, +f: Nat, +st: Bool) -> {Nat.is_le(Fx.cap.shrink(x, Fx.Win{w, p, s, f, st}), Nat.max(f, x)) == True{} : Bool}:
  pf.fit_le(Bool.and(Bool.not(st), Bool.and(Nat.is_lt(0n, w), Fx.cap.over(w, p, s, x))), x, w, p, s, f, st, {==})

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
      LLogicLogic.pq.absurdF({0n == 1n+q : Nat}, h)
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      %w2.min_r(p, q, h) : {1n+Nat.min(p, q) == 1n+_ : Nat}
      {==}

# the minimal budget of an ordered rule is at most its high budget
def pf.ord_mh(+b: Fx.Budgets, +ordered: {Fx.Budgets.ordered(b) == True{} : Bool}) -> {Nat.is_le(Fx.Budgets.minimal(b), Fx.Budgets.high(b)) == True{} : Bool}:
  match b:
    case Fx.Budgets{+mi, +lo, +me, +hi}:
      +ml = LLogicBool.pq.and_l(Nat.is_le(mi, lo), Bool.and(Nat.is_le(lo, me), Nat.is_le(me, hi)), ordered)
      +rest = LLogicBool.pq.and_r(Nat.is_le(mi, lo), Bool.and(Nat.is_le(lo, me), Nat.is_le(me, hi)), ordered)
      +lm = LLogicBool.pq.and_l(Nat.is_le(lo, me), Nat.is_le(me, hi), rest)
      +mh = LLogicBool.pq.and_r(Nat.is_le(lo, me), Nat.is_le(me, hi), rest)
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
def pc.f_customs(+c: Fx.Customs, +rest: String, h: {FactsBudgets.core_customs_fit(c) == True{} : Bool}) -> {Wr.Got{c, rest} == FFx.get_customs(FFx.put_customs(c, rest)) : Wr.Dec<Fx.Customs>}:
  match c:
    case Fx.Customs{+mi, +lo, +me, +hi}:
      +hhh = h
      +hh0 = LLogicBool.wr_and_r(LawsBase.core_mfits(mi), Bool.and(LawsBase.core_mfits(lo), Bool.and(LawsBase.core_mfits(me), LawsBase.core_mfits(hi))), hhh)
      +hh1 = LLogicBool.wr_and_r(LawsBase.core_mfits(lo), Bool.and(LawsBase.core_mfits(me), LawsBase.core_mfits(hi)), hh0)
      +hh2 = LLogicBool.wr_and_r(LawsBase.core_mfits(me), LawsBase.core_mfits(hi), hh1)
      +r3 = FFx.put_mnat(hi, rest)
      +r2 = FFx.put_mnat(me, r3)
      +r1 = FFx.put_mnat(lo, r2)
      +r0 = FFx.put_mnat(mi, r1)
      +d0 = FFx.get_mnat(r0)
      +e0 = pc.f_mnat(mi, r1, LLogicBool.wr_and_l(LawsBase.core_mfits(mi), Bool.and(LawsBase.core_mfits(lo), Bool.and(LawsBase.core_mfits(me), LawsBase.core_mfits(hi))), hhh))
      +d1 = FFx.seq(~Maybe<&2, Nat>, ~Maybe<&2, Nat>, ~FFx.get_mnat, d0)
      +e1 = pc.seqFFx(~Maybe<&2, Nat>, ~Maybe<&2, Nat>, ~FFx.get_mnat, mi, r1, lo, r2, d0, e0, pc.f_mnat(lo, r2, LLogicBool.wr_and_l(LawsBase.core_mfits(lo), Bool.and(LawsBase.core_mfits(me), LawsBase.core_mfits(hi)), hh0)))
      +d2 = FFx.seq(~FFx.P2<Maybe<&2, Nat>, Maybe<&2, Nat>>, ~Maybe<&2, Nat>, ~FFx.get_mnat, d1)
      +e2 = pc.seqFFx(~FFx.P2<Maybe<&2, Nat>, Maybe<&2, Nat>>, ~Maybe<&2, Nat>, ~FFx.get_mnat, FFx.P2{mi, lo}, r2, me, r3, d1, e1, pc.f_mnat(me, r3, LLogicBool.wr_and_l(LawsBase.core_mfits(me), LawsBase.core_mfits(hi), hh1)))
      +d3 = FFx.seq(~FFx.P2<FFx.P2<Maybe<&2, Nat>, Maybe<&2, Nat>>, Maybe<&2, Nat>>, ~Maybe<&2, Nat>, ~FFx.get_mnat, d2)
      +e3 = pc.seqFFx(~FFx.P2<FFx.P2<Maybe<&2, Nat>, Maybe<&2, Nat>>, Maybe<&2, Nat>>, ~Maybe<&2, Nat>, ~FFx.get_mnat, FFx.P2{FFx.P2{mi, lo}, me}, r3, hi, rest, d2, e2, pc.f_mnat(hi, rest, hh2))
      %e3 : {Wr.Got{Fx.Customs{mi, lo, me, hi}, rest} == FFx.get_customs.of(_) : Wr.Dec<Fx.Customs>}
      {==}

# a budget table that fits reads back
def pc.f_budgets(+b: Fx.Budgets, +rest: String, h: {FactsBudgets.core_budgets_fit(b) == True{} : Bool}) -> {Wr.Got{b, rest} == FFx.get_budgets(FFx.put_budgets(b, rest)) : Wr.Dec<Fx.Budgets>}:
  match b:
    case Fx.Budgets{+mi, +lo, +me, +hi}:
      +hhh = h
      +hh0 = LLogicBool.wr_and_r(LawsBase.wire_fits(mi), Bool.and(LawsBase.wire_fits(lo), Bool.and(LawsBase.wire_fits(me), LawsBase.wire_fits(hi))), hhh)
      +hh1 = LLogicBool.wr_and_r(LawsBase.wire_fits(lo), Bool.and(LawsBase.wire_fits(me), LawsBase.wire_fits(hi)), hh0)
      +hh2 = LLogicBool.wr_and_r(LawsBase.wire_fits(me), LawsBase.wire_fits(hi), hh1)
      +r3 = Wr.put_nat(hi, rest)
      +r2 = Wr.put_nat(me, r3)
      +r1 = Wr.put_nat(lo, r2)
      +r0 = Wr.put_nat(mi, r1)
      +d0 = Wr.get_nat(r0)
      +e0 = LWire.pc.nat(mi, r1, LLogicBool.wr_and_l(LawsBase.wire_fits(mi), Bool.and(LawsBase.wire_fits(lo), Bool.and(LawsBase.wire_fits(me), LawsBase.wire_fits(hi))), hhh))
      +d1 = FFx.seq(~Nat, ~Nat, ~Wr.get_nat, d0)
      +e1 = pc.seqFFx(~Nat, ~Nat, ~Wr.get_nat, mi, r1, lo, r2, d0, e0, LWire.pc.nat(lo, r2, LLogicBool.wr_and_l(LawsBase.wire_fits(lo), Bool.and(LawsBase.wire_fits(me), LawsBase.wire_fits(hi)), hh0)))
      +d2 = FFx.seq(~FFx.P2<Nat, Nat>, ~Nat, ~Wr.get_nat, d1)
      +e2 = pc.seqFFx(~FFx.P2<Nat, Nat>, ~Nat, ~Wr.get_nat, FFx.P2{mi, lo}, r2, me, r3, d1, e1, LWire.pc.nat(me, r3, LLogicBool.wr_and_l(LawsBase.wire_fits(me), LawsBase.wire_fits(hi), hh1)))
      +d3 = FFx.seq(~FFx.P2<FFx.P2<Nat, Nat>, Nat>, ~Nat, ~Wr.get_nat, d2)
      +e3 = pc.seqFFx(~FFx.P2<FFx.P2<Nat, Nat>, Nat>, ~Nat, ~Wr.get_nat, FFx.P2{FFx.P2{mi, lo}, me}, r3, hi, rest, d2, e2, LWire.pc.nat(hi, rest, hh2))
      %e3 : {Wr.Got{Fx.Budgets{mi, lo, me, hi}, rest} == FFx.get_budgets.of(_) : Wr.Dec<Fx.Budgets>}
      {==}

# a Maybe<Budgets> that fits reads back
def pc.f_mbudgets(+m: Maybe<&2, Fx.Budgets>, +rest: String, h: {FactsBudgets.core_mbudgets_fit(m) == True{} : Bool}) -> {Wr.Got{m, rest} == FFx.get_mbudgets(FFx.put_mbudgets(m, rest)) : Wr.Dec<Maybe<&2, Fx.Budgets>>}:
  match m:
    case None{}:
      {==}
    case Some{+b}:
      %pc.f_budgets(b, rest, h) : {Wr.Got{Some{b}, rest} == FFx.get_mbudgets.some(_) : Wr.Dec<Maybe<&2, Fx.Budgets>>}
      {==}

# a Bool reads back
def pc.f_bool(+b: Bool, +rest: String) -> {Wr.Got{b, rest} == Wr.get_bool(Wr.put_bool(b, rest)) : Wr.Dec<Bool>}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

# the window facts that fit read back
def pc.f_win(+win: Fx.Win, +rest: String, h: {FactsBudgets.core_win_fit(win) == True{} : Bool}) -> {Wr.Got{win, rest} == FFx.get_win(FFx.put_win(win, rest)) : Wr.Dec<Fx.Win>}:
  match win:
    case Fx.Win{+n, +p, +s, +f, +st}:
      +hhh = h
      +hh0 = LLogicBool.wr_and_r(LawsBase.wire_fits(n), Bool.and(LawsBase.wire_fits(p), Bool.and(LawsBase.wire_fits(s), LawsBase.wire_fits(f))), hhh)
      +hh1 = LLogicBool.wr_and_r(LawsBase.wire_fits(p), Bool.and(LawsBase.wire_fits(s), LawsBase.wire_fits(f)), hh0)
      +hh2 = LLogicBool.wr_and_r(LawsBase.wire_fits(s), LawsBase.wire_fits(f), hh1)
      +r4 = Wr.put_bool(st, rest)
      +r3 = Wr.put_nat(f, r4)
      +r2 = Wr.put_nat(s, r3)
      +r1 = Wr.put_nat(p, r2)
      +r0 = Wr.put_nat(n, r1)
      +d0 = Wr.get_nat(r0)
      +e0 = LWire.pc.nat(n, r1, LLogicBool.wr_and_l(LawsBase.wire_fits(n), Bool.and(LawsBase.wire_fits(p), Bool.and(LawsBase.wire_fits(s), LawsBase.wire_fits(f))), hhh))
      +d1 = FFx.seq(~Nat, ~Nat, ~Wr.get_nat, d0)
      +e1 = pc.seqFFx(~Nat, ~Nat, ~Wr.get_nat, n, r1, p, r2, d0, e0, LWire.pc.nat(p, r2, LLogicBool.wr_and_l(LawsBase.wire_fits(p), Bool.and(LawsBase.wire_fits(s), LawsBase.wire_fits(f)), hh0)))
      +d2 = FFx.seq(~FFx.P2<Nat, Nat>, ~Nat, ~Wr.get_nat, d1)
      +e2 = pc.seqFFx(~FFx.P2<Nat, Nat>, ~Nat, ~Wr.get_nat, FFx.P2{n, p}, r2, s, r3, d1, e1, LWire.pc.nat(s, r3, LLogicBool.wr_and_l(LawsBase.wire_fits(s), LawsBase.wire_fits(f), hh1)))
      +d3 = FFx.seq(~FFx.P2<FFx.P2<Nat, Nat>, Nat>, ~Nat, ~Wr.get_nat, d2)
      +e3 = pc.seqFFx(~FFx.P2<FFx.P2<Nat, Nat>, Nat>, ~Nat, ~Wr.get_nat, FFx.P2{FFx.P2{n, p}, s}, r3, f, r4, d2, e2, LWire.pc.nat(f, r4, hh2))
      +d4 = FFx.seq(~FFx.P2<FFx.P2<FFx.P2<Nat, Nat>, Nat>, Nat>, ~Bool, ~Wr.get_bool, d3)
      +e4 = pc.seqFFx(~FFx.P2<FFx.P2<FFx.P2<Nat, Nat>, Nat>, Nat>, ~Bool, ~Wr.get_bool, FFx.P2{FFx.P2{FFx.P2{n, p}, s}, f}, r4, st, rest, d3, e3, pc.f_bool(st, rest))
      %e4 : {Wr.Got{Fx.Win{n, p, s, f, st}, rest} == FFx.get_win.of(_) : Wr.Dec<Fx.Win>}
      {==}


# a budget request that fits reads back
def pc.f_req(+q: FFx.Req, +rest: String, h: {FactsBudgets.core_facts_req_fits(q) == True{} : Bool}) -> {Wr.Got{q, rest} == FFx.get_req(FFx.put_req(q, rest)) : Wr.Dec<FFx.Req>}:
  match q:
    case FFx.Level{+l, +c, +d}:
      +hhh = h
      +hh0 = LLogicBool.wr_and_r(FactsBudgets.core_customs_fit(c), FactsBudgets.core_budgets_fit(d), hhh)
      +r2 = FFx.put_budgets(d, rest)
      +r1 = FFx.put_customs(c, r2)
      +r0 = FFx.put_elv(l, r1)
      +d0 = FFx.get_elv(r0)
      +e0 = pc.f_elv(l, r1)
      +d1 = FFx.seq(~Fx.ELv, ~Fx.Customs, ~FFx.get_customs, d0)
      +e1 = pc.seqFFx(~Fx.ELv, ~Fx.Customs, ~FFx.get_customs, l, r1, c, r2, d0, e0, pc.f_customs(c, r2, LLogicBool.wr_and_l(FactsBudgets.core_customs_fit(c), FactsBudgets.core_budgets_fit(d), hhh)))
      +d2 = FFx.seq(~FFx.P2<Fx.ELv, Fx.Customs>, ~Fx.Budgets, ~FFx.get_budgets, d1)
      +e2 = pc.seqFFx(~FFx.P2<Fx.ELv, Fx.Customs>, ~Fx.Budgets, ~FFx.get_budgets, FFx.P2{l, c}, r2, d, rest, d1, e1, pc.f_budgets(d, rest, hh0))
      %e2 : {Wr.Got{FFx.Level{l, c, d}, rest} == FFx.get_level.of(_) : Wr.Dec<FFx.Req>}
      {==}
    case FFx.Room{+b, +m, +a}:
      +hhh = h
      +hh0 = LLogicBool.wr_and_r(LawsBase.wire_fits(b), Bool.and(LawsBase.wire_fits(m), LawsBase.wire_fits(a)), hhh)
      +hh1 = LLogicBool.wr_and_r(LawsBase.wire_fits(m), LawsBase.wire_fits(a), hh0)
      +r2 = Wr.put_nat(a, rest)
      +r1 = Wr.put_nat(m, r2)
      +r0 = Wr.put_nat(b, r1)
      +d0 = Wr.get_nat(r0)
      +e0 = LWire.pc.nat(b, r1, LLogicBool.wr_and_l(LawsBase.wire_fits(b), Bool.and(LawsBase.wire_fits(m), LawsBase.wire_fits(a)), hhh))
      +d1 = FFx.seq(~Nat, ~Nat, ~Wr.get_nat, d0)
      +e1 = pc.seqFFx(~Nat, ~Nat, ~Wr.get_nat, b, r1, m, r2, d0, e0, LWire.pc.nat(m, r2, LLogicBool.wr_and_l(LawsBase.wire_fits(m), LawsBase.wire_fits(a), hh0)))
      +d2 = FFx.seq(~FFx.P2<Nat, Nat>, ~Nat, ~Wr.get_nat, d1)
      +e2 = pc.seqFFx(~FFx.P2<Nat, Nat>, ~Nat, ~Wr.get_nat, FFx.P2{b, m}, r2, a, rest, d1, e1, LWire.pc.nat(a, rest, hh1))
      %e2 : {Wr.Got{FFx.Room{b, m, a}, rest} == FFx.get_room.of(_) : Wr.Dec<FFx.Req>}
      {==}
    case FFx.Adjust{+base, +mm, +l, +c, +d, +a, +w}:
      +hhh = h
      +hh0 = LLogicBool.wr_and_r(LawsBase.core_mfits(base), Bool.and(LawsBase.wire_fits(mm), Bool.and(FactsBudgets.core_customs_fit(c), Bool.and(FactsBudgets.core_budgets_fit(d), Bool.and(LawsBase.wire_fits(a), FactsBudgets.core_win_fit(w))))), hhh)
      +hh1 = LLogicBool.wr_and_r(LawsBase.wire_fits(mm), Bool.and(FactsBudgets.core_customs_fit(c), Bool.and(FactsBudgets.core_budgets_fit(d), Bool.and(LawsBase.wire_fits(a), FactsBudgets.core_win_fit(w)))), hh0)
      +hh2 = LLogicBool.wr_and_r(FactsBudgets.core_customs_fit(c), Bool.and(FactsBudgets.core_budgets_fit(d), Bool.and(LawsBase.wire_fits(a), FactsBudgets.core_win_fit(w))), hh1)
      +hh3 = LLogicBool.wr_and_r(FactsBudgets.core_budgets_fit(d), Bool.and(LawsBase.wire_fits(a), FactsBudgets.core_win_fit(w)), hh2)
      +hh4 = LLogicBool.wr_and_r(LawsBase.wire_fits(a), FactsBudgets.core_win_fit(w), hh3)
      +r6 = FFx.put_win(w, rest)
      +r5 = Wr.put_nat(a, r6)
      +r4 = FFx.put_budgets(d, r5)
      +r3 = FFx.put_customs(c, r4)
      +r2 = FFx.put_elv(l, r3)
      +r1 = Wr.put_nat(mm, r2)
      +r0 = FFx.put_mnat(base, r1)
      +d0 = FFx.get_mnat(r0)
      +e0 = pc.f_mnat(base, r1, LLogicBool.wr_and_l(LawsBase.core_mfits(base), Bool.and(LawsBase.wire_fits(mm), Bool.and(FactsBudgets.core_customs_fit(c), Bool.and(FactsBudgets.core_budgets_fit(d), Bool.and(LawsBase.wire_fits(a), FactsBudgets.core_win_fit(w))))), hhh))
      +d1 = FFx.seq(~Maybe<&2, Nat>, ~Nat, ~Wr.get_nat, d0)
      +e1 = pc.seqFFx(~Maybe<&2, Nat>, ~Nat, ~Wr.get_nat, base, r1, mm, r2, d0, e0, LWire.pc.nat(mm, r2, LLogicBool.wr_and_l(LawsBase.wire_fits(mm), Bool.and(FactsBudgets.core_customs_fit(c), Bool.and(FactsBudgets.core_budgets_fit(d), Bool.and(LawsBase.wire_fits(a), FactsBudgets.core_win_fit(w)))), hh0)))
      +d2 = FFx.seq(~FFx.P2<Maybe<&2, Nat>, Nat>, ~Fx.ELv, ~FFx.get_elv, d1)
      +e2 = pc.seqFFx(~FFx.P2<Maybe<&2, Nat>, Nat>, ~Fx.ELv, ~FFx.get_elv, FFx.P2{base, mm}, r2, l, r3, d1, e1, pc.f_elv(l, r3))
      +d3 = FFx.seq(~FFx.P2<FFx.P2<Maybe<&2, Nat>, Nat>, Fx.ELv>, ~Fx.Customs, ~FFx.get_customs, d2)
      +e3 = pc.seqFFx(~FFx.P2<FFx.P2<Maybe<&2, Nat>, Nat>, Fx.ELv>, ~Fx.Customs, ~FFx.get_customs, FFx.P2{FFx.P2{base, mm}, l}, r3, c, r4, d2, e2, pc.f_customs(c, r4, LLogicBool.wr_and_l(FactsBudgets.core_customs_fit(c), Bool.and(FactsBudgets.core_budgets_fit(d), Bool.and(LawsBase.wire_fits(a), FactsBudgets.core_win_fit(w))), hh1)))
      +d4 = FFx.seq(~FFx.P2<FFx.P2<FFx.P2<Maybe<&2, Nat>, Nat>, Fx.ELv>, Fx.Customs>, ~Fx.Budgets, ~FFx.get_budgets, d3)
      +e4 = pc.seqFFx(~FFx.P2<FFx.P2<FFx.P2<Maybe<&2, Nat>, Nat>, Fx.ELv>, Fx.Customs>, ~Fx.Budgets, ~FFx.get_budgets, FFx.P2{FFx.P2{FFx.P2{base, mm}, l}, c}, r4, d, r5, d3, e3, pc.f_budgets(d, r5, LLogicBool.wr_and_l(FactsBudgets.core_budgets_fit(d), Bool.and(LawsBase.wire_fits(a), FactsBudgets.core_win_fit(w)), hh2)))
      +d5 = FFx.seq(~FFx.P2<FFx.P2<FFx.P2<FFx.P2<Maybe<&2, Nat>, Nat>, Fx.ELv>, Fx.Customs>, Fx.Budgets>, ~Nat, ~Wr.get_nat, d4)
      +e5 = pc.seqFFx(~FFx.P2<FFx.P2<FFx.P2<FFx.P2<Maybe<&2, Nat>, Nat>, Fx.ELv>, Fx.Customs>, Fx.Budgets>, ~Nat, ~Wr.get_nat, FFx.P2{FFx.P2{FFx.P2{FFx.P2{base, mm}, l}, c}, d}, r5, a, r6, d4, e4, LWire.pc.nat(a, r6, LLogicBool.wr_and_l(LawsBase.wire_fits(a), FactsBudgets.core_win_fit(w), hh3)))
      +d6 = FFx.seq(~FFx.P2<FFx.P2<FFx.P2<FFx.P2<FFx.P2<Maybe<&2, Nat>, Nat>, Fx.ELv>, Fx.Customs>, Fx.Budgets>, Nat>, ~Fx.Win, ~FFx.get_win, d5)
      +e6 = pc.seqFFx(~FFx.P2<FFx.P2<FFx.P2<FFx.P2<FFx.P2<Maybe<&2, Nat>, Nat>, Fx.ELv>, Fx.Customs>, Fx.Budgets>, Nat>, ~Fx.Win, ~FFx.get_win, FFx.P2{FFx.P2{FFx.P2{FFx.P2{FFx.P2{base, mm}, l}, c}, d}, a}, r6, w, rest, d5, e5, pc.f_win(w, rest, hh4))
      %e6 : {Wr.Got{FFx.Adjust{base, mm, l, c, d, a, w}, rest} == FFx.get_adjust.of(_) : Wr.Dec<FFx.Req>}
      {==}
    case FFx.Google{+rule, +c, +l}:
      +hhh = h
      +hh0 = LLogicBool.wr_and_r(FactsBudgets.core_mbudgets_fit(rule), FactsBudgets.core_customs_fit(c), hhh)
      +r2 = FFx.put_lv(l, rest)
      +r1 = FFx.put_customs(c, r2)
      +r0 = FFx.put_mbudgets(rule, r1)
      +d0 = FFx.get_mbudgets(r0)
      +e0 = pc.f_mbudgets(rule, r1, LLogicBool.wr_and_l(FactsBudgets.core_mbudgets_fit(rule), FactsBudgets.core_customs_fit(c), hhh))
      +d1 = FFx.seq(~Maybe<&2, Fx.Budgets>, ~Fx.Customs, ~FFx.get_customs, d0)
      +e1 = pc.seqFFx(~Maybe<&2, Fx.Budgets>, ~Fx.Customs, ~FFx.get_customs, rule, r1, c, r2, d0, e0, pc.f_customs(c, r2, hh0))
      +d2 = FFx.seq(~FFx.P2<Maybe<&2, Fx.Budgets>, Fx.Customs>, ~Fx.Lv, ~FFx.get_lv, d1)
      +e2 = pc.seqFFx(~FFx.P2<Maybe<&2, Fx.Budgets>, Fx.Customs>, ~Fx.Lv, ~FFx.get_lv, FFx.P2{rule, c}, r2, l, rest, d1, e1, pc.f_lv(l, rest))
      %e2 : {Wr.Got{FFx.Google{rule, c, l}, rest} == FFx.get_google.of(_) : Wr.Dec<FFx.Req>}
      {==}
    case FFx.Aux{+c, +d, +a, +top}:
      +hhh = h
      +hh0 = LLogicBool.wr_and_r(FactsBudgets.core_customs_fit(c), Bool.and(FactsBudgets.core_budgets_fit(d), Bool.and(LawsBase.wire_fits(a), LawsBase.wire_fits(top))), hhh)
      +hh1 = LLogicBool.wr_and_r(FactsBudgets.core_budgets_fit(d), Bool.and(LawsBase.wire_fits(a), LawsBase.wire_fits(top)), hh0)
      +hh2 = LLogicBool.wr_and_r(LawsBase.wire_fits(a), LawsBase.wire_fits(top), hh1)
      +r3 = Wr.put_nat(top, rest)
      +r2 = Wr.put_nat(a, r3)
      +r1 = FFx.put_budgets(d, r2)
      +r0 = FFx.put_customs(c, r1)
      +d0 = FFx.get_customs(r0)
      +e0 = pc.f_customs(c, r1, LLogicBool.wr_and_l(FactsBudgets.core_customs_fit(c), Bool.and(FactsBudgets.core_budgets_fit(d), Bool.and(LawsBase.wire_fits(a), LawsBase.wire_fits(top))), hhh))
      +d1 = FFx.seq(~Fx.Customs, ~Fx.Budgets, ~FFx.get_budgets, d0)
      +e1 = pc.seqFFx(~Fx.Customs, ~Fx.Budgets, ~FFx.get_budgets, c, r1, d, r2, d0, e0, pc.f_budgets(d, r2, LLogicBool.wr_and_l(FactsBudgets.core_budgets_fit(d), Bool.and(LawsBase.wire_fits(a), LawsBase.wire_fits(top)), hh0)))
      +d2 = FFx.seq(~FFx.P2<Fx.Customs, Fx.Budgets>, ~Nat, ~Wr.get_nat, d1)
      +e2 = pc.seqFFx(~FFx.P2<Fx.Customs, Fx.Budgets>, ~Nat, ~Wr.get_nat, FFx.P2{c, d}, r2, a, r3, d1, e1, LWire.pc.nat(a, r3, LLogicBool.wr_and_l(LawsBase.wire_fits(a), LawsBase.wire_fits(top), hh1)))
      +d3 = FFx.seq(~FFx.P2<FFx.P2<Fx.Customs, Fx.Budgets>, Nat>, ~Nat, ~Wr.get_nat, d2)
      +e3 = pc.seqFFx(~FFx.P2<FFx.P2<Fx.Customs, Fx.Budgets>, Nat>, ~Nat, ~Wr.get_nat, FFx.P2{FFx.P2{c, d}, a}, r3, top, rest, d2, e2, LWire.pc.nat(top, rest, hh2))
      %e3 : {Wr.Got{FFx.Aux{c, d, a, top}, rest} == FFx.get_aux.of(_) : Wr.Dec<FFx.Req>}
      {==}
    case FFx.Cap{+x, +mm, +n, +w}:
      +hhh = h
      +hh0 = LLogicBool.wr_and_r(LawsBase.core_mfits(x), Bool.and(LawsBase.wire_fits(mm), FactsBudgets.core_win_fit(w)), hhh)
      +hh1 = LLogicBool.wr_and_r(LawsBase.wire_fits(mm), FactsBudgets.core_win_fit(w), hh0)
      +r3 = FFx.put_win(w, rest)
      +r2 = Wr.put_bool(n, r3)
      +r1 = Wr.put_nat(mm, r2)
      +r0 = FFx.put_mnat(x, r1)
      +d0 = FFx.get_mnat(r0)
      +e0 = pc.f_mnat(x, r1, LLogicBool.wr_and_l(LawsBase.core_mfits(x), Bool.and(LawsBase.wire_fits(mm), FactsBudgets.core_win_fit(w)), hhh))
      +d1 = FFx.seq(~Maybe<&2, Nat>, ~Nat, ~Wr.get_nat, d0)
      +e1 = pc.seqFFx(~Maybe<&2, Nat>, ~Nat, ~Wr.get_nat, x, r1, mm, r2, d0, e0, LWire.pc.nat(mm, r2, LLogicBool.wr_and_l(LawsBase.wire_fits(mm), FactsBudgets.core_win_fit(w), hh0)))
      +d2 = FFx.seq(~FFx.P2<Maybe<&2, Nat>, Nat>, ~Bool, ~Wr.get_bool, d1)
      +e2 = pc.seqFFx(~FFx.P2<Maybe<&2, Nat>, Nat>, ~Bool, ~Wr.get_bool, FFx.P2{x, mm}, r2, n, r3, d1, e1, pc.f_bool(n, r3))
      +d3 = FFx.seq(~FFx.P2<FFx.P2<Maybe<&2, Nat>, Nat>, Bool>, ~Fx.Win, ~FFx.get_win, d2)
      +e3 = pc.seqFFx(~FFx.P2<FFx.P2<Maybe<&2, Nat>, Nat>, Bool>, ~Fx.Win, ~FFx.get_win, FFx.P2{FFx.P2{x, mm}, n}, r3, w, rest, d2, e2, pc.f_win(w, rest, hh1))
      %e3 : {Wr.Got{FFx.Cap{x, mm, n, w}, rest} == FFx.get_cap.of(_) : Wr.Dec<FFx.Req>}
      {==}

# The entry's writer is the grammar's spelling
# --------------------------------------------

def fs.mnat(m: Maybe<&2, Nat>, +rest: String) -> {FFx.put_mnat(m, rest) == FactsBudgets.facts_spell_mnat(m, rest) : String}:
  match m:
    case None{}:
      {==}
    case Some{n}:
      {==}

def fs.elv(l: Fx.ELv, +rest: String) -> {FFx.put_elv(l, rest) == FactsBudgets.facts_spell_elv(l, rest) : String}:
  match l:
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

def fs.lv(l: Fx.Lv, +rest: String) -> {FFx.put_lv(l, rest) == FactsBudgets.facts_spell_lv(l, rest) : String}:
  match l:
    case Fx.Minimal{}:
      {==}
    case Fx.Low{}:
      {==}
    case Fx.Medium{}:
      {==}
    case Fx.High{}:
      {==}

def fs.customs(c: Fx.Customs, +rest: String) -> {FFx.put_customs(c, rest) == FactsBudgets.facts_spell_customs(c, rest) : String}:
  match c:
    case Fx.Customs{+mi, +lo, +me, +hi}:
      %fs.mnat(hi, rest) : {FFx.put_mnat(mi, FFx.put_mnat(lo, FFx.put_mnat(me, FFx.put_mnat(hi, rest)))) == FactsBudgets.facts_spell_mnat(mi, FactsBudgets.facts_spell_mnat(lo, FactsBudgets.facts_spell_mnat(me, _))) : String}
      %fs.mnat(me, FFx.put_mnat(hi, rest)) : {FFx.put_mnat(mi, FFx.put_mnat(lo, FFx.put_mnat(me, FFx.put_mnat(hi, rest)))) == FactsBudgets.facts_spell_mnat(mi, FactsBudgets.facts_spell_mnat(lo, _)) : String}
      %fs.mnat(lo, FFx.put_mnat(me, FFx.put_mnat(hi, rest))) : {FFx.put_mnat(mi, FFx.put_mnat(lo, FFx.put_mnat(me, FFx.put_mnat(hi, rest)))) == FactsBudgets.facts_spell_mnat(mi, _) : String}
      fs.mnat(mi, FFx.put_mnat(lo, FFx.put_mnat(me, FFx.put_mnat(hi, rest))))

def fs.budgets(b: Fx.Budgets, +rest: String) -> {FFx.put_budgets(b, rest) == FactsBudgets.facts_spell_budgets(b, rest) : String}:
  match b:
    case Fx.Budgets{mi, lo, me, hi}:
      {==}

def fs.mbudgets(m: Maybe<&2, Fx.Budgets>, +rest: String) -> {FFx.put_mbudgets(m, rest) == FactsBudgets.facts_spell_mbudgets(m, rest) : String}:
  match m:
    case None{}:
      {==}
    case Some{+b}:
      %fs.budgets(b, rest) : {Wr.put_nat(1n, FFx.put_budgets(b, rest)) == Wr.put_nat(1n, _) : String}
      {==}

def fs.win(w: Fx.Win, +rest: String) -> {FFx.put_win(w, rest) == FactsBudgets.facts_spell_win(w, rest) : String}:
  match w:
    case Fx.Win{n, p, s, f, st}:
      {==}

def fs.req(q: FFx.Req, +rest: String) -> {FFx.put_req(q, rest) == FactsBudgets.facts_spell_req(q, rest) : String}:
  match q:
    case FFx.Level{+l, +c, +d}:
      %fs.budgets(d, rest) : {FFx.put_req(FFx.Level{l, c, d}, rest) == Wr.put_nat(0n, FactsBudgets.facts_spell_elv(l, FactsBudgets.facts_spell_customs(c, _))) : String}
      %fs.customs(c, FFx.put_budgets(d, rest)) : {FFx.put_req(FFx.Level{l, c, d}, rest) == Wr.put_nat(0n, FactsBudgets.facts_spell_elv(l, _)) : String}
      %fs.elv(l, FFx.put_customs(c, FFx.put_budgets(d, rest))) : {FFx.put_req(FFx.Level{l, c, d}, rest) == Wr.put_nat(0n, _) : String}
      {==}
    case FFx.Room{b, m, a}:
      {==}
    case FFx.Adjust{+base, +mm, +l, +c, +d, +a, +w}:
      %fs.win(w, rest) : {FFx.put_req(FFx.Adjust{base, mm, l, c, d, a, w}, rest) == Wr.put_nat(2n, FactsBudgets.facts_spell_mnat(base, Wr.put_nat(mm, FactsBudgets.facts_spell_elv(l, FactsBudgets.facts_spell_customs(c, FactsBudgets.facts_spell_budgets(d, Wr.put_nat(a, _))))))) : String}
      %fs.budgets(d, Wr.put_nat(a, FFx.put_win(w, rest))) : {FFx.put_req(FFx.Adjust{base, mm, l, c, d, a, w}, rest) == Wr.put_nat(2n, FactsBudgets.facts_spell_mnat(base, Wr.put_nat(mm, FactsBudgets.facts_spell_elv(l, FactsBudgets.facts_spell_customs(c, _))))) : String}
      %fs.customs(c, FFx.put_budgets(d, Wr.put_nat(a, FFx.put_win(w, rest)))) : {FFx.put_req(FFx.Adjust{base, mm, l, c, d, a, w}, rest) == Wr.put_nat(2n, FactsBudgets.facts_spell_mnat(base, Wr.put_nat(mm, FactsBudgets.facts_spell_elv(l, _)))) : String}
      %fs.elv(l, FFx.put_customs(c, FFx.put_budgets(d, Wr.put_nat(a, FFx.put_win(w, rest))))) : {FFx.put_req(FFx.Adjust{base, mm, l, c, d, a, w}, rest) == Wr.put_nat(2n, FactsBudgets.facts_spell_mnat(base, Wr.put_nat(mm, _))) : String}
      %fs.mnat(base, Wr.put_nat(mm, FFx.put_elv(l, FFx.put_customs(c, FFx.put_budgets(d, Wr.put_nat(a, FFx.put_win(w, rest))))))) : {FFx.put_req(FFx.Adjust{base, mm, l, c, d, a, w}, rest) == Wr.put_nat(2n, _) : String}
      {==}
    case FFx.Google{+rule, +c, +l}:
      %fs.lv(l, rest) : {FFx.put_req(FFx.Google{rule, c, l}, rest) == Wr.put_nat(3n, FactsBudgets.facts_spell_mbudgets(rule, FactsBudgets.facts_spell_customs(c, _))) : String}
      %fs.customs(c, FFx.put_lv(l, rest)) : {FFx.put_req(FFx.Google{rule, c, l}, rest) == Wr.put_nat(3n, FactsBudgets.facts_spell_mbudgets(rule, _)) : String}
      %fs.mbudgets(rule, FFx.put_customs(c, FFx.put_lv(l, rest))) : {FFx.put_req(FFx.Google{rule, c, l}, rest) == Wr.put_nat(3n, _) : String}
      {==}
    case FFx.Aux{+c, +d, +a, +top}:
      %fs.budgets(d, Wr.put_nat(a, Wr.put_nat(top, rest))) : {FFx.put_req(FFx.Aux{c, d, a, top}, rest) == Wr.put_nat(4n, FactsBudgets.facts_spell_customs(c, _)) : String}
      %fs.customs(c, FFx.put_budgets(d, Wr.put_nat(a, Wr.put_nat(top, rest)))) : {FFx.put_req(FFx.Aux{c, d, a, top}, rest) == Wr.put_nat(4n, _) : String}
      {==}
    case FFx.Cap{+x, +mm, +n, +w}:
      %fs.win(w, rest) : {FFx.put_req(FFx.Cap{x, mm, n, w}, rest) == Wr.put_nat(5n, FactsBudgets.facts_spell_mnat(x, Wr.put_nat(mm, Wr.put_bool(n, _)))) : String}
      %fs.mnat(x, Wr.put_nat(mm, Wr.put_bool(n, FFx.put_win(w, rest)))) : {FFx.put_req(FFx.Cap{x, mm, n, w}, rest) == Wr.put_nat(5n, _) : String}
      {==}

def fs.fit(f: Fx.Fit, +rest: String) -> {FFx.put_fit(f, rest) == FactsBudgets.facts_spell_fit(f, rest) : String}:
  match f:
    case Fx.Fit{m, b}:
      {==}

def fs.gb(g: Fx.GB, +rest: String) -> {FFx.put_gb(g, rest) == FactsBudgets.facts_spell_gb(g, rest) : String}:
  match g:
    case Fx.Dynamic{}:
      {==}
    case Fx.Tokens{n}:
      {==}
    case Fx.Unordered{}:
      {==}

# the entry's reply to a request is the spelled reply of the model's
# decision
def fs.answer(q: FFx.Req) -> {FFx.answer(q) == FactsBudgets.facts_spell_answer(q) : String}:
  match q:
    case FFx.Level{l, c, d}:
      {==}
    case FFx.Room{b, m, a}:
      {==}
    case FFx.Adjust{base, mm, l, c, d, a, w}:
      fs.fit(Fx.adjust(base, mm, l, c, d, a, w), "")
    case FFx.Google{rule, c, l}:
      fs.gb(Fx.gbudget(rule, c, l), "")
    case FFx.Aux{c, d, a, top}:
      {==}
    case FFx.Cap{x, mm, n, w}:
      fs.mnat(Fx.cap(x, mm, n, w), "")

# a spelled request that fits, then rest, runs to the entry's end check
def fs.run(+q: FFx.Req, +rest: String, fits: {FactsBudgets.core_facts_req_fits(q) == True{} : Bool}) -> {FFx.ffi(FactsBudgets.facts_spell_req(q, rest)) == FFx.ffi.done(Wr.end(rest), q) : String}:
  %fs.req(q, rest) : {FFx.ffi(_) == FFx.ffi.done(Wr.end(rest), q) : String}
  %pc.f_req(q, rest, fits) : {FFx.ffi.go(_) == FFx.ffi.done(Wr.end(rest), q) : String}
  {==}

# Bool
# ----

# a or b false: a false
def fb.or_fl(+a: Bool, +b: Bool, +h: {Bool.or(a, b) == False{} : Bool}) -> {a == False{} : Bool}:
  match a:
    case False{}:
      {==}
    case True{}:
      LLogicLogic.pf.absurd_tf({True{} == False{} : Bool}, h)

# a or b false: b false
def fb.or_fr(+a: Bool, +b: Bool, +h: {Bool.or(a, b) == False{} : Bool}) -> {b == False{} : Bool}:
  match a:
    case False{}:
      h
    case True{}:
      LLogicLogic.pf.absurd_tf({b == False{} : Bool}, h)

def fb.and_false_r(+a: Bool) -> {Bool.and(a, False{}) == False{} : Bool}:
  match a:
    case False{}:
      {==}
    case True{}:
      {==}

def fb.and_true_r(+a: Bool) -> {Bool.and(a, True{}) == a : Bool}:
  match a:
    case False{}:
      {==}
    case True{}:
      {==}

def fb.and_comm(+a: Bool, +b: Bool) -> {Bool.and(a, b) == Bool.and(b, a) : Bool}:
  match a b:
    case False{} False{}:
      {==}
    case False{} True{}:
      {==}
    case True{} False{}:
      {==}
    case True{} True{}:
      {==}

def fb.and_tt(+a: Bool, +b: Bool, +ea: {a == True{} : Bool}, +eb: {b == True{} : Bool}) -> {Bool.and(a, b) == True{} : Bool}:
  match a:
    case False{}:
      LLogicLogic.pf.absurd_ft({Bool.and(False{}, b) == True{} : Bool}, ea)
    case True{}:
      eb

# x false and x true: anything
def fb.clash(-A: Type, x: Bool, f: {x == False{} : Bool}, t: {x == True{} : Bool}) -> A:
  match x:
    case False{}:
      LLogicLogic.pf.absurd_ft(A, t)
    case True{}:
      LLogicLogic.pf.absurd_tf(A, f)

# Budget rules (the facts_google_* laws)
# --------------------------------------

def fg.p1(+mi: Nat, +lo: Nat, +me: Nat, +hi: Nat, +h: {Facts.rule_falls(mi, lo, me, hi) == False{} : Bool}) -> {Nat.is_le(mi, lo) == True{} : Bool}:
  pf.not_lt_le(lo, mi, fb.or_fl(Nat.is_lt(lo, mi), Bool.or(Nat.is_lt(me, lo), Nat.is_lt(hi, me)), h))

def fg.p2(+mi: Nat, +lo: Nat, +me: Nat, +hi: Nat, +h: {Facts.rule_falls(mi, lo, me, hi) == False{} : Bool}) -> {Nat.is_le(lo, me) == True{} : Bool}:
  +r = fb.or_fr(Nat.is_lt(lo, mi), Bool.or(Nat.is_lt(me, lo), Nat.is_lt(hi, me)), h)
  pf.not_lt_le(me, lo, fb.or_fl(Nat.is_lt(me, lo), Nat.is_lt(hi, me), r))

def fg.p3(+mi: Nat, +lo: Nat, +me: Nat, +hi: Nat, +h: {Facts.rule_falls(mi, lo, me, hi) == False{} : Bool}) -> {Nat.is_le(me, hi) == True{} : Bool}:
  +r = fb.or_fr(Nat.is_lt(lo, mi), Bool.or(Nat.is_lt(me, lo), Nat.is_lt(hi, me)), h)
  pf.not_lt_le(hi, me, fb.or_fr(Nat.is_lt(me, lo), Nat.is_lt(hi, me), r))

# a rule that never falls has minimal at most high
def fg.mh(+mi: Nat, +lo: Nat, +me: Nat, +hi: Nat, +h: {Facts.rule_falls(mi, lo, me, hi) == False{} : Bool}) -> {Nat.is_le(mi, hi) == True{} : Bool}:
  pf.le_trans(mi, lo, hi, fg.p1(mi, lo, me, hi, h), pf.le_trans(lo, me, hi, fg.p2(mi, lo, me, hi, h), fg.p3(mi, lo, me, hi, h)))

# a rule that never falls is ordered: its Google budget is gtokens
def fg.tokens(+mi: Nat, +lo: Nat, +me: Nat, +hi: Nat, +c: Fx.Customs, +l: Fx.Lv, +h: {Facts.rule_falls(mi, lo, me, hi) == False{} : Bool}) -> {Fx.gbudget(Some{Fx.Budgets{mi, lo, me, hi}}, c, l) == Fx.Tokens{Fx.gtokens(Fx.Budgets{mi, lo, me, hi}, c, l)} : Fx.GB}:
  +o = fb.and_tt(Nat.is_le(mi, lo), Bool.and(Nat.is_le(lo, me), Nat.is_le(me, hi)), fg.p1(mi, lo, me, hi, h), fb.and_tt(Nat.is_le(lo, me), Nat.is_le(me, hi), fg.p2(mi, lo, me, hi, h), fg.p3(mi, lo, me, hi, h)))
  %Equal.sym(Bool, Fx.Budgets.ordered(Fx.Budgets{mi, lo, me, hi}), True{}, o) : {Fx.gbudget.rule(_, Fx.Budgets{mi, lo, me, hi}, c, l) == Fx.Tokens{Fx.gtokens(Fx.Budgets{mi, lo, me, hi}, c, l)} : Fx.GB}
  {==}

# the model reads the user's budget of the level as the laws do
def fg.at(+c: Fx.Customs, +l: Fx.Lv) -> {Fx.Customs.at(c, l) == Facts.customs_spec(c, l) : Maybe<&2, Nat>}:
  match c:
    case Fx.Customs{mi, lo, me, hi}:
      match l:
        case Fx.Minimal{}:
          {==}
        case Fx.Low{}:
          {==}
        case Fx.Medium{}:
          {==}
        case Fx.High{}:
          {==}

# x inside lo..hi is held as it is
def fg.kept.hi(+g: Bool, +x: Nat, +hi: Nat, +eg: {Nat.is_lt(hi, x) == g : Bool}, +b: {Nat.is_le(x, hi) == True{} : Bool}) -> {Fx.clamp.hi(g, x, hi) == x : Nat}:
  match g:
    case True{}:
      fb.clash({Fx.clamp.hi(True{}, x, hi) == x : Nat}, Nat.is_le(x, hi), LNat.pi.lt_nle(hi, x, eg), b)
    case False{}:
      {==}

def fg.kept.lo(+c: Bool, +x: Nat, +lo: Nat, +hi: Nat, +ec: {Nat.is_lt(x, lo) == c : Bool}, +a: {Nat.is_le(lo, x) == True{} : Bool}, +b: {Nat.is_le(x, hi) == True{} : Bool}) -> {Fx.clamp.lo(c, x, lo, hi) == x : Nat}:
  match c:
    case True{}:
      fb.clash({Fx.clamp.lo(True{}, x, lo, hi) == x : Nat}, Nat.is_le(lo, x), LNat.pi.lt_nle(x, lo, ec), a)
    case False{}:
      fg.kept.hi(Nat.is_lt(hi, x), x, hi, {==}, b)

def fg.kept(+x: Nat, +lo: Nat, +hi: Nat, +a: {Nat.is_le(lo, x) == True{} : Bool}, +b: {Nat.is_le(x, hi) == True{} : Bool}) -> {Fx.clamp(x, lo, hi) == x : Nat}:
  fg.kept.lo(Nat.is_lt(x, lo), x, lo, hi, {==}, a, b)

# the Google budget of a rule that never falls, with the user's budget n
# of the level, is the clamp of n
def fg.user.t(+mi: Nat, +lo: Nat, +me: Nat, +hi: Nat, +c: Fx.Customs, +l: Fx.Lv, +n: Nat, +u: {Facts.customs_spec(c, l) == Some{n} : Maybe<&2, Nat>}) -> {Fx.Tokens{Fx.gtokens(Fx.Budgets{mi, lo, me, hi}, c, l)} == Fx.Tokens{Fx.clamp(n, mi, hi)} : Fx.GB}:
  +ua = Equal.trans(Maybe<&2, Nat>, Fx.Customs.at(c, l), Facts.customs_spec(c, l), Some{n}, fg.at(c, l), u)
  %Equal.sym(Maybe<&2, Nat>, Fx.Customs.at(c, l), Some{n}, ua) : {Fx.Tokens{Fx.clamp(Maybe.default(&2, Nat, _, Fx.Budgets.at(Fx.Budgets{mi, lo, me, hi}, l)), mi, hi)} == Fx.Tokens{Fx.clamp(n, mi, hi)} : Fx.GB}
  {==}

def fg.user(+mi: Nat, +lo: Nat, +me: Nat, +hi: Nat, +c: Fx.Customs, +l: Fx.Lv, +n: Nat, +h: {Facts.rule_falls(mi, lo, me, hi) == False{} : Bool}, +u: {Facts.customs_spec(c, l) == Some{n} : Maybe<&2, Nat>}) -> {Fx.gbudget(Some{Fx.Budgets{mi, lo, me, hi}}, c, l) == Fx.Tokens{Fx.clamp(n, mi, hi)} : Fx.GB}:
  Equal.trans(Fx.GB, Fx.gbudget(Some{Fx.Budgets{mi, lo, me, hi}}, c, l), Fx.Tokens{Fx.gtokens(Fx.Budgets{mi, lo, me, hi}, c, l)}, Fx.Tokens{Fx.clamp(n, mi, hi)}, fg.tokens(mi, lo, me, hi, c, l, h), fg.user.t(mi, lo, me, hi, c, l, n, u))

# Tokens of equal budgets are equal
def fg.tok(+x: Nat, +y: Nat, +e: {x == y : Nat}) -> {Fx.Tokens{x} == Fx.Tokens{y} : Fx.GB}:
  %e : {Fx.Tokens{x} == Fx.Tokens{_} : Fx.GB}
  {==}

# Answer room (facts_room_*, facts_fit_budget_*)
# ----------------------------------------------

# the smaller of b and x is b or x
def fr.mm(+b: Nat, +x: Nat) -> {Bool.or(Nat.is_eq(Nat.min(b, x), b), Nat.is_eq(Nat.min(b, x), x)) == True{} : Bool}:
  match b x:
    case 0n x:
      {==}
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      fr.mm(p, q)

# a at most m: min(b, m - a) is b, or a plus it is m
def fr.cut(+b: Nat, +m: Nat, +a: Nat, +h: {Nat.is_le(a, m) == True{} : Bool}) -> {Bool.or(Nat.is_eq(Nat.min(b, Nat.sub(m, a)), b), Nat.is_eq(Nat.add(a, Nat.min(b, Nat.sub(m, a))), m)) == True{} : Bool}:
  match m a:
    case 0n 0n:
      fr.mm(b, 0n)
    case 1n+q 0n:
      fr.mm(b, 1n+q)
    case 0n 1n+p:
      LLogicLogic.pf.absurd_ft({Bool.or(Nat.is_eq(Nat.min(b, Nat.sub(0n, 1n+p)), b), Nat.is_eq(Nat.add(1n+p, Nat.min(b, Nat.sub(0n, 1n+p))), 0n)) == True{} : Bool}, h)
    case 1n+q 1n+p:
      fr.cut(b, q, p, h)

# Price rows (facts_tier_price_model_row_first, facts_price_*)
# -----------------------------------------------------------

# a row hits the model's lookup exactly when it is a row of the model for the tier
def fp.hit_m(+r: Fx.PRow, +m: Nat, +t: Nat) -> {Fx.PRow.hit(r, m, t, True{}) == Facts.row_of_model(r, m, t) : Bool}:
  match r:
    case Fx.PRow{rm, rt, k}:
      match rm:
        case None{}:
          fb.and_false_r(Nat.is_eq(rt, t))
        case Some{x}:
          fb.and_comm(Nat.is_eq(rt, t), Nat.is_eq(x, m))

# a row hits the every-model lookup exactly when it is a row of every model for the tier
def fp.hit_a(+r: Fx.PRow, +m: Nat, +t: Nat) -> {Fx.PRow.hit(r, m, t, False{}) == Facts.row_of_all(r, t) : Bool}:
  match r:
    case Fx.PRow{rm, rt, k}:
      match rm:
        case None{}:
          fb.and_true_r(Nat.is_eq(rt, t))
        case Some{x}:
          fb.and_false_r(Nat.is_eq(rt, t))

def fp.pick_f(+x: Bool, +ex: {x == False{} : Bool}, +r: Fx.PRow, +later: Maybe<&2, Nat>) -> {Fx.price.pick(x, r, later) == later : Maybe<&2, Nat>}:
  match x:
    case False{}:
      {==}
    case True{}:
      LLogicLogic.pf.absurd_tf({Fx.price.pick(True{}, r, later) == later : Maybe<&2, Nat>}, ex)

def fp.pick_t(+x: Bool, +ex: {x == True{} : Bool}, +r: Fx.PRow, +later: Maybe<&2, Nat>) -> {Fx.price.pick(x, r, later) == Some{Fx.PRow.mult(r)} : Maybe<&2, Nat>}:
  match x:
    case True{}:
      {==}
    case False{}:
      LLogicLogic.pf.absurd_ft({Fx.price.pick(False{}, r, later) == Some{Fx.PRow.mult(r)} : Maybe<&2, Nat>}, ex)

# no row of the model: the model's lookup finds nothing
def fp.none_m(+rows: List<&2, Fx.PRow>, +m: Nat, +t: Nat, +h: {Facts.rows_of_model(rows, m, t) == False{} : Bool}) -> {Fx.price.find(rows, m, t, True{}) == None{} : Maybe<&2, Nat>}:
  match rows:
    case Nil{}:
      {==}
    case r <> more:
      +hr = Equal.trans(Bool, Fx.PRow.hit(r, m, t, True{}), Facts.row_of_model(r, m, t), False{}, fp.hit_m(r, m, t), fb.or_fl(Facts.row_of_model(r, m, t), Facts.rows_of_model(more, m, t), h))
      Equal.trans(Maybe<&2, Nat>, Fx.price.pick(Fx.PRow.hit(r, m, t, True{}), r, Fx.price.find(more, m, t, True{})), Fx.price.find(more, m, t, True{}), None{}, fp.pick_f(Fx.PRow.hit(r, m, t, True{}), hr, r, Fx.price.find(more, m, t, True{})), fp.none_m(more, m, t, fb.or_fr(Facts.row_of_model(r, m, t), Facts.rows_of_model(more, m, t), h)))

# no row of every model: the every-model lookup finds nothing
def fp.none_a(+rows: List<&2, Fx.PRow>, +m: Nat, +t: Nat, +h: {Facts.rows_of_all(rows, t) == False{} : Bool}) -> {Fx.price.find(rows, m, t, False{}) == None{} : Maybe<&2, Nat>}:
  match rows:
    case Nil{}:
      {==}
    case r <> more:
      +hr = Equal.trans(Bool, Fx.PRow.hit(r, m, t, False{}), Facts.row_of_all(r, t), False{}, fp.hit_a(r, m, t), fb.or_fl(Facts.row_of_all(r, t), Facts.rows_of_all(more, t), h))
      Equal.trans(Maybe<&2, Nat>, Fx.price.pick(Fx.PRow.hit(r, m, t, False{}), r, Fx.price.find(more, m, t, False{})), Fx.price.find(more, m, t, False{}), None{}, fp.pick_f(Fx.PRow.hit(r, m, t, False{}), hr, r, Fx.price.find(more, m, t, False{})), fp.none_a(more, m, t, fb.or_fr(Facts.row_of_all(r, t), Facts.rows_of_all(more, t), h)))

# the model's lookup finds the first row of the model for the tier
def fp.first_m(+pre: List<&2, Fx.PRow>, +post: List<&2, Fx.PRow>, +m: Nat, +t: Nat, +k: Nat, +h: {Facts.rows_of_model(pre, m, t) == False{} : Bool}) -> {Fx.price.find(List.append(&2, Fx.PRow, pre, Fx.PRow{Some{m}, t, k} <> post), m, t, True{}) == Some{k} : Maybe<&2, Nat>}:
  match pre:
    case Nil{}:
      +hit = fb.and_tt(Nat.is_eq(t, t), Nat.is_eq(m, m), LNat.child.pc.eq_refl(t), LNat.child.pc.eq_refl(m))
      fp.pick_t(Fx.PRow.hit(Fx.PRow{Some{m}, t, k}, m, t, True{}), hit, Fx.PRow{Some{m}, t, k}, Fx.price.find(post, m, t, True{}))
    case r <> more:
      +X = List.append(&2, Fx.PRow, more, Fx.PRow{Some{m}, t, k} <> post)
      +hr = Equal.trans(Bool, Fx.PRow.hit(r, m, t, True{}), Facts.row_of_model(r, m, t), False{}, fp.hit_m(r, m, t), fb.or_fl(Facts.row_of_model(r, m, t), Facts.rows_of_model(more, m, t), h))
      Equal.trans(Maybe<&2, Nat>, Fx.price.pick(Fx.PRow.hit(r, m, t, True{}), r, Fx.price.find(X, m, t, True{})), Fx.price.find(X, m, t, True{}), Some{k}, fp.pick_f(Fx.PRow.hit(r, m, t, True{}), hr, r, Fx.price.find(X, m, t, True{})), fp.first_m(more, post, m, t, k, fb.or_fr(Facts.row_of_model(r, m, t), Facts.rows_of_model(more, m, t), h)))

# the every-model lookup finds the first row of every model for the tier
def fp.first_a(+pre: List<&2, Fx.PRow>, +post: List<&2, Fx.PRow>, +m: Nat, +t: Nat, +k: Nat, +h: {Facts.rows_of_all(pre, t) == False{} : Bool}) -> {Fx.price.find(List.append(&2, Fx.PRow, pre, Fx.PRow{None{}, t, k} <> post), m, t, False{}) == Some{k} : Maybe<&2, Nat>}:
  match pre:
    case Nil{}:
      +hit = fb.and_tt(Nat.is_eq(t, t), True{}, LNat.child.pc.eq_refl(t), {==})
      fp.pick_t(Fx.PRow.hit(Fx.PRow{None{}, t, k}, m, t, False{}), hit, Fx.PRow{None{}, t, k}, Fx.price.find(post, m, t, False{}))
    case r <> more:
      +X = List.append(&2, Fx.PRow, more, Fx.PRow{None{}, t, k} <> post)
      +hr = Equal.trans(Bool, Fx.PRow.hit(r, m, t, False{}), Facts.row_of_all(r, t), False{}, fp.hit_a(r, m, t), fb.or_fl(Facts.row_of_all(r, t), Facts.rows_of_all(more, t), h))
      Equal.trans(Maybe<&2, Nat>, Fx.price.pick(Fx.PRow.hit(r, m, t, False{}), r, Fx.price.find(X, m, t, False{})), Fx.price.find(X, m, t, False{}), Some{k}, fp.pick_f(Fx.PRow.hit(r, m, t, False{}), hr, r, Fx.price.find(X, m, t, False{})), fp.first_a(more, post, m, t, k, fb.or_fr(Facts.row_of_all(r, t), Facts.rows_of_all(more, t), h)))

def fp.or_some(+a: Maybe<&2, Nat>, +k: Nat, +ea: {a == Some{k} : Maybe<&2, Nat>}, +b: Maybe<&2, Nat>) -> {Fx.price.or(a, b) == Some{k} : Maybe<&2, Nat>}:
  %Equal.sym(Maybe<&2, Nat>, a, Some{k}, ea) : {Fx.price.or(_, b) == Some{k} : Maybe<&2, Nat>}
  {==}

def fp.or_none(+a: Maybe<&2, Nat>, +ea: {a == None{} : Maybe<&2, Nat>}, +b: Maybe<&2, Nat>) -> {Fx.price.or(a, b) == b : Maybe<&2, Nat>}:
  %Equal.sym(Maybe<&2, Nat>, a, None{}, ea) : {Fx.price.or(_, b) == b : Maybe<&2, Nat>}
  {==}
