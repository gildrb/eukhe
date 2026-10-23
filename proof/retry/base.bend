# eukhe: lemmas the proofs of area retry share

import Base
import ../../bend/ffi_retry.bend as Fr
import ../../bend/retry.bend as R
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/retry.bend as Retry
import ../../laws/wire.bend as Wire
import ../base/logic/bool.bend as LLogicBool
import ../base/logic/logic.bend as LLogicLogic
import ../base/nat.bend as LNat
import ../base/wire.bend as LWire
import ../wire/wire_bool_round_trip.bend as PWireBoolRoundTrip

def rp.add_zero(n: Nat) -> {Nat.add(n, 0n) == n : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      %rp.add_zero(p) : {1n+Nat.add(p, 0n) == 1n+_ : Nat}
      {==}

def rp.add_none(+s: Nat, +x: Nat, e: {x == 0n : Nat}) -> {Nat.add(s, x) == s : Nat}:
  %Equal.sym(Nat, x, 0n, e) : {Nat.add(s, _) == s : Nat}
  rp.add_zero(s)

# (R6) The idle deadline
# ----------------------

def rp.le_refl(n: Nat) -> {Nat.is_le(n, n) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      rp.le_refl(p)

def rp.le_add(n: Nat, +d: Nat) -> {Nat.is_le(n, Nat.add(n, d)) == True{} : Bool}:
  match n:
    case 0n:
      LNat.rp.le_zero(d)
    case 1n+p:
      rp.le_add(p, d)

# The exact laws
# --------------

# Order facts
# -----------

def rx.lt_le(c: Cmp, e: {Cmp.is_lt(c) == True{} : Bool}) -> {Cmp.is_le(c) == True{} : Bool}:
  match c:
    case LT{}:
      {==}
    case EQ{}:
      LLogicLogic.rp.absurdF({True{} == True{} : Bool}, e)
    case GT{}:
      LLogicLogic.rp.absurdF({False{} == True{} : Bool}, e)

def rx.le_of_not_gt(c: Cmp, e: {Cmp.is_gt(c) == False{} : Bool}) -> {Cmp.is_le(c) == True{} : Bool}:
  match c:
    case LT{}:
      {==}
    case EQ{}:
      {==}
    case GT{}:
      LLogicLogic.rp.absurdT({False{} == True{} : Bool}, e)

# a <= b and b <= c give a <= c
def rx.le_trans(+a: Nat, +b: Nat, +c: Nat, h1: {Nat.is_le(a, b) == True{} : Bool}, h2: {Nat.is_le(b, c) == True{} : Bool}) -> {Nat.is_le(a, c) == True{} : Bool}:
  match a b c:
    case 0n b c:
      LNat.rp.le_zero(c)
    case 1n+p 0n c:
      LLogicLogic.rp.absurdF({Nat.is_le(1n+p, c) == True{} : Bool}, h1)
    case 1n+p 1n+q 0n:
      LLogicLogic.rp.absurdF({Nat.is_le(1n+p, 0n) == True{} : Bool}, h2)
    case 1n+p 1n+q 1n+r:
      rx.le_trans(p, q, r, h1, h2)

# a <= b and c > b give a <= c
def rx.le_gt(+a: Nat, +b: Nat, +c: Nat, h1: {Nat.is_le(a, b) == True{} : Bool}, h2: {Nat.is_gt(c, b) == True{} : Bool}) -> {Nat.is_le(a, c) == True{} : Bool}:
  match a b c:
    case 0n b c:
      LNat.rp.le_zero(c)
    case 1n+p 0n c:
      LLogicLogic.rp.absurdF({Nat.is_le(1n+p, c) == True{} : Bool}, h1)
    case 1n+p 1n+q 0n:
      LLogicLogic.rp.absurdF({Nat.is_le(1n+p, 0n) == True{} : Bool}, h2)
    case 1n+p 1n+q 1n+r:
      rx.le_gt(p, q, r, h1, h2)

# min(a, b) = a when a <= b
def rx.min_l(+a: Nat, +b: Nat, h: {Nat.is_le(a, b) == True{} : Bool}) -> {Nat.min(a, b) == a : Nat}:
  match a b:
    case 0n b:
      {==}
    case 1n+p 0n:
      LLogicLogic.rp.absurdF({Nat.min(1n+p, 0n) == 1n+p : Nat}, h)
    case 1n+p 1n+q:
      %rx.min_l(p, q, h) : {1n+Nat.min(p, q) == 1n+_ : Nat}
      {==}

# min(a, b) = b when b <= a
def rx.min_r(+a: Nat, +b: Nat, h: {Nat.is_le(b, a) == True{} : Bool}) -> {Nat.min(a, b) == b : Nat}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      LLogicLogic.rp.absurdF({Nat.min(0n, 1n+q) == 1n+q : Nat}, h)
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      %rx.min_r(p, q, h) : {1n+Nat.min(p, q) == 1n+_ : Nat}
      {==}

# min(a, b) > x when a > x and b > x
def rx.gt_min(+a: Nat, +b: Nat, +x: Nat, ha: {Nat.is_gt(a, x) == True{} : Bool}, hb: {Nat.is_gt(b, x) == True{} : Bool}) -> {Nat.is_gt(Nat.min(a, b), x) == True{} : Bool}:
  match a b x:
    case 0n b 0n:
      LLogicLogic.rp.absurdF({Nat.is_gt(0n, 0n) == True{} : Bool}, ha)
    case 0n b 1n+r:
      LLogicLogic.rp.absurdF({Nat.is_gt(0n, 1n+r) == True{} : Bool}, ha)
    case 1n+p 0n 0n:
      LLogicLogic.rp.absurdF({Nat.is_gt(0n, 0n) == True{} : Bool}, hb)
    case 1n+p 0n 1n+r:
      LLogicLogic.rp.absurdF({Nat.is_gt(0n, 1n+r) == True{} : Bool}, hb)
    case 1n+p 1n+q 0n:
      {==}
    case 1n+p 1n+q 1n+r:
      rx.gt_min(p, q, r, ha, hb)

# a > b gives b < a
def rx.gt_lt(+a: Nat, +b: Nat, h: {Nat.is_gt(a, b) == True{} : Bool}) -> {Nat.is_lt(b, a) == True{} : Bool}:
  match a b:
    case 0n 0n:
      LLogicLogic.rp.absurdF({Nat.is_lt(0n, 0n) == True{} : Bool}, h)
    case 0n 1n+q:
      LLogicLogic.rp.absurdF({Nat.is_lt(1n+q, 0n) == True{} : Bool}, h)
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      rx.gt_lt(p, q, h)

# 0 < x gives 0 < b + x
def rx.lt0_add(b: Nat, +x: Nat, h: {Nat.is_lt(0n, x) == True{} : Bool}) -> {Nat.is_lt(0n, Nat.add(b, x)) == True{} : Bool}:
  match b:
    case 0n:
      h
    case 1n+q:
      {==}

# x > d - b gives d < b + x
def rx.lt_sub(+d: Nat, +b: Nat, +x: Nat, h: {Nat.is_lt(Nat.sub(d, b), x) == True{} : Bool}) -> {Nat.is_lt(d, Nat.add(b, x)) == True{} : Bool}:
  match d b:
    case 0n b:
      rx.lt0_add(b, x, h)
    case 1n+p 0n:
      h
    case 1n+p 1n+q:
      rx.lt_sub(p, q, x, h)

# Bool facts
# ----------

def rx.and_f(a: Bool, -b: Bool, e: {b == False{} : Bool}) -> {Bool.and(a, b) == False{} : Bool}:
  match a:
    case True{}:
      e
    case False{}:
      {==}

# (R2) The step: the bounded doubling is the doubling, capped
# -----------------------------------------------------------

def rx.twice_zero(k: Nat) -> {0n == Retry.rs.twice(k, 0n) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+j:
      rx.twice_zero(j)

# b <= twice(k, b)
def rx.twice_ge(k: Nat, +b: Nat) -> {Nat.is_le(b, Retry.rs.twice(k, b)) == True{} : Bool}:
  match k:
    case 0n:
      rp.le_refl(b)
    case 1n++j:
      rx.le_trans(b, Nat.add(b, b), Retry.rs.twice(j, Nat.add(b, b)), rp.le_add(b, b), rx.twice_ge(j, Nat.add(b, b)))

def rx.double_go(k: Nat, h: Bool, +b: Nat, +cap: Nat, eh: {R.double.halt(b, cap) == h : Bool}) -> {R.double.go(k, h, b, cap) == Nat.min(Retry.rs.twice(k, b), cap) : Nat}:
  match k h:
    case 0n h:
      {==}
    case 1n++j True{}:
      match b:
        case 0n:
          %rx.twice_zero(j) : {0n == Nat.min(_, cap) : Nat}
          {==}
        case 1n+p:
          +b2 = Nat.add(1n+p, 1n+p)
          +lt = rx.lt_sub(cap, 1n+p, 1n+p, rx.gt_lt(1n+p, Nat.sub(cap, 1n+p), eh))
          +le = rx.le_trans(cap, b2, Retry.rs.twice(j, b2), rx.lt_le(Nat.cmp(cap, b2), lt), rx.twice_ge(j, b2))
          Equal.sym(Nat, Nat.min(Retry.rs.twice(j, b2), cap), cap, rx.min_r(Retry.rs.twice(j, b2), cap, le))
    case 1n+j False{}:
      rx.double_go(j, R.double.halt(Nat.add(b, b), cap), Nat.add(b, b), cap, {==})

# the bounded doubling of the model is min(b doubled k times, cap)
def rx.double(k: Nat, +b: Nat, +cap: Nat) -> {R.double(k, b, cap) == Nat.min(Retry.rs.twice(k, b), cap) : Nat}:
  rx.double_go(k, R.double.halt(b, cap), b, cap, {==})

# the Nat and Bool round trips, turned for rewriting
def rw.rt(+n: Nat, +rest: String, h: {LawsBase.wire_fits(n) == True{} : Bool}) -> {Wr.Got{n, rest} == Wr.get_nat(Wr.put_nat(n, rest)) : Wr.Dec<Nat>}:
  Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(n, rest)), Wr.Got{n, rest}, Wire.wire_nat_round_trip(n, rest, h))

def rw.brt(+b: Bool, +rest: String) -> {Wr.Got{b, rest} == Wr.get_bool(Wr.put_bool(b, rest)) : Wr.Dec<Bool>}:
  Equal.sym(Wr.Dec<Bool>, Wr.get_bool(Wr.put_bool(b, rest)), Wr.Got{b, rest}, Wire.wire_bool_round_trip(b, rest))

# Round trip
# ----------

def rw.mnat_rt(m: Maybe<&2, Nat>, +rest: String, h: {Retry.rs.mfits(m) == True{} : Bool}) -> {Fr.get_mnat(Fr.put_mnat(m, rest)) == Wr.Got{m, rest} : Wr.Dec<Maybe<&2, Nat>>}:
  match m:
    case None{}:
      %rw.rt(0n, rest, {==}) : {Fr.get_mnat.tag(_) == Wr.Got{None{}, rest} : Wr.Dec<Maybe<&2, Nat>>}
      {==}
    case Some{+n}:
      %rw.rt(1n, Wr.put_nat(n, rest), {==}) : {Fr.get_mnat.tag(_) == Wr.Got{Some{n}, rest} : Wr.Dec<Maybe<&2, Nat>>}
      %rw.rt(n, rest, h) : {Fr.get_mnat.some(_) == Wr.Got{Some{n}, rest} : Wr.Dec<Maybe<&2, Nat>>}
      {==}

def rw.cause_rt(k: R.Cause) -> {Fr.cause.of(Fr.cause.tag(k)) == Some{k} : Maybe<&2, R.Cause>}:
  match k:
    case R.Refusal{}:
      {==}
    case R.Safety{}:
      {==}
    case R.PaymentRequired{}:
      {==}
    case R.Overloaded{}:
      {==}
    case R.RateLimit{}:
      {==}
    case R.ServerError{}:
      {==}
    case R.Auth{}:
      {==}
    case R.Permission{}:
      {==}
    case R.InvalidRequest{}:
      {==}
    case R.MalformedResponse{}:
      {==}
    case R.StreamDrop{}:
      {==}
    case R.StreamStalled{}:
      {==}
    case R.StreamRepeating{}:
      {==}
    case R.Unknown{}:
      {==}

def rw.cause_fits(k: R.Cause) -> {LawsBase.wire_fits(Fr.cause.tag(k)) == True{} : Bool}:
  match k:
    case R.Refusal{}:
      {==}
    case R.Safety{}:
      {==}
    case R.PaymentRequired{}:
      {==}
    case R.Overloaded{}:
      {==}
    case R.RateLimit{}:
      {==}
    case R.ServerError{}:
      {==}
    case R.Auth{}:
      {==}
    case R.Permission{}:
      {==}
    case R.InvalidRequest{}:
      {==}
    case R.MalformedResponse{}:
      {==}
    case R.StreamDrop{}:
      {==}
    case R.StreamStalled{}:
      {==}
    case R.StreamRepeating{}:
      {==}
    case R.Unknown{}:
      {==}

def rw.mcause_rt(m: Maybe<&2, R.Cause>, +rest: String) -> {Fr.get_mcause(Fr.put_mcause(m, rest)) == Wr.Got{m, rest} : Wr.Dec<Maybe<&2, R.Cause>>}:
  match m:
    case None{}:
      %rw.rt(0n, rest, {==}) : {Fr.get_mcause.tag(_) == Wr.Got{None{}, rest} : Wr.Dec<Maybe<&2, R.Cause>>}
      {==}
    case Some{+k}:
      %rw.rt(1n, Wr.put_nat(Fr.cause.tag(k), rest), {==}) : {Fr.get_mcause.tag(_) == Wr.Got{Some{k}, rest} : Wr.Dec<Maybe<&2, R.Cause>>}
      %rw.rt(Fr.cause.tag(k), rest, rw.cause_fits(k)) : {Fr.get_mcause.some(_) == Wr.Got{Some{k}, rest} : Wr.Dec<Maybe<&2, R.Cause>>}
      %Equal.sym(Maybe<&2, R.Cause>, Fr.cause.of(Fr.cause.tag(k)), Some{k}, rw.cause_rt(k)) : {Fr.get_mcause.known(_, rest) == Wr.Got{Some{k}, rest} : Wr.Dec<Maybe<&2, R.Cause>>}
      {==}

def rw.facts_rt(f: R.Facts, +rest: String, h: {Retry.rs.req_fits(Fr.QClassify{f}) == True{} : Bool}) -> {Fr.get_facts(Fr.put_facts(f, rest)) == Wr.Got{f, rest} : Wr.Dec<R.Facts>}:
  match f:
    case R.Facts{+p, +l, +st, +k, +t}:
      +F = {R.Facts{p, l, st, k, t} : R.Facts}
      +s4 = Wr.put_bool(t, rest)
      +s3 = Fr.put_mcause(k, s4)
      +s2 = Fr.put_mnat(st, s3)
      +s1 = Wr.put_bool(l, s2)
      %rw.brt(p, s1) : {Fr.get_facts.parked(_) == Wr.Got{F, rest} : Wr.Dec<R.Facts>}
      %rw.brt(l, s2) : {Fr.get_facts.limit(p, _) == Wr.Got{F, rest} : Wr.Dec<R.Facts>}
      %Equal.sym(Wr.Dec<Maybe<&2, Nat>>, Fr.get_mnat(s2), Wr.Got{st, s3}, rw.mnat_rt(st, s3, h)) : {Fr.get_facts.status(p, l, _) == Wr.Got{F, rest} : Wr.Dec<R.Facts>}
      %Equal.sym(Wr.Dec<Maybe<&2, R.Cause>>, Fr.get_mcause(s3), Wr.Got{k, s4}, rw.mcause_rt(k, s4)) : {Fr.get_facts.kind(p, l, st, _) == Wr.Got{F, rest} : Wr.Dec<R.Facts>}
      %rw.brt(t, rest) : {Fr.get_facts.text(p, l, st, k, _) == Wr.Got{F, rest} : Wr.Dec<R.Facts>}
      {==}

# one attempt fits the wire
def rw.fit1(t: R.Tried) -> Bool:
  match t:
    case R.Tried{at, w}:
      Bool.and(LawsBase.wire_fits(at), Retry.rs.mfits(w))

def rw.fit_l(t: R.Tried, -ts: List<&2, R.Tried>, h: {Retry.rs.tried_fit(t <> ts) == True{} : Bool}) -> {rw.fit1(t) == True{} : Bool}:
  match t:
    case R.Tried{+at, +w}:
      LLogicBool.rp.and_l(Bool.and(LawsBase.wire_fits(at), Retry.rs.mfits(w)), Retry.rs.tried_fit(ts), h)

def rw.fit_r(t: R.Tried, -ts: List<&2, R.Tried>, h: {Retry.rs.tried_fit(t <> ts) == True{} : Bool}) -> {Retry.rs.tried_fit(ts) == True{} : Bool}:
  match t:
    case R.Tried{+at, +w}:
      LLogicBool.rp.and_r(Bool.and(LawsBase.wire_fits(at), Retry.rs.mfits(w)), Retry.rs.tried_fit(ts), h)

def rw.tried_rt(t: R.Tried, +rest: String, +h: {rw.fit1(t) == True{} : Bool}) -> {Fr.get_tried(Fr.put_tried(t, rest)) == Wr.Got{t, rest} : Wr.Dec<R.Tried>}:
  match t:
    case R.Tried{+at, +w}:
      %rw.rt(at, Fr.put_mnat(w, rest), LLogicBool.rp.and_l(LawsBase.wire_fits(at), Retry.rs.mfits(w), h)) : {Fr.get_tried.at(_) == Wr.Got{R.Tried{at, w}, rest} : Wr.Dec<R.Tried>}
      %Equal.sym(Wr.Dec<Maybe<&2, Nat>>, Fr.get_mnat(Fr.put_mnat(w, rest)), Wr.Got{w, rest}, rw.mnat_rt(w, rest, LLogicBool.rp.and_r(LawsBase.wire_fits(at), Retry.rs.mfits(w), h))) : {Fr.get_tried.wait(at, _) == Wr.Got{R.Tried{at, w}, rest} : Wr.Dec<R.Tried>}
      {==}

# the items of a list of attempts, then rest
def rw.items(ts: List<&2, R.Tried>, rest: String) -> String:
  match ts:
    case Nil{}:
      rest
    case t <> r:
      Fr.put_tried(t, rw.items(r, rest))

def rw.go(ts: List<&2, R.Tried>, +rest: String) -> {Wr.put_list.go(~R.Tried, ~Fr.put_tried, ts, rest) == (R.length(ts), rw.items(ts, rest)) : Nat & String}:
  match ts:
    case Nil{}:
      {==}
    case +t <> +r:
      %Equal.sym(Nat & String, Wr.put_list.go(~R.Tried, ~Fr.put_tried, r, rest), (R.length(r), rw.items(r, rest)), rw.go(r, rest)) : {Wr.put_list.step(~R.Tried, ~Fr.put_tried, t, _) == (1n+R.length(r), Fr.put_tried(t, rw.items(r, rest))) : Nat & String}
      {==}

# a list of attempts is its count, then its items
def rw.put_list(+ts: List<&2, R.Tried>, +rest: String) -> {Wr.put_list(~R.Tried, ~Fr.put_tried, ts, rest) == Wr.put_nat(R.length(ts), rw.items(ts, rest)) : String}:
  Equal.cong(Nat & String, String, x => Wr.put_list.fin(x), Wr.put_list.go(~R.Tried, ~Fr.put_tried, ts, rest), (R.length(ts), rw.items(ts, rest)), rw.go(ts, rest))

def rw.list_go(ts: List<&2, R.Tried>, +t: R.Tried, +rest: String, +hf: {Retry.rs.tried_fit(t <> ts) == True{} : Bool}) -> {Wr.get_list.go(~R.Tried, ~Fr.get_tried, R.length(ts), Fr.get_tried(Fr.put_tried(t, rw.items(ts, rest)))) == Wr.Got{t <> ts, rest} : Wr.Dec<List<&2, R.Tried>>}:
  match ts:
    case Nil{}:
      %Equal.sym(Wr.Dec<R.Tried>, Fr.get_tried(Fr.put_tried(t, rest)), Wr.Got{t, rest}, rw.tried_rt(t, rest, rw.fit_l(t, Nil{}, hf))) : {Wr.get_list.go(~R.Tried, ~Fr.get_tried, 0n, _) == Wr.Got{[t], rest} : Wr.Dec<List<&2, R.Tried>>}
      {==}
    case +t2 <> +ts2:
      %Equal.sym(Wr.Dec<R.Tried>, Fr.get_tried(Fr.put_tried(t, rw.items(t2 <> ts2, rest))), Wr.Got{t, rw.items(t2 <> ts2, rest)}, rw.tried_rt(t, rw.items(t2 <> ts2, rest), rw.fit_l(t, t2 <> ts2, hf))) : {Wr.get_list.go(~R.Tried, ~Fr.get_tried, 1n+R.length(ts2), _) == Wr.Got{t <> t2 <> ts2, rest} : Wr.Dec<List<&2, R.Tried>>}
      %Equal.sym(Wr.Dec<List<&2, R.Tried>>, Wr.get_list.go(~R.Tried, ~Fr.get_tried, R.length(ts2), Fr.get_tried(Fr.put_tried(t2, rw.items(ts2, rest)))), Wr.Got{t2 <> ts2, rest}, rw.list_go(ts2, t2, rest, rw.fit_r(t, t2 <> ts2, hf))) : {Wr.get_list.cons(R.Tried, t, _) == Wr.Got{t <> t2 <> ts2, rest} : Wr.Dec<List<&2, R.Tried>>}
      {==}

def rw.list_start(ts: List<&2, R.Tried>, +rest: String, +hf: {Retry.rs.tried_fit(ts) == True{} : Bool}) -> {Wr.get_list.start(~R.Tried, ~Fr.get_tried, Wr.Got{R.length(ts), rw.items(ts, rest)}) == Wr.Got{ts, rest} : Wr.Dec<List<&2, R.Tried>>}:
  match ts:
    case Nil{}:
      {==}
    case +t <> +r:
      rw.list_go(r, t, rest, hf)

# a list of attempts that fits reads back
def rw.list_rt(+ts: List<&2, R.Tried>, +rest: String, hl: {LawsBase.wire_fits(R.length(ts)) == True{} : Bool}, +hf: {Retry.rs.tried_fit(ts) == True{} : Bool}) -> {Wr.get_list(~R.Tried, ~Fr.get_tried, Wr.put_list(~R.Tried, ~Fr.put_tried, ts, rest)) == Wr.Got{ts, rest} : Wr.Dec<List<&2, R.Tried>>}:
  %Equal.sym(String, Wr.put_list(~R.Tried, ~Fr.put_tried, ts, rest), Wr.put_nat(R.length(ts), rw.items(ts, rest)), rw.put_list(ts, rest)) : {Wr.get_list(~R.Tried, ~Fr.get_tried, _) == Wr.Got{ts, rest} : Wr.Dec<List<&2, R.Tried>>}
  %rw.rt(R.length(ts), rw.items(ts, rest), hl) : {Wr.get_list.start(~R.Tried, ~Fr.get_tried, _) == Wr.Got{ts, rest} : Wr.Dec<List<&2, R.Tried>>}
  rw.list_start(ts, rest, hf)

def rw.req_rt(q: Fr.Req, +rest: String, +h: {Retry.rs.req_fits(q) == True{} : Bool}) -> {Fr.get_req(Fr.put_req(q, rest)) == Wr.Got{q, rest} : Wr.Dec<Fr.Req>}:
  match q:
    case Fr.QClassify{+f}:
      %rw.rt(0n, Fr.put_facts(f, rest), {==}) : {Fr.get_req.start(_) == Wr.Got{Fr.QClassify{f}, rest} : Wr.Dec<Fr.Req>}
      %Equal.sym(Wr.Dec<R.Facts>, Fr.get_facts(Fr.put_facts(f, rest)), Wr.Got{f, rest}, rw.facts_rt(f, rest, h)) : {Fr.get_classify(_) == Wr.Got{Fr.QClassify{f}, rest} : Wr.Dec<Fr.Req>}
      {==}
    case Fr.QWait{+b, +a, +c, +d, +sv}:
      +ha = LLogicBool.rp.and_l(Bool.and(LawsBase.wire_fits(b), LawsBase.wire_fits(a)), Bool.and(Bool.and(LawsBase.wire_fits(c), LawsBase.wire_fits(d)), Retry.rs.mfits(sv)), h)
      +hb = LLogicBool.rp.and_r(Bool.and(LawsBase.wire_fits(b), LawsBase.wire_fits(a)), Bool.and(Bool.and(LawsBase.wire_fits(c), LawsBase.wire_fits(d)), Retry.rs.mfits(sv)), h)
      +hc = LLogicBool.rp.and_l(Bool.and(LawsBase.wire_fits(c), LawsBase.wire_fits(d)), Retry.rs.mfits(sv), hb)
      +Q = {Fr.QWait{b, a, c, d, sv} : Fr.Req}
      +s5 = Fr.put_mnat(sv, rest)
      %rw.rt(1n, Wr.put_nat(b, Wr.put_nat(a, Wr.put_nat(c, Wr.put_nat(d, s5)))), {==}) : {Fr.get_req.start(_) == Wr.Got{Q, rest} : Wr.Dec<Fr.Req>}
      %rw.rt(b, Wr.put_nat(a, Wr.put_nat(c, Wr.put_nat(d, s5))), LLogicBool.rp.and_l(LawsBase.wire_fits(b), LawsBase.wire_fits(a), ha)) : {Fr.get_wait(_) == Wr.Got{Q, rest} : Wr.Dec<Fr.Req>}
      %rw.rt(a, Wr.put_nat(c, Wr.put_nat(d, s5)), LLogicBool.rp.and_r(LawsBase.wire_fits(b), LawsBase.wire_fits(a), ha)) : {Fr.get_wait.attempt(b, _) == Wr.Got{Q, rest} : Wr.Dec<Fr.Req>}
      %rw.rt(c, Wr.put_nat(d, s5), LLogicBool.rp.and_l(LawsBase.wire_fits(c), LawsBase.wire_fits(d), hc)) : {Fr.get_wait.cap(b, a, _) == Wr.Got{Q, rest} : Wr.Dec<Fr.Req>}
      %rw.rt(d, s5, LLogicBool.rp.and_r(LawsBase.wire_fits(c), LawsBase.wire_fits(d), hc)) : {Fr.get_wait.draw(b, a, c, _) == Wr.Got{Q, rest} : Wr.Dec<Fr.Req>}
      %Equal.sym(Wr.Dec<Maybe<&2, Nat>>, Fr.get_mnat(s5), Wr.Got{sv, rest}, rw.mnat_rt(sv, rest, LLogicBool.rp.and_r(Bool.and(LawsBase.wire_fits(c), LawsBase.wire_fits(d)), Retry.rs.mfits(sv), hb))) : {Fr.get_wait.server(b, a, c, d, _) == Wr.Got{Q, rest} : Wr.Dec<Fr.Req>}
      {==}
    case Fr.QFailover{+len, +ts, p}:
      match p:
        case R.Policy{+sw, +b, +m}:
          +A = Bool.and(LawsBase.wire_fits(len), Bool.and(LawsBase.wire_fits(R.length(ts)), Retry.rs.tried_fit(ts)))
          +B = Bool.and(LawsBase.wire_fits(sw), Bool.and(LawsBase.wire_fits(b), LawsBase.wire_fits(m)))
          +ha = LLogicBool.rp.and_l(A, B, h)
          +hb = LLogicBool.rp.and_r(A, B, h)
          +hts = LLogicBool.rp.and_r(LawsBase.wire_fits(len), Bool.and(LawsBase.wire_fits(R.length(ts)), Retry.rs.tried_fit(ts)), ha)
          +hbm = LLogicBool.rp.and_r(LawsBase.wire_fits(sw), Bool.and(LawsBase.wire_fits(b), LawsBase.wire_fits(m)), hb)
          +Q = {Fr.QFailover{len, ts, R.Policy{sw, b, m}} : Fr.Req}
          +s3 = Fr.put_policy(R.Policy{sw, b, m}, rest)
          +s2 = Wr.put_list(~R.Tried, ~Fr.put_tried, ts, s3)
          %rw.rt(2n, Wr.put_nat(len, s2), {==}) : {Fr.get_req.start(_) == Wr.Got{Q, rest} : Wr.Dec<Fr.Req>}
          %rw.rt(len, s2, LLogicBool.rp.and_l(LawsBase.wire_fits(len), Bool.and(LawsBase.wire_fits(R.length(ts)), Retry.rs.tried_fit(ts)), ha)) : {Fr.get_failover(_) == Wr.Got{Q, rest} : Wr.Dec<Fr.Req>}
          %Equal.sym(Wr.Dec<List<&2, R.Tried>>, Wr.get_list(~R.Tried, ~Fr.get_tried, s2), Wr.Got{ts, s3}, rw.list_rt(ts, s3, LLogicBool.rp.and_l(LawsBase.wire_fits(R.length(ts)), Retry.rs.tried_fit(ts), hts), LLogicBool.rp.and_r(LawsBase.wire_fits(R.length(ts)), Retry.rs.tried_fit(ts), hts))) : {Fr.get_failover.tried(len, _) == Wr.Got{Q, rest} : Wr.Dec<Fr.Req>}
          %rw.rt(sw, Wr.put_nat(b, Wr.put_nat(m, rest)), LLogicBool.rp.and_l(LawsBase.wire_fits(sw), Bool.and(LawsBase.wire_fits(b), LawsBase.wire_fits(m)), hb)) : {Fr.get_failover.policy(len, ts, Fr.get_policy.switches(_)) == Wr.Got{Q, rest} : Wr.Dec<Fr.Req>}
          %rw.rt(b, Wr.put_nat(m, rest), LLogicBool.rp.and_l(LawsBase.wire_fits(b), LawsBase.wire_fits(m), hbm)) : {Fr.get_failover.policy(len, ts, Fr.get_policy.base(sw, _)) == Wr.Got{Q, rest} : Wr.Dec<Fr.Req>}
          %rw.rt(m, rest, LLogicBool.rp.and_r(LawsBase.wire_fits(b), LawsBase.wire_fits(m), hbm)) : {Fr.get_failover.policy(len, ts, Fr.get_policy.max(sw, b, _)) == Wr.Got{Q, rest} : Wr.Dec<Fr.Req>}
          {==}
    case Fr.QStall{+i}:
      %rw.rt(3n, Wr.put_nat(i, rest), {==}) : {Fr.get_req.start(_) == Wr.Got{Fr.QStall{i}, rest} : Wr.Dec<Fr.Req>}
      %rw.rt(i, rest, h) : {Fr.get_stall(_) == Wr.Got{Fr.QStall{i}, rest} : Wr.Dec<Fr.Req>}
      {==}
