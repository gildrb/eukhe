# eukhe: lemmas the proofs of area retry_ffi share: the laws' spelling is
# the entry's encoding; every number and count the entry's decoder reads
# fits the wire; the entry's decisions are no error form

import Base
import ../../bend/ffi_retry.bend as Fr
import ../../bend/retry.bend as R
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire
import ../../laws/retry.bend as Retry
import ../../laws/retry_ffi.bend as RetryFfi
import ../wire/wire_nat_decoded_fits.bend as PWireNatDecodedFits
import ../wire/wire_nat_not_err.bend as PWireNatNotErr
import ../base/staging.bend as LStg

# Spelling
# --------

def rf.mnat(m: Maybe<&2, Nat>, rest: String) -> {RetryFfi.spell_mnat(m, rest) == Fr.put_mnat(m, rest) : String}:
  match m:
    case None{}:
      {==}
    case Some{n}:
      {==}

def rf.cause(k: R.Cause) -> {RetryFfi.cause_num(k) == Fr.cause.tag(k) : Nat}:
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

def rf.mcause(m: Maybe<&2, R.Cause>, rest: String) -> {RetryFfi.spell_mcause(m, rest) == Fr.put_mcause(m, rest) : String}:
  match m:
    case None{}:
      {==}
    case Some{+k}:
      %Equal.sym(Nat, RetryFfi.cause_num(k), Fr.cause.tag(k), rf.cause(k)) : {Wr.put_nat(1n, Wr.put_nat(_, rest)) == Fr.put_mcause(Some{k}, rest) : String}
      {==}

def rf.tried(t: R.Tried, rest: String) -> {RetryFfi.spell_tried(t, rest) == Fr.put_tried(t, rest) : String}:
  match t:
    case R.Tried{at, w}:
      Equal.cong(String, String, x => Wr.put_nat(at, x), RetryFfi.spell_mnat(w, rest), Fr.put_mnat(w, rest), rf.mnat(w, rest))

def rf.step(x: R.Tried, p: Nat & String) -> {Wr.put_list.step(~R.Tried, ~RetryFfi.spell_tried, x, p) == Wr.put_list.step(~R.Tried, ~Fr.put_tried, x, p) : Nat & String}:
  (n, s) = p
  Equal.cong(String, Nat & String, y => (1n+n, y), RetryFfi.spell_tried(x, s), Fr.put_tried(x, s), rf.tried(x, s))

def rf.put_go(ts: List<&2, R.Tried>, +rest: String) -> {Wr.put_list.go(~R.Tried, ~RetryFfi.spell_tried, ts, rest) == Wr.put_list.go(~R.Tried, ~Fr.put_tried, ts, rest) : Nat & String}:
  match ts:
    case Nil{}:
      {==}
    case +x <> +t:
      %Equal.sym(Nat & String, Wr.put_list.go(~R.Tried, ~RetryFfi.spell_tried, t, rest), Wr.put_list.go(~R.Tried, ~Fr.put_tried, t, rest), rf.put_go(t, rest)) : {Wr.put_list.step(~R.Tried, ~RetryFfi.spell_tried, x, _) == Wr.put_list.step(~R.Tried, ~Fr.put_tried, x, Wr.put_list.go(~R.Tried, ~Fr.put_tried, t, rest)) : Nat & String}
      rf.step(x, Wr.put_list.go(~R.Tried, ~Fr.put_tried, t, rest))

def rf.put_list(+ts: List<&2, R.Tried>, +rest: String) -> {Wr.put_list(~R.Tried, ~RetryFfi.spell_tried, ts, rest) == Wr.put_list(~R.Tried, ~Fr.put_tried, ts, rest) : String}:
  Equal.cong(Nat & String, String, y => Wr.put_list.fin(y), Wr.put_list.go(~R.Tried, ~RetryFfi.spell_tried, ts, rest), Wr.put_list.go(~R.Tried, ~Fr.put_tried, ts, rest), rf.put_go(ts, rest))

# the laws spell every request, with any input after it, as the entry's
# encoder writes it
def rf.req(q: Fr.Req, +rest: String) -> {RetryFfi.spell_req(q, rest) == Fr.put_req(q, rest) : String}:
  match q:
    case Fr.QClassify{f}:
      match f:
        case R.Facts{parked, limit, +status, +kind, +text}:
          %Equal.sym(String, RetryFfi.spell_mcause(kind, Wr.put_bool(text, rest)), Fr.put_mcause(kind, Wr.put_bool(text, rest)), rf.mcause(kind, Wr.put_bool(text, rest))) : {Wr.put_nat(0n, Wr.put_bool(parked, Wr.put_bool(limit, RetryFfi.spell_mnat(status, _)))) == Fr.put_req(Fr.QClassify{R.Facts{parked, limit, status, kind, text}}, rest) : String}
          %Equal.sym(String, RetryFfi.spell_mnat(status, Fr.put_mcause(kind, Wr.put_bool(text, rest))), Fr.put_mnat(status, Fr.put_mcause(kind, Wr.put_bool(text, rest))), rf.mnat(status, Fr.put_mcause(kind, Wr.put_bool(text, rest)))) : {Wr.put_nat(0n, Wr.put_bool(parked, Wr.put_bool(limit, _))) == Fr.put_req(Fr.QClassify{R.Facts{parked, limit, status, kind, text}}, rest) : String}
          {==}
    case Fr.QWait{base, attempt, cap, draw, server}:
      Equal.cong(String, String, x => Wr.put_nat(1n, Wr.put_nat(base, Wr.put_nat(attempt, Wr.put_nat(cap, Wr.put_nat(draw, x))))), RetryFfi.spell_mnat(server, rest), Fr.put_mnat(server, rest), rf.mnat(server, rest))
    case Fr.QFailover{len, tried, p}:
      match p:
        case R.Policy{switches, base, max}:
          Equal.cong(String, String, x => Wr.put_nat(2n, Wr.put_nat(len, x)), Wr.put_list(~R.Tried, ~RetryFfi.spell_tried, tried, Wr.put_nat(switches, Wr.put_nat(base, Wr.put_nat(max, rest)))), Wr.put_list(~R.Tried, ~Fr.put_tried, tried, Wr.put_nat(switches, Wr.put_nat(base, Wr.put_nat(max, rest)))), rf.put_list(tried, Wr.put_nat(switches, Wr.put_nat(base, Wr.put_nat(max, rest)))))
    case Fr.QStall{idle}:
      {==}

def rf.delay(d: R.Delay) -> {Fr.put_delay(d, "") == RetryFfi.spell_delay(d) : String}:
  match d:
    case R.After{ms}:
      {==}
    case R.Refused{server, cap}:
      {==}

def rf.switch(m: Maybe<&2, R.Switch>) -> {Fr.put_switch(m, "") == RetryFfi.spell_switch(m) : String}:
  match m:
    case None{}:
      {==}
    case Some{sw}:
      match sw:
        case R.Switch{to, delay}:
          {==}

# Replies: a decision is no error form
# -----------------------------------

def rf.bool_ok(b: Bool) -> {LawsBase.wire_opens_err(Wr.put_bool(b, "")) == False{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def rf.delay_ok(d: R.Delay) -> {LawsBase.wire_opens_err(Fr.put_delay(d, "")) == False{} : Bool}:
  match d:
    case R.After{ms}:
      Wire.wire_nat_not_err(0n, Wr.put_nat(ms, ""))
    case R.Refused{server, cap}:
      Wire.wire_nat_not_err(1n, Wr.put_nat(server, Wr.put_nat(cap, "")))

def rf.switch_ok(m: Maybe<&2, R.Switch>) -> {LawsBase.wire_opens_err(Fr.put_switch(m, "")) == False{} : Bool}:
  match m:
    case None{}:
      Wire.wire_nat_not_err(0n, "")
    case Some{sw}:
      match sw:
        case R.Switch{to, delay}:
          Wire.wire_nat_not_err(1n, Wr.put_nat(to, Wr.put_nat(delay, "")))

def rf.answer_ok(q: Fr.Req) -> {LawsBase.wire_opens_err(Fr.answer(q)) == False{} : Bool}:
  match q:
    case Fr.QClassify{f}:
      rf.bool_ok(R.retryable(f))
    case Fr.QWait{base, attempt, cap, draw, server}:
      rf.delay_ok(R.retry_wait(base, attempt, cap, draw, server))
    case Fr.QFailover{len, tried, p}:
      rf.switch_ok(R.next(len, tried, p))
    case Fr.QStall{idle}:
      Wire.wire_nat_not_err(R.stall.next(idle), "")

# a decision answered as an error form proves anything
def rf.answer_err(-G: Type, +q: Fr.Req, -t: String, e: {Fr.answer(q) == Wr.err(t) : String}) -> G:
  LStg.stg.absurdF(G, Equal.trans(Bool, False{}, LawsBase.wire_opens_err(Fr.answer(q)), True{}, Equal.sym(Bool, LawsBase.wire_opens_err(Fr.answer(q)), False{}, rf.answer_ok(q)), Equal.cong(String, Bool, z => LawsBase.wire_opens_err(z), Fr.answer(q), Wr.err(t), e)))

# Fits: every number and count the request decoder reads fits the wire
# --------------------------------------------------------------------

# both sides of an and hold, so it does
def rf.and2(-a: Bool, -b: Bool, ha: {a == True{} : Bool}, hb: {b == True{} : Bool}) -> {Bool.and(a, b) == True{} : Bool}:
  %Equal.sym(Bool, a, True{}, ha) : {Bool.and(_, b) == True{} : Bool}
  hb

# Nat

def rf.FN(d: Wr.Dec<Nat>) -> Type:
  match d:
    case Wr.Got{n, r}:
      {LawsBase.wire_fits(n) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def rf.fn_go(+s: String, d: Wr.Dec<Nat>, +ed: {Wr.get_nat(s) == d : Wr.Dec<Nat>}) -> rf.FN(d):
  match d:
    case Wr.Got{+n, +r}:
      Wire.wire_nat_decoded_fits(s, n, r, ed)
    case Wr.Bad{}:
      Unit{}

def rf.fn(+s: String) -> rf.FN(Wr.get_nat(s)):
  rf.fn_go(s, Wr.get_nat(s), {==})

# Maybe<Nat>

def rf.FM(d: Wr.Dec<Maybe<&2, Nat>>) -> Type:
  match d:
    case Wr.Got{m, r}:
      {Retry.rs.mfits(m) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def rf.fm_some(d: Wr.Dec<Nat>, fn: rf.FN(d)) -> rf.FM(Fr.get_mnat.some(d)):
  match d:
    case Wr.Got{n, r}:
      fn
    case Wr.Bad{}:
      Unit{}

def rf.fm_tag(d: Wr.Dec<Nat>) -> rf.FM(Fr.get_mnat.tag(d)):
  match d:
    case Wr.Got{t, +s}:
      match t:
        case 0n:
          {==}
        case 1n:
          rf.fm_some(Wr.get_nat(s), rf.fn(s))
        case 2n+k:
          Unit{}
    case Wr.Bad{}:
      Unit{}

def rf.fm(+s: String) -> rf.FM(Fr.get_mnat(s)):
  rf.fm_tag(Wr.get_nat(s))

# Tried

def rf.FT(d: Wr.Dec<R.Tried>) -> Type:
  match d:
    case Wr.Got{t, r}:
      match t:
        case R.Tried{+at, w}:
          {Bool.and(LawsBase.wire_fits(at), Retry.rs.mfits(w)) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def rf.ft_wait(-at: Nat, fa: {LawsBase.wire_fits(at) == True{} : Bool}, d: Wr.Dec<Maybe<&2, Nat>>, fw: rf.FM(d)) -> rf.FT(Fr.get_tried.wait(at, d)):
  match d:
    case Wr.Got{+w, r}:
      rf.and2(LawsBase.wire_fits(at), Retry.rs.mfits(w), fa, fw)
    case Wr.Bad{}:
      Unit{}

def rf.ft_at(d: Wr.Dec<Nat>, fa: rf.FN(d)) -> rf.FT(Fr.get_tried.at(d)):
  match d:
    case Wr.Got{+at, +s}:
      rf.ft_wait(at, fa, Fr.get_mnat(s), rf.fm(s))
    case Wr.Bad{}:
      Unit{}

def rf.ft(+s: String) -> rf.FT(Fr.get_tried(s)):
  rf.ft_at(Wr.get_nat(s), rf.fn(s))

# List<Tried>

# the item loop's answer (m + 1 items): the attempts fit and there are m + 1
def rf.FLL(m: Nat, d: Wr.Dec<List<&2, R.Tried>>) -> Type:
  match d:
    case Wr.Got{+xs, r}:
      {Retry.rs.tried_fit(xs) == True{} : Bool} & {List.length(&2, R.Tried, xs) == 1n+m : Nat}
    case Wr.Bad{}:
      Unit

def rf.fl_step(x: R.Tried, -s3: String, -k: Nat, d: Wr.Dec<List<&2, R.Tried>>, ih: rf.FLL(k, d), fx: rf.FT(Wr.Got{x, s3})) -> rf.FLL(1n+k, Wr.get_list.cons(R.Tried, x, d)):
  match x:
    case R.Tried{+at, +w}:
      match d:
        case Wr.Got{+ys, r}:
          (e1, e2) = ih
          (rf.and2(Bool.and(LawsBase.wire_fits(at), Retry.rs.mfits(w)), Retry.rs.tried_fit(ys), fx, e1), Equal.cong(Nat, Nat, k2 => 1n+k2, List.length(&2, R.Tried, ys), 1n+k, e2))
        case Wr.Bad{}:
          Unit{}

def rf.fl_loop(m: Nat, cur: Wr.Dec<R.Tried>, fc: rf.FT(cur)) -> rf.FLL(m, Wr.get_list.go(~R.Tried, ~Fr.get_tried, m, cur)):
  match m cur:
    case 0n Wr.Got{x, s3}:
      match x:
        case R.Tried{+at, +w}:
          (rf.and2(Bool.and(LawsBase.wire_fits(at), Retry.rs.mfits(w)), True{}, fc, {==}), {==})
    case 0n Wr.Bad{}:
      Unit{}
    case 1n++k Wr.Got{+x, +s3}:
      rf.fl_step(x, s3, k, Wr.get_list.go(~R.Tried, ~Fr.get_tried, k, Fr.get_tried(s3)), rf.fl_loop(k, Fr.get_tried(s3), rf.ft(s3)), fc)
    case 1n++k Wr.Bad{}:
      Unit{}

def rf.FLS(d: Wr.Dec<List<&2, R.Tried>>) -> Type:
  match d:
    case Wr.Got{+xs, r}:
      {Bool.and(LawsBase.wire_fits(List.length(&2, R.Tried, xs)), Retry.rs.tried_fit(xs)) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def rf.fl_conv(-m: Nat, fn: {LawsBase.wire_fits(1n+m) == True{} : Bool}, d: Wr.Dec<List<&2, R.Tried>>, fl: rf.FLL(m, d)) -> rf.FLS(d):
  match d:
    case Wr.Got{+xs, r}:
      (e1, e2) = fl
      rf.and2(LawsBase.wire_fits(List.length(&2, R.Tried, xs)), Retry.rs.tried_fit(xs), Equal.trans(Bool, LawsBase.wire_fits(List.length(&2, R.Tried, xs)), LawsBase.wire_fits(1n+m), True{}, Equal.cong(Nat, Bool, k => LawsBase.wire_fits(k), List.length(&2, R.Tried, xs), 1n+m, e2), fn), e1)
    case Wr.Bad{}:
      Unit{}

def rf.fl_nat(n: Nat, +s2: String, fn: {LawsBase.wire_fits(n) == True{} : Bool}) -> rf.FLS(Wr.get_list.start(~R.Tried, ~Fr.get_tried, Wr.Got{n, s2})):
  match n:
    case 0n:
      {==}
    case 1n++m:
      rf.fl_conv(m, fn, Wr.get_list.go(~R.Tried, ~Fr.get_tried, m, Fr.get_tried(s2)), rf.fl_loop(m, Fr.get_tried(s2), rf.ft(s2)))

def rf.fl_top(d: Wr.Dec<Nat>, fn: rf.FN(d)) -> rf.FLS(Wr.get_list.start(~R.Tried, ~Fr.get_tried, d)):
  match d:
    case Wr.Got{+n, +s2}:
      rf.fl_nat(n, s2, fn)
    case Wr.Bad{}:
      Unit{}

def rf.fls(+s: String) -> rf.FLS(Wr.get_list(~R.Tried, ~Fr.get_tried, s)):
  rf.fl_top(Wr.get_nat(s), rf.fn(s))

# Policy

def rf.FP(d: Wr.Dec<R.Policy>) -> Type:
  match d:
    case Wr.Got{p, r}:
      match p:
        case R.Policy{+sw, +b, +m}:
          {Bool.and(LawsBase.wire_fits(sw), Bool.and(LawsBase.wire_fits(b), LawsBase.wire_fits(m))) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def rf.fp_max(-sw: Nat, -b: Nat, fsw: {LawsBase.wire_fits(sw) == True{} : Bool}, fb: {LawsBase.wire_fits(b) == True{} : Bool}, d: Wr.Dec<Nat>, fm: rf.FN(d)) -> rf.FP(Fr.get_policy.max(sw, b, d)):
  match d:
    case Wr.Got{+m, r}:
      rf.and2(LawsBase.wire_fits(sw), Bool.and(LawsBase.wire_fits(b), LawsBase.wire_fits(m)), fsw, rf.and2(LawsBase.wire_fits(b), LawsBase.wire_fits(m), fb, fm))
    case Wr.Bad{}:
      Unit{}

def rf.fp_base(-sw: Nat, fsw: {LawsBase.wire_fits(sw) == True{} : Bool}, d: Wr.Dec<Nat>, fb: rf.FN(d)) -> rf.FP(Fr.get_policy.base(sw, d)):
  match d:
    case Wr.Got{+b, +s}:
      rf.fp_max(sw, b, fsw, fb, Wr.get_nat(s), rf.fn(s))
    case Wr.Bad{}:
      Unit{}

def rf.fp_sw(d: Wr.Dec<Nat>, fsw: rf.FN(d)) -> rf.FP(Fr.get_policy.switches(d)):
  match d:
    case Wr.Got{+sw, +s}:
      rf.fp_base(sw, fsw, Wr.get_nat(s), rf.fn(s))
    case Wr.Bad{}:
      Unit{}

def rf.fp(+s: String) -> rf.FP(Fr.get_policy(s)):
  rf.fp_sw(Wr.get_nat(s), rf.fn(s))

# Facts (only the status is a number)

def rf.FF(d: Wr.Dec<R.Facts>) -> Type:
  match d:
    case Wr.Got{f, r}:
      match f:
        case R.Facts{p, l, st, k, t}:
          {Retry.rs.mfits(st) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def rf.ff_text(-p: Bool, -l: Bool, -st: Maybe<&2, Nat>, -k: Maybe<&2, R.Cause>, fst: {Retry.rs.mfits(st) == True{} : Bool}, d: Wr.Dec<Bool>) -> rf.FF(Fr.get_facts.text(p, l, st, k, d)):
  match d:
    case Wr.Got{t, r}:
      fst
    case Wr.Bad{}:
      Unit{}

def rf.ff_kind(-p: Bool, -l: Bool, -st: Maybe<&2, Nat>, fst: {Retry.rs.mfits(st) == True{} : Bool}, d: Wr.Dec<Maybe<&2, R.Cause>>) -> rf.FF(Fr.get_facts.kind(p, l, st, d)):
  match d:
    case Wr.Got{k, +s}:
      rf.ff_text(p, l, st, k, fst, Wr.get_bool(s))
    case Wr.Bad{}:
      Unit{}

def rf.ff_status(-p: Bool, -l: Bool, d: Wr.Dec<Maybe<&2, Nat>>, fm: rf.FM(d)) -> rf.FF(Fr.get_facts.status(p, l, d)):
  match d:
    case Wr.Got{st, +s}:
      rf.ff_kind(p, l, st, fm, Fr.get_mcause(s))
    case Wr.Bad{}:
      Unit{}

def rf.ff_limit(-p: Bool, d: Wr.Dec<Bool>) -> rf.FF(Fr.get_facts.limit(p, d)):
  match d:
    case Wr.Got{l, +s}:
      rf.ff_status(p, l, Fr.get_mnat(s), rf.fm(s))
    case Wr.Bad{}:
      Unit{}

def rf.ff_parked(d: Wr.Dec<Bool>) -> rf.FF(Fr.get_facts.parked(d)):
  match d:
    case Wr.Got{p, +s}:
      rf.ff_limit(p, Wr.get_bool(s))
    case Wr.Bad{}:
      Unit{}

def rf.ff(+s: String) -> rf.FF(Fr.get_facts(s)):
  rf.ff_parked(Wr.get_bool(s))

# Req

def rf.FR(d: Wr.Dec<Fr.Req>) -> Type:
  match d:
    case Wr.Got{q, r}:
      {Retry.rs.req_fits(q) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def rf.fr_classify(d: Wr.Dec<R.Facts>, ff: rf.FF(d)) -> rf.FR(Fr.get_classify(d)):
  match d:
    case Wr.Got{f, r}:
      match f:
        case R.Facts{p, l, st, k, t}:
          ff
    case Wr.Bad{}:
      Unit{}

def rf.fr_w_server(-b: Nat, -a: Nat, -c: Nat, -dr: Nat, fb: {LawsBase.wire_fits(b) == True{} : Bool}, fa: {LawsBase.wire_fits(a) == True{} : Bool}, fc: {LawsBase.wire_fits(c) == True{} : Bool}, fd: {LawsBase.wire_fits(dr) == True{} : Bool}, d: Wr.Dec<Maybe<&2, Nat>>, fs: rf.FM(d)) -> rf.FR(Fr.get_wait.server(b, a, c, dr, d)):
  match d:
    case Wr.Got{+sv, r}:
      rf.and2(Bool.and(LawsBase.wire_fits(b), LawsBase.wire_fits(a)), Bool.and(Bool.and(LawsBase.wire_fits(c), LawsBase.wire_fits(dr)), Retry.rs.mfits(sv)), rf.and2(LawsBase.wire_fits(b), LawsBase.wire_fits(a), fb, fa), rf.and2(Bool.and(LawsBase.wire_fits(c), LawsBase.wire_fits(dr)), Retry.rs.mfits(sv), rf.and2(LawsBase.wire_fits(c), LawsBase.wire_fits(dr), fc, fd), fs))
    case Wr.Bad{}:
      Unit{}

def rf.fr_w_draw(-b: Nat, -a: Nat, -c: Nat, fb: {LawsBase.wire_fits(b) == True{} : Bool}, fa: {LawsBase.wire_fits(a) == True{} : Bool}, fc: {LawsBase.wire_fits(c) == True{} : Bool}, d: Wr.Dec<Nat>, fd: rf.FN(d)) -> rf.FR(Fr.get_wait.draw(b, a, c, d)):
  match d:
    case Wr.Got{+dr, +s}:
      rf.fr_w_server(b, a, c, dr, fb, fa, fc, fd, Fr.get_mnat(s), rf.fm(s))
    case Wr.Bad{}:
      Unit{}

def rf.fr_w_cap(-b: Nat, -a: Nat, fb: {LawsBase.wire_fits(b) == True{} : Bool}, fa: {LawsBase.wire_fits(a) == True{} : Bool}, d: Wr.Dec<Nat>, fc: rf.FN(d)) -> rf.FR(Fr.get_wait.cap(b, a, d)):
  match d:
    case Wr.Got{+c, +s}:
      rf.fr_w_draw(b, a, c, fb, fa, fc, Wr.get_nat(s), rf.fn(s))
    case Wr.Bad{}:
      Unit{}

def rf.fr_w_attempt(-b: Nat, fb: {LawsBase.wire_fits(b) == True{} : Bool}, d: Wr.Dec<Nat>, fa: rf.FN(d)) -> rf.FR(Fr.get_wait.attempt(b, d)):
  match d:
    case Wr.Got{+a, +s}:
      rf.fr_w_cap(b, a, fb, fa, Wr.get_nat(s), rf.fn(s))
    case Wr.Bad{}:
      Unit{}

def rf.fr_wait(d: Wr.Dec<Nat>, fb: rf.FN(d)) -> rf.FR(Fr.get_wait(d)):
  match d:
    case Wr.Got{+b, +s}:
      rf.fr_w_attempt(b, fb, Wr.get_nat(s), rf.fn(s))
    case Wr.Bad{}:
      Unit{}

def rf.fr_f_policy(-len: Nat, -ts: List<&2, R.Tried>, flen: {LawsBase.wire_fits(len) == True{} : Bool}, fts: {Bool.and(LawsBase.wire_fits(List.length(&2, R.Tried, ts)), Retry.rs.tried_fit(ts)) == True{} : Bool}, d: Wr.Dec<R.Policy>, fp: rf.FP(d)) -> rf.FR(Fr.get_failover.policy(len, ts, d)):
  match d:
    case Wr.Got{p, r}:
      match p:
        case R.Policy{+sw, +b, +m}:
          rf.and2(Bool.and(LawsBase.wire_fits(len), Bool.and(LawsBase.wire_fits(List.length(&2, R.Tried, ts)), Retry.rs.tried_fit(ts))), Bool.and(LawsBase.wire_fits(sw), Bool.and(LawsBase.wire_fits(b), LawsBase.wire_fits(m))), rf.and2(LawsBase.wire_fits(len), Bool.and(LawsBase.wire_fits(List.length(&2, R.Tried, ts)), Retry.rs.tried_fit(ts)), flen, fts), fp)
    case Wr.Bad{}:
      Unit{}

def rf.fr_f_tried(-len: Nat, flen: {LawsBase.wire_fits(len) == True{} : Bool}, d: Wr.Dec<List<&2, R.Tried>>, fl: rf.FLS(d)) -> rf.FR(Fr.get_failover.tried(len, d)):
  match d:
    case Wr.Got{+ts, +s}:
      rf.fr_f_policy(len, ts, flen, fl, Fr.get_policy(s), rf.fp(s))
    case Wr.Bad{}:
      Unit{}

def rf.fr_failover(d: Wr.Dec<Nat>, fl: rf.FN(d)) -> rf.FR(Fr.get_failover(d)):
  match d:
    case Wr.Got{+len, +s}:
      rf.fr_f_tried(len, fl, Wr.get_list(~R.Tried, ~Fr.get_tried, s), rf.fls(s))
    case Wr.Bad{}:
      Unit{}

def rf.fr_stall(d: Wr.Dec<Nat>, fi: rf.FN(d)) -> rf.FR(Fr.get_stall(d)):
  match d:
    case Wr.Got{i, r}:
      fi
    case Wr.Bad{}:
      Unit{}

def rf.fr_tag(t: Nat, +s: String) -> rf.FR(Fr.get_req.tag(t, s)):
  match t:
    case 0n:
      rf.fr_classify(Fr.get_facts(s), rf.ff(s))
    case 1n:
      rf.fr_wait(Wr.get_nat(s), rf.fn(s))
    case 2n:
      rf.fr_failover(Wr.get_nat(s), rf.fn(s))
    case 3n:
      rf.fr_stall(Wr.get_nat(s), rf.fn(s))
    case 4n+u:
      Unit{}

def rf.fr_start(d: Wr.Dec<Nat>) -> rf.FR(Fr.get_req.start(d)):
  match d:
    case Wr.Got{t, +s}:
      rf.fr_tag(t, s)
    case Wr.Bad{}:
      Unit{}

# every request the decoder reads fits the wire
def rf.fr(+s: String) -> rf.FR(Fr.get_req(s)):
  rf.fr_start(Wr.get_nat(s))

# the laws' Facts reader against the entry's, stage by stage: the entry
# reads Facts and wraps them in QClassify
def rf.f_text(parked: Bool, limit: Bool, status: Maybe<&2, Nat>, kind: Maybe<&2, R.Cause>, r: Wr.Dec<Bool>) -> {RetryFfi.read_facts.text(parked, limit, status, kind, r) == Fr.get_classify(Fr.get_facts.text(parked, limit, status, kind, r)) : Wr.Dec<Fr.Req>}:
  match r:
    case Wr.Got{text, s}:
      {==}
    case Wr.Bad{}:
      {==}

def rf.f_kind(parked: Bool, limit: Bool, status: Maybe<&2, Nat>, r: Wr.Dec<Maybe<&2, R.Cause>>) -> {RetryFfi.read_facts.kind(parked, limit, status, r) == Fr.get_classify(Fr.get_facts.kind(parked, limit, status, r)) : Wr.Dec<Fr.Req>}:
  match r:
    case Wr.Got{kind, s}:
      rf.f_text(parked, limit, status, kind, Wr.get_bool(s))
    case Wr.Bad{}:
      {==}

def rf.cause_of(t: Nat) -> {RetryFfi.cause_of(t) == Fr.cause.of(t) : Maybe<&2, R.Cause>}:
  match t:
    case 0n:
      {==}
    case 1n:
      {==}
    case 2n:
      {==}
    case 3n:
      {==}
    case 4n:
      {==}
    case 5n:
      {==}
    case 6n:
      {==}
    case 7n:
      {==}
    case 8n:
      {==}
    case 9n:
      {==}
    case 10n:
      {==}
    case 11n:
      {==}
    case 12n:
      {==}
    case 13n:
      {==}
    case 14n+u:
      {==}

def rf.known(m: Maybe<&2, R.Cause>, s: String) -> {RetryFfi.read_mcause.known(m, s) == Fr.get_mcause.known(m, s) : Wr.Dec<Maybe<&2, R.Cause>>}:
  match m:
    case Some{k}:
      {==}
    case None{}:
      {==}

def rf.mc_some(r: Wr.Dec<Nat>) -> {RetryFfi.read_mcause.some(r) == Fr.get_mcause.some(r) : Wr.Dec<Maybe<&2, R.Cause>>}:
  match r:
    case Wr.Got{+t, +s}:
      %Equal.sym(Maybe<&2, R.Cause>, RetryFfi.cause_of(t), Fr.cause.of(t), rf.cause_of(t)) : {RetryFfi.read_mcause.known(_, s) == Fr.get_mcause.known(Fr.cause.of(t), s) : Wr.Dec<Maybe<&2, R.Cause>>}
      rf.known(Fr.cause.of(t), s)
    case Wr.Bad{}:
      {==}

def rf.mc_tag(r: Wr.Dec<Nat>) -> {RetryFfi.read_mcause.tag(r) == Fr.get_mcause.tag(r) : Wr.Dec<Maybe<&2, R.Cause>>}:
  match r:
    case Wr.Got{t, s}:
      match t:
        case 0n:
          {==}
        case 1n:
          rf.mc_some(Wr.get_nat(s))
        case 2n+k:
          {==}
    case Wr.Bad{}:
      {==}

def rf.rd_mcause(s: String) -> {RetryFfi.read_mcause(s) == Fr.get_mcause(s) : Wr.Dec<Maybe<&2, R.Cause>>}:
  rf.mc_tag(Wr.get_nat(s))

def rf.f_status(parked: Bool, limit: Bool, r: Wr.Dec<Maybe<&2, Nat>>) -> {RetryFfi.read_facts.status(parked, limit, r) == Fr.get_classify(Fr.get_facts.status(parked, limit, r)) : Wr.Dec<Fr.Req>}:
  match r:
    case Wr.Got{status, +s}:
      %Equal.sym(Wr.Dec<Maybe<&2, R.Cause>>, RetryFfi.read_mcause(s), Fr.get_mcause(s), rf.rd_mcause(s)) : {RetryFfi.read_facts.kind(parked, limit, status, _) == Fr.get_classify(Fr.get_facts.kind(parked, limit, status, Fr.get_mcause(s))) : Wr.Dec<Fr.Req>}
      rf.f_kind(parked, limit, status, Fr.get_mcause(s))
    case Wr.Bad{}:
      {==}

def rf.mn_some(r: Wr.Dec<Nat>) -> {RetryFfi.read_mnat.some(r) == Fr.get_mnat.some(r) : Wr.Dec<Maybe<&2, Nat>>}:
  match r:
    case Wr.Got{n, u}:
      {==}
    case Wr.Bad{}:
      {==}

def rf.rd_mnat_tag(r: Wr.Dec<Nat>) -> {RetryFfi.read_mnat.tag(r) == Fr.get_mnat.tag(r) : Wr.Dec<Maybe<&2, Nat>>}:
  match r:
    case Wr.Got{t, s}:
      match t:
        case 0n:
          {==}
        case 1n:
          rf.mn_some(Wr.get_nat(s))
        case 2n+k:
          {==}
    case Wr.Bad{}:
      {==}

def rf.rd_mnat(s: String) -> {RetryFfi.read_mnat(s) == Fr.get_mnat(s) : Wr.Dec<Maybe<&2, Nat>>}:
  rf.rd_mnat_tag(Wr.get_nat(s))

def rf.f_limit(parked: Bool, r: Wr.Dec<Bool>) -> {RetryFfi.read_facts.limit(parked, r) == Fr.get_classify(Fr.get_facts.limit(parked, r)) : Wr.Dec<Fr.Req>}:
  match r:
    case Wr.Got{limit, +s}:
      %Equal.sym(Wr.Dec<Maybe<&2, Nat>>, RetryFfi.read_mnat(s), Fr.get_mnat(s), rf.rd_mnat(s)) : {RetryFfi.read_facts.status(parked, limit, _) == Fr.get_classify(Fr.get_facts.status(parked, limit, Fr.get_mnat(s))) : Wr.Dec<Fr.Req>}
      rf.f_status(parked, limit, Fr.get_mnat(s))
    case Wr.Bad{}:
      {==}

def rf.facts(r: Wr.Dec<Bool>) -> {RetryFfi.read_facts(r) == Fr.get_classify(Fr.get_facts.parked(r)) : Wr.Dec<Fr.Req>}:
  match r:
    case Wr.Got{parked, s}:
      rf.f_limit(parked, Wr.get_bool(s))
    case Wr.Bad{}:
      {==}

def rf.fo_max(len: Nat, tried: List<&2, R.Tried>, switches: Nat, base: Nat, r: Wr.Dec<Nat>) -> {RetryFfi.read_failover.max(len, tried, switches, base, r) == Fr.get_failover.policy(len, tried, Fr.get_policy.max(switches, base, r)) : Wr.Dec<Fr.Req>}:
  match r:
    case Wr.Got{max, s}:
      {==}
    case Wr.Bad{}:
      {==}

def rf.fo_base(len: Nat, tried: List<&2, R.Tried>, switches: Nat, r: Wr.Dec<Nat>) -> {RetryFfi.read_failover.base(len, tried, switches, r) == Fr.get_failover.policy(len, tried, Fr.get_policy.base(switches, r)) : Wr.Dec<Fr.Req>}:
  match r:
    case Wr.Got{base, s}:
      rf.fo_max(len, tried, switches, base, Wr.get_nat(s))
    case Wr.Bad{}:
      {==}

def rf.fo_switches(len: Nat, tried: List<&2, R.Tried>, r: Wr.Dec<Nat>) -> {RetryFfi.read_failover.switches(len, tried, r) == Fr.get_failover.policy(len, tried, Fr.get_policy.switches(r)) : Wr.Dec<Fr.Req>}:
  match r:
    case Wr.Got{switches, s}:
      rf.fo_base(len, tried, switches, Wr.get_nat(s))
    case Wr.Bad{}:
      {==}

def rf.fo_tried(len: Nat, r: Wr.Dec<List<&2, R.Tried>>) -> {RetryFfi.read_failover.tried(len, r) == Fr.get_failover.tried(len, r) : Wr.Dec<Fr.Req>}:
  match r:
    case Wr.Got{tried, s}:
      rf.fo_switches(len, tried, Wr.get_nat(s))
    case Wr.Bad{}:
      {==}

def rf.t_wait(at: Nat, r: Wr.Dec<Maybe<&2, Nat>>) -> {RetryFfi.read_tried.wait(at, r) == Fr.get_tried.wait(at, r) : Wr.Dec<R.Tried>}:
  match r:
    case Wr.Got{w, s}:
      {==}
    case Wr.Bad{}:
      {==}

def rf.t_at(r: Wr.Dec<Nat>) -> {RetryFfi.read_tried.at(r) == Fr.get_tried.at(r) : Wr.Dec<R.Tried>}:
  match r:
    case Wr.Got{at, +s}:
      %Equal.sym(Wr.Dec<Maybe<&2, Nat>>, RetryFfi.read_mnat(s), Fr.get_mnat(s), rf.rd_mnat(s)) : {RetryFfi.read_tried.wait(at, _) == Fr.get_tried.wait(at, Fr.get_mnat(s)) : Wr.Dec<R.Tried>}
      rf.t_wait(at, Fr.get_mnat(s))
    case Wr.Bad{}:
      {==}

def rf.rd_tried(s: String) -> {RetryFfi.read_tried(s) == Fr.get_tried(s) : Wr.Dec<R.Tried>}:
  rf.t_at(Wr.get_nat(s))

def rf.list_go(n: Nat, cur: Wr.Dec<R.Tried>) -> {Wr.get_list.go(~R.Tried, ~RetryFfi.read_tried, n, cur) == Wr.get_list.go(~R.Tried, ~Fr.get_tried, n, cur) : Wr.Dec<List<&2, R.Tried>>}:
  match n:
    case 0n:
      match cur:
        case Wr.Got{x, s}:
          {==}
        case Wr.Bad{}:
          {==}
    case 1n+m:
      match cur:
        case Wr.Got{x, +s}:
          %Equal.sym(Wr.Dec<R.Tried>, RetryFfi.read_tried(s), Fr.get_tried(s), rf.rd_tried(s)) : {Wr.get_list.cons(R.Tried, x, Wr.get_list.go(~R.Tried, ~RetryFfi.read_tried, m, _)) == Wr.get_list.cons(R.Tried, x, Wr.get_list.go(~R.Tried, ~Fr.get_tried, m, Fr.get_tried(s))) : Wr.Dec<List<&2, R.Tried>>}
          Equal.cong(Wr.Dec<List<&2, R.Tried>>, Wr.Dec<List<&2, R.Tried>>, y => Wr.get_list.cons(R.Tried, x, y), Wr.get_list.go(~R.Tried, ~RetryFfi.read_tried, m, Fr.get_tried(s)), Wr.get_list.go(~R.Tried, ~Fr.get_tried, m, Fr.get_tried(s)), rf.list_go(m, Fr.get_tried(s)))
        case Wr.Bad{}:
          {==}

def rf.list_start(r: Wr.Dec<Nat>) -> {Wr.get_list.start(~R.Tried, ~RetryFfi.read_tried, r) == Wr.get_list.start(~R.Tried, ~Fr.get_tried, r) : Wr.Dec<List<&2, R.Tried>>}:
  match r:
    case Wr.Got{n, +s}:
      match n:
        case 0n:
          {==}
        case 1n+m:
          %Equal.sym(Wr.Dec<R.Tried>, RetryFfi.read_tried(s), Fr.get_tried(s), rf.rd_tried(s)) : {Wr.get_list.go(~R.Tried, ~RetryFfi.read_tried, m, _) == Wr.get_list.go(~R.Tried, ~Fr.get_tried, m, Fr.get_tried(s)) : Wr.Dec<List<&2, R.Tried>>}
          rf.list_go(m, Fr.get_tried(s))
    case Wr.Bad{}:
      {==}

def rf.failover(r: Wr.Dec<Nat>) -> {RetryFfi.read_failover(r) == Fr.get_failover(r) : Wr.Dec<Fr.Req>}:
  match r:
    case Wr.Got{len, +s}:
      %Equal.sym(Wr.Dec<List<&2, R.Tried>>, Wr.get_list.start(~R.Tried, ~RetryFfi.read_tried, Wr.get_nat(s)), Wr.get_list.start(~R.Tried, ~Fr.get_tried, Wr.get_nat(s)), rf.list_start(Wr.get_nat(s))) : {RetryFfi.read_failover.tried(len, _) == Fr.get_failover.tried(len, Wr.get_list(~R.Tried, ~Fr.get_tried, s)) : Wr.Dec<Fr.Req>}
      rf.fo_tried(len, Wr.get_list(~R.Tried, ~Fr.get_tried, s))
    case Wr.Bad{}:
      {==}

def rf.stall(r: Wr.Dec<Nat>) -> {RetryFfi.read_stall(r) == Fr.get_stall(r) : Wr.Dec<Fr.Req>}:
  match r:
    case Wr.Got{idle, s}:
      {==}
    case Wr.Bad{}:
      {==}

def rf.w_server(base: Nat, attempt: Nat, cap: Nat, draw: Nat, r: Wr.Dec<Maybe<&2, Nat>>) -> {RetryFfi.read_wait.server(base, attempt, cap, draw, r) == Fr.get_wait.server(base, attempt, cap, draw, r) : Wr.Dec<Fr.Req>}:
  match r:
    case Wr.Got{server, s}:
      {==}
    case Wr.Bad{}:
      {==}

def rf.w_draw(base: Nat, attempt: Nat, cap: Nat, r: Wr.Dec<Nat>) -> {RetryFfi.read_wait.draw(base, attempt, cap, r) == Fr.get_wait.draw(base, attempt, cap, r) : Wr.Dec<Fr.Req>}:
  match r:
    case Wr.Got{draw, +s}:
      %Equal.sym(Wr.Dec<Maybe<&2, Nat>>, RetryFfi.read_mnat(s), Fr.get_mnat(s), rf.rd_mnat(s)) : {RetryFfi.read_wait.server(base, attempt, cap, draw, _) == Fr.get_wait.server(base, attempt, cap, draw, Fr.get_mnat(s)) : Wr.Dec<Fr.Req>}
      rf.w_server(base, attempt, cap, draw, Fr.get_mnat(s))
    case Wr.Bad{}:
      {==}

def rf.w_cap(base: Nat, attempt: Nat, r: Wr.Dec<Nat>) -> {RetryFfi.read_wait.cap(base, attempt, r) == Fr.get_wait.cap(base, attempt, r) : Wr.Dec<Fr.Req>}:
  match r:
    case Wr.Got{cap, s}:
      rf.w_draw(base, attempt, cap, Wr.get_nat(s))
    case Wr.Bad{}:
      {==}

def rf.w_attempt(base: Nat, r: Wr.Dec<Nat>) -> {RetryFfi.read_wait.attempt(base, r) == Fr.get_wait.attempt(base, r) : Wr.Dec<Fr.Req>}:
  match r:
    case Wr.Got{attempt, s}:
      rf.w_cap(base, attempt, Wr.get_nat(s))
    case Wr.Bad{}:
      {==}

def rf.wait(r: Wr.Dec<Nat>) -> {RetryFfi.read_wait(r) == Fr.get_wait(r) : Wr.Dec<Fr.Req>}:
  match r:
    case Wr.Got{base, s}:
      rf.w_attempt(base, Wr.get_nat(s))
    case Wr.Bad{}:
      {==}

def rf.tag(t: Nat, s: String) -> {RetryFfi.read_req.tag(t, s) == Fr.get_req.tag(t, s) : Wr.Dec<Fr.Req>}:
  match t:
    case 0n:
      rf.facts(Wr.get_bool(s))
    case 1n:
      rf.wait(Wr.get_nat(s))
    case 2n:
      rf.failover(Wr.get_nat(s))
    case 3n:
      rf.stall(Wr.get_nat(s))
    case 4n+u:
      {==}

# the laws read every input as the entry's decoder does
def rf.rq(r: Wr.Dec<Nat>) -> {RetryFfi.read_req.go(r) == Fr.get_req.start(r) : Wr.Dec<Fr.Req>}:
  match r:
    case Wr.Got{t, s}:
      rf.tag(t, s)
    case Wr.Bad{}:
      {==}
