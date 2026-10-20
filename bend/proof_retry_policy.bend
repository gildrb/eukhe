# proof_retry_policy: the laws of laws/retry.bend over the model in
# bend/retry.bend. Most decisions are a match on their inputs, so most
# laws follow by case analysis. A clash of two values is refuted with a
# motive that sends the expected value to the goal and the other to Unit.
#
# - retry_never_parked, retry_never_limit, retry_status_first: the park
#   and the limit are matched first; then each side computes to the same
#   value.
# - retry_never_client_error, retry_server_errors, retry_only_retryable:
#   a helper takes the result of `Nat.is_lt(s, 500n)` as a Bool with its
#   equation, and matches on it. Below 500, the status must be listed;
#   at 500 or more, the status is a server error.
# - retry_kind_before_text: a known kind has a class that is not Unsure,
#   so the text is not read.
# - retry_after_respected: the wait is `Nat.max(jitter, s)`, and
#   `Nat.max_ge_r` gives that it is at least s. A refused wait sends no
#   retry.
# - retry_refuses_past_cap: the two premises make the refusal test True.
# - The failover laws: each pick (`pick.fresh`, `pick.back`) is shown, by
#   induction on its order list, to give only a switch that satisfies its
#   own Bool condition (the equation of the condition goes into
#   `pick.sel`); its switch is never the last provider, since the order
#   holds no last (`rp.order_notin`: the order's first part is above
#   last, its second part below it). `next` then goes through `next.last`, `next.budget` and
#   `next.mode` with the equations of the last attempt, the budget and
#   the all-seen test. From these facts, `good` gets the five `Switch`
#   checks together; each failover law takes one of them.
# - deferred_pays_once, deferred_bounded_in_time: a step never sends
#   while the job is live, and never polls a live job with 0 ms left.
#   Induction over the replies, with any start tally, shows that the run
#   adds 0 to each count.
# - deferred_failed_poll_repolls: the two premises make the repoll test
#   True.
# - stall_retry_extends: idle < idle + idle when idle > 0.
# - stall_detection_bounded: induction over the events, with any start
#   time: a stall ends at the last event plus the deadline, a close at
#   the last event, which is at most it plus the deadline.
# - stall_silent_ends_at_deadline: by computation.

import Base
import ./retry.bend as R

# Clashes
# -------

def rp.BD(b: Bool, A: Type) -> Type:
  match b:
    case True{}:
      A
    case False{}:
      Unit

def rp.absurdF(-A: Type, e: {False{} == True{} : Bool}) -> A:
  %e : rp.BD(_, A)
  Unit{}

def rp.ND(b: Bool, A: Type) -> Type:
  match b:
    case True{}:
      Unit
    case False{}:
      A

def rp.absurdT(-A: Type, e: {True{} == False{} : Bool}) -> A:
  %e : rp.ND(_, A)
  Unit{}

# Bools
# -----

def rp.or_l(a: Bool, -b: Bool, ea: {a == True{} : Bool}) -> {Bool.or(a, b) == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      rp.absurdF({Bool.or(False{}, b) == True{} : Bool}, ea)

def rp.or_r(a: Bool, -b: Bool, eb: {b == True{} : Bool}) -> {Bool.or(a, b) == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      eb

def rp.or_ff(a: Bool, b: Bool, ea: {a == False{} : Bool}, eb: {b == False{} : Bool}) -> {Bool.or(a, b) == False{} : Bool}:
  match a:
    case True{}:
      rp.absurdT({Bool.or(True{}, b) == False{} : Bool}, ea)
    case False{}:
      eb

def rp.and_tt(a: Bool, -b: Bool, ea: {a == True{} : Bool}, eb: {b == True{} : Bool}) -> {Bool.and(a, b) == True{} : Bool}:
  match a:
    case True{}:
      eb
    case False{}:
      rp.absurdF({Bool.and(False{}, b) == True{} : Bool}, ea)

def rp.and_l(a: Bool, -b: Bool, e: {Bool.and(a, b) == True{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      rp.absurdF({False{} == True{} : Bool}, e)

def rp.and_r(a: Bool, -b: Bool, e: {Bool.and(a, b) == True{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case True{}:
      e
    case False{}:
      rp.absurdF({b == True{} : Bool}, e)

# Numbers
# -------

def rp.eq_refl(k: Nat) -> {True{} == Nat.is_eq(k, k) : Bool}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      rp.eq_refl(p)

def rp.eq_true(a: Nat, b: Nat, h: {Nat.is_eq(a, b) == True{} : Bool}) -> {a == b : Nat}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      rp.absurdF({0n == 1n+q : Nat}, h)
    case 1n+p 0n:
      rp.absurdF({1n+p == 0n : Nat}, h)
    case 1n+p 1n+q:
      Equal.cong(Nat, Nat, n => 1n+n, p, q, rp.eq_true(p, q, h))

def rp.cmp_ge(c: Cmp, e: {Cmp.is_lt(c) == False{} : Bool}) -> {Cmp.is_ge(c) == True{} : Bool}:
  match c:
    case LT{}:
      rp.absurdT({False{} == True{} : Bool}, e)
    case EQ{}:
      {==}
    case GT{}:
      {==}

def rp.ge_of_not_lt(+a: Nat, +b: Nat, e: {Nat.is_lt(a, b) == False{} : Bool}) -> {Nat.is_ge(a, b) == True{} : Bool}:
  rp.cmp_ge(Nat.cmp(a, b), e)

def rp.le_zero(n: Nat) -> {Nat.is_le(0n, n) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      {==}

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

def rp.lt_add_succ(k: Nat, +j: Nat) -> {Nat.is_lt(k, Nat.add(k, 1n+j)) == True{} : Bool}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      rp.lt_add_succ(p, j)

# (R1) The classifier
# -------------------

def never_parked(limit: Bool, status: Maybe<&2, Nat>, kind: Maybe<&2, R.Cause>, text: Bool) -> {R.retryable(R.Facts{True{}, limit, status, kind, text}) == False{} : Bool}:
  {==}

def never_limit(parked: Bool, status: Maybe<&2, Nat>, kind: Maybe<&2, R.Cause>, text: Bool) -> {R.retryable(R.Facts{parked, True{}, status, kind, text}) == False{} : Bool}:
  match parked:
    case True{}:
      {==}
    case False{}:
      {==}

def rp.client(lt: Bool, +s: Nat, below: {lt == True{} : Bool}, n408: {Nat.is_eq(s, 408n) == False{} : Bool}, n409: {Nat.is_eq(s, 409n) == False{} : Bool}, n429: {Nat.is_eq(s, 429n) == False{} : Bool}) -> {R.status.ok.go(lt, s) == False{} : Bool}:
  match lt:
    case True{}:
      rp.or_ff(Nat.is_eq(s, 408n), Bool.or(Nat.is_eq(s, 409n), Nat.is_eq(s, 429n)), n408, rp.or_ff(Nat.is_eq(s, 409n), Nat.is_eq(s, 429n), n409, n429))
    case False{}:
      rp.absurdF({R.status.ok.go(False{}, s) == False{} : Bool}, below)

def never_client_error(parked: Bool, limit: Bool, kind: Maybe<&2, R.Cause>, text: Bool, +s: Nat, below: {Nat.is_lt(s, 500n) == True{} : Bool}, n408: {Nat.is_eq(s, 408n) == False{} : Bool}, n409: {Nat.is_eq(s, 409n) == False{} : Bool}, n429: {Nat.is_eq(s, 429n) == False{} : Bool}) -> {R.retryable(R.Facts{parked, limit, Some{s}, kind, text}) == False{} : Bool}:
  match parked limit:
    case True{} l:
      {==}
    case False{} True{}:
      {==}
    case False{} False{}:
      rp.client(Nat.is_lt(s, 500n), s, below, n408, n409, n429)

def rp.only(lt: Bool, +s: Nat, elt: {Nat.is_lt(s, 500n) == lt : Bool}, r: {R.status.ok.go(lt, s) == True{} : Bool}) -> {Bool.or(Nat.is_ge(s, 500n), R.status.listed(s)) == True{} : Bool}:
  match lt:
    case True{}:
      rp.or_r(Nat.is_ge(s, 500n), R.status.listed(s), r)
    case False{}:
      rp.or_l(Nat.is_ge(s, 500n), R.status.listed(s), rp.ge_of_not_lt(s, 500n, elt))

def only_retryable(parked: Bool, limit: Bool, kind: Maybe<&2, R.Cause>, text: Bool, +s: Nat, retried: {R.retryable(R.Facts{parked, limit, Some{s}, kind, text}) == True{} : Bool}) -> {Bool.or(Nat.is_ge(s, 500n), R.status.listed(s)) == True{} : Bool}:
  match parked limit:
    case True{} l:
      rp.absurdF({Bool.or(Nat.is_ge(s, 500n), R.status.listed(s)) == True{} : Bool}, retried)
    case False{} True{}:
      rp.absurdF({Bool.or(Nat.is_ge(s, 500n), R.status.listed(s)) == True{} : Bool}, retried)
    case False{} False{}:
      rp.only(Nat.is_lt(s, 500n), s, {==}, retried)

def status_first(parked: Bool, limit: Bool, +s: Nat, k1: Maybe<&2, R.Cause>, t1: Bool, k2: Maybe<&2, R.Cause>, t2: Bool) -> {R.retryable(R.Facts{parked, limit, Some{s}, k1, t1}) == R.retryable(R.Facts{parked, limit, Some{s}, k2, t2}) : Bool}:
  match parked limit:
    case True{} l:
      {==}
    case False{} True{}:
      {==}
    case False{} False{}:
      {==}

def rp.known(k: R.Cause, known: {R.Cause.known(k) == True{} : Bool}, t1: Bool, t2: Bool) -> {R.by_class(R.Cause.class(k), t1) == R.by_class(R.Cause.class(k), t2) : Bool}:
  match k:
    case R.Unknown{}:
      rp.absurdF({t1 == t2 : Bool}, known)
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

def kind_before_text(parked: Bool, limit: Bool, k: R.Cause, known: {R.Cause.known(k) == True{} : Bool}, t1: Bool, t2: Bool) -> {R.retryable(R.Facts{parked, limit, None{}, Some{k}, t1}) == R.retryable(R.Facts{parked, limit, None{}, Some{k}, t2}) : Bool}:
  match parked limit:
    case True{} l:
      {==}
    case False{} True{}:
      {==}
    case False{} False{}:
      rp.known(k, known, t1, t2)

def rp.server(lt: Bool, +s: Nat, e: {lt == False{} : Bool}) -> {R.status.ok.go(lt, s) == True{} : Bool}:
  match lt:
    case True{}:
      rp.absurdT({R.status.ok.go(True{}, s) == True{} : Bool}, e)
    case False{}:
      {==}

def server_errors(kind: Maybe<&2, R.Cause>, text: Bool, +s: Nat, server: {Nat.is_lt(s, 500n) == False{} : Bool}) -> {R.retryable(R.Facts{False{}, False{}, Some{s}, kind, text}) == True{} : Bool}:
  rp.server(Nat.is_lt(s, 500n), s, server)

# (R2) The wait
# -------------

def rp.after(over: Bool, +jitter: Nat, +s: Nat, +cap: Nat) -> {R.Delay.respects(R.wait.server(over, jitter, s, cap), s) == True{} : Bool}:
  match over:
    case True{}:
      {==}
    case False{}:
      Nat.max_ge_r(jitter, s)

def after_respected(+jitter: Nat, +s: Nat, +cap: Nat) -> {R.Delay.respects(R.wait(jitter, Some{s}, cap), s) == True{} : Bool}:
  rp.after(Bool.and(Nat.is_gt(cap, 0n), Nat.is_gt(s, cap)), jitter, s, cap)

def rp.refuse(over: Bool, +jitter: Nat, +s: Nat, +cap: Nat, e: {over == True{} : Bool}) -> {R.wait.server(over, jitter, s, cap) == R.Refused{s, cap} : R.Delay}:
  match over:
    case True{}:
      {==}
    case False{}:
      rp.absurdF({R.wait.server(False{}, jitter, s, cap) == R.Refused{s, cap} : R.Delay}, e)

def refuses_past_cap(+jitter: Nat, +s: Nat, +cap: Nat, capped: {Nat.is_gt(cap, 0n) == True{} : Bool}, over: {Nat.is_gt(s, cap) == True{} : Bool}) -> {R.wait(jitter, Some{s}, cap) == R.Refused{s, cap} : R.Delay}:
  rp.refuse(Bool.and(Nat.is_gt(cap, 0n), Nat.is_gt(s, cap)), jitter, s, cap, rp.and_tt(Nat.is_gt(cap, 0n), Nat.is_gt(s, cap), capped, over))

# (R3) The failover walk
# ----------------------

# what pick.fresh guarantees of its switch: no wait, not the last
# provider, not tried
def rp.fresh_ok(m: Maybe<&2, R.Switch>, +last: Nat, +ts: List<&2, R.Tried>) -> Bool:
  match m:
    case None{}:
      True{}
    case Some{s}:
      match s:
        case R.Switch{+to, d}:
          Bool.and(Nat.is_eq(d, 0n), Bool.and(Bool.not(Nat.is_eq(to, last)), Bool.not(R.seen(to, ts))))

# Order
# -----

# last is no element of xs
def rp.notin(+last: Nat, xs: List<&2, Nat>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case x <> rest:
      Bool.and(Bool.not(Nat.is_eq(x, last)), rp.notin(last, rest))

def rp.not_of_false(b: Bool, e: {b == False{} : Bool}) -> {Bool.not(b) == True{} : Bool}:
  match b:
    case True{}:
      rp.absurdT({Bool.not(True{}) == True{} : Bool}, e)
    case False{}:
      {==}

def rp.ne_of_lt(+last: Nat, +a: Nat, h: {Nat.is_lt(last, a) == True{} : Bool}) -> {Nat.is_eq(a, last) == False{} : Bool}:
  match last a:
    case 0n 0n:
      rp.absurdF({Nat.is_eq(0n, 0n) == False{} : Bool}, h)
    case 0n 1n+p:
      {==}
    case 1n+q 0n:
      rp.absurdF({Nat.is_eq(0n, 1n+q) == False{} : Bool}, h)
    case 1n+q 1n+p:
      rp.ne_of_lt(q, p, h)

def rp.lt_succ(+last: Nat, +a: Nat, h: {Nat.is_lt(last, a) == True{} : Bool}) -> {Nat.is_lt(last, 1n+a) == True{} : Bool}:
  match last a:
    case 0n a:
      {==}
    case 1n+q 0n:
      rp.absurdF({Nat.is_lt(1n+q, 1n) == True{} : Bool}, h)
    case 1n+q 1n+p:
      rp.lt_succ(q, p, h)

def rp.lt_self(n: Nat) -> {Nat.is_lt(n, 1n+n) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      rp.lt_self(p)

# every element of upto(k, a) is at least a, so above last
def rp.notin_above(k: Nat, +a: Nat, +last: Nat, +h: {Nat.is_lt(last, a) == True{} : Bool}) -> {rp.notin(last, R.upto(k, a)) == True{} : Bool}:
  match k:
    case 0n:
      {==}
    case 1n+j:
      rp.and_tt(Bool.not(Nat.is_eq(a, last)), rp.notin(last, R.upto(j, 1n+a)), rp.not_of_false(Nat.is_eq(a, last), rp.ne_of_lt(last, a, h)), rp.notin_above(j, 1n+a, last, rp.lt_succ(last, a, h)))

# shifting the list and last by one keeps the answer
def rp.notin_shift(k: Nat, +a: Nat, +last: Nat) -> {rp.notin(1n+last, R.upto(k, 1n+a)) == rp.notin(last, R.upto(k, a)) : Bool}:
  match k:
    case 0n:
      {==}
    case 1n+j:
      %rp.notin_shift(j, 1n+a, last) : {Bool.and(Bool.not(Nat.is_eq(a, last)), rp.notin(1n+last, R.upto(j, 2n+a))) == Bool.and(Bool.not(Nat.is_eq(a, last)), _) : Bool}
      {==}

# every element of upto(k, 0) is below k, so below last when k <= last
def rp.notin_below(+k: Nat, +last: Nat, h: {Nat.is_le(k, last) == True{} : Bool}) -> {rp.notin(last, R.upto(k, 0n)) == True{} : Bool}:
  match k last:
    case 0n l:
      {==}
    case 1n+j 0n:
      rp.absurdF({rp.notin(0n, R.upto(1n+j, 0n)) == True{} : Bool}, h)
    case 1n+j 1n+q:
      %Equal.sym(Bool, rp.notin(1n+q, R.upto(j, 1n)), rp.notin(q, R.upto(j, 0n)), rp.notin_shift(j, 0n, q)) : {_ == True{} : Bool}
      rp.notin_below(j, q, h)

def rp.min_le(+a: Nat, +b: Nat) -> {Nat.is_le(Nat.min(a, b), a) == True{} : Bool}:
  match a b:
    case 0n b:
      {==}
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      rp.min_le(p, q)

def rp.notin_append(+last: Nat, xs: List<&2, Nat>, +ys: List<&2, Nat>, +hx: {rp.notin(last, xs) == True{} : Bool}, hy: {rp.notin(last, ys) == True{} : Bool}) -> {rp.notin(last, List.append(&2, Nat, xs, ys)) == True{} : Bool}:
  match xs:
    case Nil{}:
      hy
    case +x <> +rest:
      ne = rp.and_l(Bool.not(Nat.is_eq(x, last)), rp.notin(last, rest), hx)
      nr = rp.and_r(Bool.not(Nat.is_eq(x, last)), rp.notin(last, rest), hx)
      rp.and_tt(Bool.not(Nat.is_eq(x, last)), rp.notin(last, List.append(&2, Nat, rest, ys)), ne, rp.notin_append(last, rest, ys, nr, hy))

# the chain order after last never holds last
def rp.order_notin(+last: Nat, +len: Nat) -> {rp.notin(last, R.order(last, len)) == True{} : Bool}:
  rp.notin_append(last, R.upto(Nat.sub(len, 1n+last), 1n+last), R.upto(Nat.min(last, len), 0n), rp.notin_above(Nat.sub(len, 1n+last), 1n+last, last, rp.lt_self(last)), rp.notin_below(Nat.min(last, len), last, rp.min_le(last, len)))

# The picks
# ---------

def rp.fresh_sel(c: Bool, +x: Nat, +last: Nat, +ts: List<&2, R.Tried>, r: Maybe<&2, R.Switch>, ec: {Bool.not(R.seen(x, ts)) == c : Bool}, ne: {Bool.not(Nat.is_eq(x, last)) == True{} : Bool}, ih: {rp.fresh_ok(r, last, ts) == True{} : Bool}) -> {rp.fresh_ok(R.pick.sel(c, R.Switch{x, 0n}, r), last, ts) == True{} : Bool}:
  match c:
    case True{}:
      rp.and_tt(Bool.not(Nat.is_eq(x, last)), Bool.not(R.seen(x, ts)), ne, ec)
    case False{}:
      ih

def rp.fresh_inv(xs: List<&2, Nat>, +last: Nat, +ts: List<&2, R.Tried>, +nin: {rp.notin(last, xs) == True{} : Bool}) -> {rp.fresh_ok(R.pick.fresh(xs, ts), last, ts) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +rest:
      ne = rp.and_l(Bool.not(Nat.is_eq(x, last)), rp.notin(last, rest), nin)
      nr = rp.and_r(Bool.not(Nat.is_eq(x, last)), rp.notin(last, rest), nin)
      rp.fresh_sel(Bool.not(R.seen(x, ts)), x, last, ts, R.pick.fresh(rest, ts), {==}, ne, rp.fresh_inv(rest, last, ts, nr))

# what pick.back guarantees of its switch: the wait is the backoff, and
# never less than its server's wait; not the last provider; the wait is
# positive and at most max
def rp.back_ok(m: Maybe<&2, R.Switch>, +last: Nat, +ts: List<&2, R.Tried>, +backoff: Nat, +max: Nat) -> Bool:
  match m:
    case None{}:
      True{}
    case Some{s}:
      match s:
        case R.Switch{+to, +d}:
          Bool.and(Nat.is_eq(Nat.max(backoff, R.server(to, ts)), d), Bool.and(Bool.not(Nat.is_eq(to, last)), Bool.and(Nat.is_gt(d, 0n), Nat.is_le(d, max))))

def rp.back_sel(c: Bool, +x: Nat, +last: Nat, +ts: List<&2, R.Tried>, +backoff: Nat, +max: Nat, r: Maybe<&2, R.Switch>, ec: {Bool.and(Nat.is_gt(Nat.max(backoff, R.server(x, ts)), 0n), Nat.is_le(Nat.max(backoff, R.server(x, ts)), max)) == c : Bool}, ne: {Bool.not(Nat.is_eq(x, last)) == True{} : Bool}, ih: {rp.back_ok(r, last, ts, backoff, max) == True{} : Bool}) -> {rp.back_ok(R.pick.sel(c, R.Switch{x, Nat.max(backoff, R.server(x, ts))}, r), last, ts, backoff, max) == True{} : Bool}:
  match c:
    case True{}:
      +w = Nat.max(backoff, R.server(x, ts))
      rp.and_tt(Nat.is_eq(w, w), Bool.and(Bool.not(Nat.is_eq(x, last)), Bool.and(Nat.is_gt(w, 0n), Nat.is_le(w, max))), Equal.sym(Bool, True{}, Nat.is_eq(w, w), rp.eq_refl(w)), rp.and_tt(Bool.not(Nat.is_eq(x, last)), Bool.and(Nat.is_gt(w, 0n), Nat.is_le(w, max)), ne, ec))
    case False{}:
      ih

def rp.back_inv(xs: List<&2, Nat>, +last: Nat, +ts: List<&2, R.Tried>, +backoff: Nat, +max: Nat, +nin: {rp.notin(last, xs) == True{} : Bool}) -> {rp.back_ok(R.pick.back(xs, ts, backoff, max), last, ts, backoff, max) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +rest:
      ne = rp.and_l(Bool.not(Nat.is_eq(x, last)), rp.notin(last, rest), nin)
      nr = rp.and_r(Bool.not(Nat.is_eq(x, last)), rp.notin(last, rest), nin)
      rp.back_sel(Bool.and(Nat.is_gt(Nat.max(backoff, R.server(x, ts)), 0n), Nat.is_le(Nat.max(backoff, R.server(x, ts)), max)), x, last, ts, backoff, max, R.pick.back(rest, ts, backoff, max), {==}, ne, rp.back_inv(rest, last, ts, backoff, max, nr))

# the five checks of a switch together
def rp.Good(m: Maybe<&2, R.Switch>, len: Nat, ts: List<&2, R.Tried>, p: R.Policy) -> Type:
  {R.Switch.not_last(m, ts) == True{} : Bool} & ({R.Switch.fresh_first(m, len, ts) == True{} : Bool} & ({R.Switch.return_waits(m, ts) == True{} : Bool} & ({R.Switch.capped(m, R.Policy.max(p)) == True{} : Bool} & {R.Switch.within(m, ts, p) == True{} : Bool})))

def rp.good_none(+len: Nat, +ts: List<&2, R.Tried>, +p: R.Policy) -> rp.Good(None{}, len, ts, p):
  ({==}, ({==}, ({==}, ({==}, {==}))))

def rp.not_eq_move(+to: Nat, -a: Nat, -b: Nat, e: {a == b : Nat}, h: {Bool.not(Nat.is_eq(to, a)) == True{} : Bool}) -> {Bool.not(Nat.is_eq(to, b)) == True{} : Bool}:
  %e : {Bool.not(Nat.is_eq(to, _)) == True{} : Bool}
  h

def rp.ge_move(-a: Nat, -b: Nat, +c: Nat, e: {a == b : Nat}, h: {Nat.is_ge(a, c) == True{} : Bool}) -> {Nat.is_ge(b, c) == True{} : Bool}:
  %e : {Nat.is_ge(_, c) == True{} : Bool}
  h

def rp.fresh_good(m: Maybe<&2, R.Switch>, +last: Nat, +len: Nat, +ts: List<&2, R.Tried>, +p: R.Policy, +hf: {rp.fresh_ok(m, last, ts) == True{} : Bool}, elast: {last == R.last_at(ts) : Nat}, eok: {Nat.is_le(R.length(ts), R.Policy.switches(p)) == True{} : Bool}) -> rp.Good(m, len, ts, p):
  match m:
    case None{}:
      rp.good_none(len, ts, p)
    case Some{s}:
      match s:
        case R.Switch{+to, d}:
          match d:
            case 0n:
              nl = rp.and_l(Bool.not(Nat.is_eq(to, last)), Bool.not(R.seen(to, ts)), hf)
              +fr = rp.and_r(Bool.not(Nat.is_eq(to, last)), Bool.not(R.seen(to, ts)), hf)
              nl2 = rp.not_eq_move(to, last, R.last_at(ts), elast, nl)
              ff = rp.or_l(Bool.not(R.seen(to, ts)), R.all_seen(len, ts), fr)
              rw = rp.or_l(Bool.not(R.seen(to, ts)), Bool.and(Nat.is_gt(0n, 0n), Nat.is_ge(0n, R.server(to, ts))), fr)
              (nl2, (ff, (rw, (rp.le_zero(R.Policy.max(p)), eok))))
            case 1n+k:
              rp.absurdF(rp.Good(Some{R.Switch{to, 1n+k}}, len, ts, p), hf)

def rp.back_good(m: Maybe<&2, R.Switch>, +last: Nat, +len: Nat, +ts: List<&2, R.Tried>, +p: R.Policy, +backoff: Nat, +hb: {rp.back_ok(m, last, ts, backoff, R.Policy.max(p)) == True{} : Bool}, eall: {R.all_seen(len, ts) == True{} : Bool}, elast: {last == R.last_at(ts) : Nat}, eok: {Nat.is_le(R.length(ts), R.Policy.switches(p)) == True{} : Bool}) -> rp.Good(m, len, ts, p):
  match m:
    case None{}:
      rp.good_none(len, ts, p)
    case Some{s}:
      match s:
        case R.Switch{+to, +d}:
          +rest = rp.and_r(Nat.is_eq(Nat.max(backoff, R.server(to, ts)), d), Bool.and(Bool.not(Nat.is_eq(to, last)), Bool.and(Nat.is_gt(d, 0n), Nat.is_le(d, R.Policy.max(p)))), hb)
          deq = rp.eq_true(Nat.max(backoff, R.server(to, ts)), d, rp.and_l(Nat.is_eq(Nat.max(backoff, R.server(to, ts)), d), Bool.and(Bool.not(Nat.is_eq(to, last)), Bool.and(Nat.is_gt(d, 0n), Nat.is_le(d, R.Policy.max(p)))), hb))
          nl = rp.and_l(Bool.not(Nat.is_eq(to, last)), Bool.and(Nat.is_gt(d, 0n), Nat.is_le(d, R.Policy.max(p))), rest)
          +wc = rp.and_r(Bool.not(Nat.is_eq(to, last)), Bool.and(Nat.is_gt(d, 0n), Nat.is_le(d, R.Policy.max(p))), rest)
          pos = rp.and_l(Nat.is_gt(d, 0n), Nat.is_le(d, R.Policy.max(p)), wc)
          cap = rp.and_r(Nat.is_gt(d, 0n), Nat.is_le(d, R.Policy.max(p)), wc)
          nl2 = rp.not_eq_move(to, last, R.last_at(ts), elast, nl)
          ge = rp.ge_move(Nat.max(backoff, R.server(to, ts)), d, R.server(to, ts), deq, Nat.max_ge_r(backoff, R.server(to, ts)))
          ff = rp.or_r(Bool.not(R.seen(to, ts)), R.all_seen(len, ts), eall)
          rw = rp.or_r(Bool.not(R.seen(to, ts)), Bool.and(Nat.is_gt(d, 0n), Nat.is_ge(d, R.server(to, ts))), rp.and_tt(Nat.is_gt(d, 0n), Nat.is_ge(d, R.server(to, ts)), pos, ge))
          (nl2, (ff, (rw, (cap, eok))))

def rp.mode_good(all: Bool, +last: Nat, +len: Nat, +ts: List<&2, R.Tried>, +p: R.Policy, eall: {R.all_seen(len, ts) == all : Bool}, elast: {last == R.last_at(ts) : Nat}, eok: {Nat.is_le(R.length(ts), R.Policy.switches(p)) == True{} : Bool}) -> rp.Good(R.next.mode(all, last, len, ts, p), len, ts, p):
  match all:
    case True{}:
      rp.back_good(R.pick.back(R.order(last, len), ts, R.backoff(p, len, ts), R.Policy.max(p)), last, len, ts, p, R.backoff(p, len, ts), rp.back_inv(R.order(last, len), last, ts, R.backoff(p, len, ts), R.Policy.max(p), rp.order_notin(last, len)), eall, elast, eok)
    case False{}:
      rp.fresh_good(R.pick.fresh(R.order(last, len), ts), last, len, ts, p, rp.fresh_inv(R.order(last, len), last, ts, rp.order_notin(last, len)), elast, eok)

def rp.budget_good(ok: Bool, +last: Nat, +len: Nat, +ts: List<&2, R.Tried>, +p: R.Policy, eok: {Nat.is_le(R.length(ts), R.Policy.switches(p)) == ok : Bool}, elast: {last == R.last_at(ts) : Nat}) -> rp.Good(R.next.budget(ok, last, len, ts, p), len, ts, p):
  match ok:
    case True{}:
      rp.mode_good(R.all_seen(len, ts), last, len, ts, p, {==}, elast, eok)
    case False{}:
      rp.good_none(len, ts, p)

def rp.last_good(m: Maybe<&2, R.Tried>, +len: Nat, +ts: List<&2, R.Tried>, +p: R.Policy, em: {m == R.last(ts) : Maybe<&2, R.Tried>}) -> rp.Good(R.next.last(m, len, ts, p), len, ts, p):
  match m:
    case None{}:
      rp.good_none(len, ts, p)
    case Some{+t}:
      rp.budget_good(Nat.is_le(R.length(ts), R.Policy.switches(p)), R.Tried.at(t), len, ts, p, {==}, Equal.cong(Maybe<&2, R.Tried>, Nat, R.at_of, Some{t}, R.last(ts), em))

def good(+len: Nat, +ts: List<&2, R.Tried>, +p: R.Policy) -> rp.Good(R.next(len, ts, p), len, ts, p):
  rp.last_good(R.last(ts), len, ts, p, {==})

def rp.not_last_of(-m: Maybe<&2, R.Switch>, -len: Nat, -ts: List<&2, R.Tried>, -p: R.Policy, g: rp.Good(m, len, ts, p)) -> {R.Switch.not_last(m, ts) == True{} : Bool}:
  (nl, rest) = g
  nl

def rp.fresh_first_of(-m: Maybe<&2, R.Switch>, -len: Nat, -ts: List<&2, R.Tried>, -p: R.Policy, g: rp.Good(m, len, ts, p)) -> {R.Switch.fresh_first(m, len, ts) == True{} : Bool}:
  (nl, rest) = g
  (ff, more) = rest
  ff

def rp.return_waits_of(-m: Maybe<&2, R.Switch>, -len: Nat, -ts: List<&2, R.Tried>, -p: R.Policy, g: rp.Good(m, len, ts, p)) -> {R.Switch.return_waits(m, ts) == True{} : Bool}:
  (nl, rest) = g
  (ff, more) = rest
  (rw, tail) = more
  rw

def rp.capped_of(-m: Maybe<&2, R.Switch>, -len: Nat, -ts: List<&2, R.Tried>, -p: R.Policy, g: rp.Good(m, len, ts, p)) -> {R.Switch.capped(m, R.Policy.max(p)) == True{} : Bool}:
  (nl, rest) = g
  (ff, more) = rest
  (rw, tail) = more
  (cap, wi) = tail
  cap

def rp.within_of(-m: Maybe<&2, R.Switch>, -len: Nat, -ts: List<&2, R.Tried>, -p: R.Policy, g: rp.Good(m, len, ts, p)) -> {R.Switch.within(m, ts, p) == True{} : Bool}:
  (nl, rest) = g
  (ff, more) = rest
  (rw, tail) = more
  (cap, wi) = tail
  wi

def visits_once(+len: Nat, +ts: List<&2, R.Tried>, +p: R.Policy) -> {R.Switch.fresh_first(R.next(len, ts, p), len, ts) == True{} : Bool}:
  rp.fresh_first_of(R.next(len, ts, p), len, ts, p, good(len, ts, p))

def never_twice_in_a_row(+len: Nat, +ts: List<&2, R.Tried>, +p: R.Policy) -> {R.Switch.not_last(R.next(len, ts, p), ts) == True{} : Bool}:
  rp.not_last_of(R.next(len, ts, p), len, ts, p, good(len, ts, p))

def return_waits(+len: Nat, +ts: List<&2, R.Tried>, +p: R.Policy) -> {R.Switch.return_waits(R.next(len, ts, p), ts) == True{} : Bool}:
  rp.return_waits_of(R.next(len, ts, p), len, ts, p, good(len, ts, p))

def delay_capped(+len: Nat, +ts: List<&2, R.Tried>, +p: R.Policy) -> {R.Switch.capped(R.next(len, ts, p), R.Policy.max(p)) == True{} : Bool}:
  rp.capped_of(R.next(len, ts, p), len, ts, p, good(len, ts, p))

def bounded(+len: Nat, +ts: List<&2, R.Tried>, +p: R.Policy) -> {R.Switch.within(R.next(len, ts, p), ts, p) == True{} : Bool}:
  rp.within_of(R.next(len, ts, p), len, ts, p, good(len, ts, p))

# (R4) The deferred job
# ---------------------

def rp.send_off(a: R.Act) -> {R.tally.send(a, False{}) == 0n : Nat}:
  match a:
    case R.Send{}:
      {==}
    case R.Poll{}:
      {==}
    case R.Cancel{}:
      {==}
    case R.Settle{}:
      {==}
    case R.Quit{}:
      {==}

def rp.late_off(a: R.Act, +left: Nat) -> {R.tally.late(a, left, False{}) == 0n : Nat}:
  match a:
    case R.Send{}:
      {==}
    case R.Poll{}:
      {==}
    case R.Cancel{}:
      {==}
    case R.Settle{}:
      {==}
    case R.Quit{}:
      {==}

def rp.pending_send(over: Bool, +left: Nat, +gap: Nat) -> {R.tally.send(R.Step.act(R.live.pending(over, left, gap)), True{}) == 0n : Nat}:
  match over:
    case True{}:
      {==}
    case False{}:
      {==}

def rp.failed_send(again: Bool, +failed: Nat, +left: Nat, +gap: Nat) -> {R.tally.send(R.Step.act(R.live.failed(again, failed, left, gap)), True{}) == 0n : Nat}:
  match again:
    case True{}:
      {==}
    case False{}:
      {==}

# a step sends nothing while the job is live
def rp.step_send(+fails: Nat, +budget: Nat, job: R.Job, g: R.Got) -> {R.tally.send(R.Step.act(R.step(fails, budget, job, g)), R.Job.live(job)) == 0n : Nat}:
  match job:
    case R.NoJob{}:
      rp.send_off(R.Step.act(R.step(fails, budget, R.NoJob{}, g)))
    case R.Live{+failed, +left}:
      match g:
        case R.Answer{}:
          {==}
        case R.Later{+gap}:
          rp.pending_send(Nat.is_eq(left, 0n), left, gap)
        case R.Broke{r, +gap}:
          rp.failed_send(Bool.and(r, Bool.and(Nat.is_lt(failed, fails), Nat.is_gt(left, 0n))), failed, left, gap)

def rp.pending_late(over: Bool, left: Nat, +gap: Nat, e: {Nat.is_eq(left, 0n) == over : Bool}) -> {R.tally.late(R.Step.act(R.live.pending(over, left, gap)), left, True{}) == 0n : Nat}:
  match over left:
    case True{} l:
      {==}
    case False{} 0n:
      rp.absurdT({R.late.at(0n) == 0n : Nat}, e)
    case False{} 1n+k:
      {==}

def rp.failed_late(again: Bool, r: Bool, +failed: Nat, +fails: Nat, left: Nat, +gap: Nat, e: {Bool.and(r, Bool.and(Nat.is_lt(failed, fails), Nat.is_gt(left, 0n))) == again : Bool}) -> {R.tally.late(R.Step.act(R.live.failed(again, failed, left, gap)), left, True{}) == 0n : Nat}:
  match again left:
    case False{} l:
      {==}
    case True{} 0n:
      rp.absurdF({R.late.at(0n) == 0n : Nat}, rp.and_r(Nat.is_lt(failed, fails), False{}, rp.and_r(r, Bool.and(Nat.is_lt(failed, fails), False{}), e)))
    case True{} 1n+k:
      {==}

# a step never polls a live job with 0 ms left
def rp.step_late(+fails: Nat, +budget: Nat, job: R.Job, g: R.Got) -> {R.tally.late(R.Step.act(R.step(fails, budget, job, g)), R.Job.left(job), R.Job.live(job)) == 0n : Nat}:
  match job:
    case R.NoJob{}:
      rp.late_off(R.Step.act(R.step(fails, budget, R.NoJob{}, g)), 0n)
    case R.Live{+failed, +left}:
      match g:
        case R.Answer{}:
          {==}
        case R.Later{+gap}:
          rp.pending_late(Nat.is_eq(left, 0n), left, gap, {==})
        case R.Broke{+r, +gap}:
          rp.failed_late(Bool.and(r, Bool.and(Nat.is_lt(failed, fails), Nat.is_gt(left, 0n))), r, failed, fails, left, gap, {==})

def rp.sends_go(gots: List<&2, R.Got>, +fails: Nat, +budget: Nat, +job: R.Job, +s: Nat, +l: Nat) -> {R.Tally.sends(R.run.go(gots, fails, budget, job, R.Tally{s, l})) == s : Nat}:
  match gots:
    case Nil{}:
      {==}
    case +g <> +rest:
      +x = R.tally.send(R.Step.act(R.step(fails, budget, job, g)), R.Job.live(job))
      +y = R.tally.late(R.Step.act(R.step(fails, budget, job, g)), R.Job.left(job), R.Job.live(job))
      Equal.trans(Nat, R.Tally.sends(R.run.go(rest, fails, budget, R.Step.job(R.step(fails, budget, job, g)), R.Tally{Nat.add(s, x), Nat.add(l, y)})), Nat.add(s, x), s, rp.sends_go(rest, fails, budget, R.Step.job(R.step(fails, budget, job, g)), Nat.add(s, x), Nat.add(l, y)), rp.add_none(s, x, rp.step_send(fails, budget, job, g)))

def rp.late_go(gots: List<&2, R.Got>, +fails: Nat, +budget: Nat, +job: R.Job, +s: Nat, +l: Nat) -> {R.Tally.late(R.run.go(gots, fails, budget, job, R.Tally{s, l})) == l : Nat}:
  match gots:
    case Nil{}:
      {==}
    case +g <> +rest:
      +x = R.tally.send(R.Step.act(R.step(fails, budget, job, g)), R.Job.live(job))
      +y = R.tally.late(R.Step.act(R.step(fails, budget, job, g)), R.Job.left(job), R.Job.live(job))
      Equal.trans(Nat, R.Tally.late(R.run.go(rest, fails, budget, R.Step.job(R.step(fails, budget, job, g)), R.Tally{Nat.add(s, x), Nat.add(l, y)})), Nat.add(l, y), l, rp.late_go(rest, fails, budget, R.Step.job(R.step(fails, budget, job, g)), Nat.add(s, x), Nat.add(l, y)), rp.add_none(l, y, rp.step_late(fails, budget, job, g)))

def pays_once(+fails: Nat, +budget: Nat, gots: List<&2, R.Got>) -> {R.Tally.sends(R.run(fails, budget, gots)) == 0n : Nat}:
  rp.sends_go(gots, fails, budget, R.NoJob{}, 0n, 0n)

def bounded_in_time(+fails: Nat, +budget: Nat, gots: List<&2, R.Got>) -> {R.Tally.late(R.run(fails, budget, gots)) == 0n : Nat}:
  rp.late_go(gots, fails, budget, R.NoJob{}, 0n, 0n)

def rp.repoll(again: Bool, +failed: Nat, +left: Nat, +gap: Nat, e: {again == True{} : Bool}) -> {R.live.failed(again, failed, left, gap) == R.Step{R.Poll{}, R.Live{1n+failed, Nat.sub(left, 1n+gap)}} : R.Step}:
  match again:
    case True{}:
      {==}
    case False{}:
      rp.absurdF({R.live.failed(False{}, failed, left, gap) == R.Step{R.Poll{}, R.Live{1n+failed, Nat.sub(left, 1n+gap)}} : R.Step}, e)

def failed_poll_repolls(+fails: Nat, +budget: Nat, +failed: Nat, +left: Nat, +gap: Nat, below: {Nat.is_lt(failed, fails) == True{} : Bool}, live: {Nat.is_gt(left, 0n) == True{} : Bool}) -> {R.step(fails, budget, R.Live{failed, left}, R.Broke{True{}, gap}) == R.Step{R.Poll{}, R.Live{1n+failed, Nat.sub(left, 1n+gap)}} : R.Step}:
  rp.repoll(Bool.and(Nat.is_lt(failed, fails), Nat.is_gt(left, 0n)), failed, left, gap, rp.and_tt(Nat.is_lt(failed, fails), Nat.is_gt(left, 0n), below, live))

# (R5) The stall
# --------------

def stall_extends(+idle: Nat, positive: {Nat.is_gt(idle, 0n) == True{} : Bool}) -> {Nat.is_lt(idle, R.stall.next(idle)) == True{} : Bool}:
  match idle:
    case 0n:
      rp.absurdF({Nat.is_lt(0n, R.stall.next(0n)) == True{} : Bool}, positive)
    case 1n+k:
      rp.lt_add_succ(k, k)

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
      rp.le_zero(d)
    case 1n+p:
      rp.le_add(p, d)

# the bound after one more event, given the bound of the events after it
def rp.idle_next(over: Bool, +g: Nat, rest: List<&2, Nat>, +d: Nat, +last: Nat, ih: {Nat.is_le(R.Idle.at(R.idle.go(rest, d, Nat.add(last, g))), Nat.add(R.idle.life.go(rest, d, Nat.add(last, g)), d)) == True{} : Bool}) -> {Nat.is_le(R.Idle.at(R.idle.sel(over, R.IdleStall{Nat.add(last, d)}, R.idle.go(rest, d, Nat.add(last, g)))), Nat.add(R.idle.life.sel(over, last, R.idle.life.go(rest, d, Nat.add(last, g))), d)) == True{} : Bool}:
  match over:
    case True{}:
      rp.le_refl(Nat.add(last, d))
    case False{}:
      ih

def rp.idle_go(gs: List<&2, Nat>, +d: Nat, +last: Nat) -> {Nat.is_le(R.Idle.at(R.idle.go(gs, d, last)), Nat.add(R.idle.life.go(gs, d, last), d)) == True{} : Bool}:
  match gs:
    case Nil{}:
      rp.le_add(last, d)
    case +g <> +rest:
      rp.idle_next(Nat.is_gt(g, d), g, rest, d, last, rp.idle_go(rest, d, Nat.add(last, g)))

def detection_bounded(gs: List<&2, Nat>, +d: Nat) -> {Nat.is_le(R.Idle.at(R.idle(gs, d)), Nat.add(R.idle.life(gs, d), d)) == True{} : Bool}:
  match gs:
    case Nil{}:
      rp.le_refl(d)
    case +g <> +rest:
      rp.idle_next(Nat.is_gt(g, d), g, rest, d, 0n, rp.idle_go(rest, d, g))

def silent_at_deadline(+d: Nat) -> {R.idle(Nil{}, d) == R.IdleStall{d} : R.Idle}:
  {==}
