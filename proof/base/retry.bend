# eukhe: lemmas the proofs of two or more areas share: retry

import Base
import ../../bend/retry.bend as R
import ./bool/and.bend as LBoolAnd
import ./bool/misc.bend as LBoolMisc
import ./list.bend as LList
import ./maybe.bend as LMaybe
import ./nat/is_eq.bend as LNatIsEq
import ./nat/is_le.bend as LNatIsLe
import ./nat/is_lt.bend as LNatIsLt
import ./nat/misc.bend as LNatMisc

# every element of upto(k, a) is at least a, so above last
def rp.notin_above(k: Nat, +a: Nat, +last: Nat, +h: {Nat.is_lt(last, a) == True{} : Bool}) -> {LBoolMisc.rp.notin(last, R.upto(k, a)) == True{} : Bool}:
  match k:
    case 0n:
      {==}
    case 1n+j:
      LBoolAnd.rp.and_tt(Bool.not(Nat.is_eq(a, last)), LBoolMisc.rp.notin(last, R.upto(j, 1n+a)), LBoolMisc.rp.not_of_false(Nat.is_eq(a, last), LNatIsEq.rp.ne_of_lt(last, a, h)), rp.notin_above(j, 1n+a, last, LNatIsLt.rp.lt_succ(last, a, h)))

# shifting the list and last by one keeps the answer
def rp.notin_shift(k: Nat, +a: Nat, +last: Nat) -> {LBoolMisc.rp.notin(1n+last, R.upto(k, 1n+a)) == LBoolMisc.rp.notin(last, R.upto(k, a)) : Bool}:
  match k:
    case 0n:
      {==}
    case 1n+j:
      %rp.notin_shift(j, 1n+a, last) : {Bool.and(Bool.not(Nat.is_eq(a, last)), LBoolMisc.rp.notin(1n+last, R.upto(j, 2n+a))) == Bool.and(Bool.not(Nat.is_eq(a, last)), _) : Bool}
      {==}

# every element of upto(k, 0) is below k, so below last when k <= last
def rp.notin_below(+k: Nat, +last: Nat, h: {Nat.is_le(k, last) == True{} : Bool}) -> {LBoolMisc.rp.notin(last, R.upto(k, 0n)) == True{} : Bool}:
  match k last:
    case 0n l:
      {==}
    case 1n+j 0n:
      LBoolMisc.rp.absurdF({LBoolMisc.rp.notin(0n, R.upto(1n+j, 0n)) == True{} : Bool}, h)
    case 1n+j 1n+q:
      %Equal.sym(Bool, LBoolMisc.rp.notin(1n+q, R.upto(j, 1n)), LBoolMisc.rp.notin(q, R.upto(j, 0n)), rp.notin_shift(j, 0n, q)) : {_ == True{} : Bool}
      rp.notin_below(j, q, h)

# the chain order after last never holds last
def rp.order_notin(+last: Nat, +len: Nat) -> {LBoolMisc.rp.notin(last, R.order(last, len)) == True{} : Bool}:
  LList.rp.notin_append(last, R.upto(Nat.sub(len, 1n+last), 1n+last), R.upto(Nat.min(last, len), 0n), rp.notin_above(Nat.sub(len, 1n+last), 1n+last, last, LNatIsLt.rp.lt_self(last)), rp.notin_below(Nat.min(last, len), last, LNatIsLe.rp.min_le(last, len)))

# The picks
# ---------

def rp.fresh_sel(c: Bool, +x: Nat, +last: Nat, +ts: List<&2, R.Tried>, r: Maybe<&2, R.Switch>, ec: {Bool.not(R.seen(x, ts)) == c : Bool}, ne: {Bool.not(Nat.is_eq(x, last)) == True{} : Bool}, ih: {LBoolMisc.rp.fresh_ok(r, last, ts) == True{} : Bool}) -> {LBoolMisc.rp.fresh_ok(R.pick.sel(c, R.Switch{x, 0n}, r), last, ts) == True{} : Bool}:
  match c:
    case True{}:
      LBoolAnd.rp.and_tt(Bool.not(Nat.is_eq(x, last)), Bool.not(R.seen(x, ts)), ne, ec)
    case False{}:
      ih

def rp.fresh_inv(xs: List<&2, Nat>, +last: Nat, +ts: List<&2, R.Tried>, +nin: {LBoolMisc.rp.notin(last, xs) == True{} : Bool}) -> {LBoolMisc.rp.fresh_ok(R.pick.fresh(xs, ts), last, ts) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +rest:
      ne = LBoolAnd.rp.and_l(Bool.not(Nat.is_eq(x, last)), LBoolMisc.rp.notin(last, rest), nin)
      nr = LBoolAnd.rp.and_r(Bool.not(Nat.is_eq(x, last)), LBoolMisc.rp.notin(last, rest), nin)
      rp.fresh_sel(Bool.not(R.seen(x, ts)), x, last, ts, R.pick.fresh(rest, ts), {==}, ne, rp.fresh_inv(rest, last, ts, nr))

def rp.back_sel(c: Bool, +x: Nat, +last: Nat, +ts: List<&2, R.Tried>, +backoff: Nat, +max: Nat, r: Maybe<&2, R.Switch>, ec: {Bool.and(Nat.is_gt(Nat.max(backoff, R.server(x, ts)), 0n), Nat.is_le(Nat.max(backoff, R.server(x, ts)), max)) == c : Bool}, ne: {Bool.not(Nat.is_eq(x, last)) == True{} : Bool}, ih: {LBoolMisc.rp.back_ok(r, last, ts, backoff, max) == True{} : Bool}) -> {LBoolMisc.rp.back_ok(R.pick.sel(c, R.Switch{x, Nat.max(backoff, R.server(x, ts))}, r), last, ts, backoff, max) == True{} : Bool}:
  match c:
    case True{}:
      +w = Nat.max(backoff, R.server(x, ts))
      LBoolAnd.rp.and_tt(Nat.is_eq(w, w), Bool.and(Bool.not(Nat.is_eq(x, last)), Bool.and(Nat.is_gt(w, 0n), Nat.is_le(w, max))), Equal.sym(Bool, True{}, Nat.is_eq(w, w), LNatIsEq.rp.eq_refl(w)), LBoolAnd.rp.and_tt(Bool.not(Nat.is_eq(x, last)), Bool.and(Nat.is_gt(w, 0n), Nat.is_le(w, max)), ne, ec))
    case False{}:
      ih

def rp.back_inv(xs: List<&2, Nat>, +last: Nat, +ts: List<&2, R.Tried>, +backoff: Nat, +max: Nat, +nin: {LBoolMisc.rp.notin(last, xs) == True{} : Bool}) -> {LBoolMisc.rp.back_ok(R.pick.back(xs, ts, backoff, max), last, ts, backoff, max) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +rest:
      ne = LBoolAnd.rp.and_l(Bool.not(Nat.is_eq(x, last)), LBoolMisc.rp.notin(last, rest), nin)
      nr = LBoolAnd.rp.and_r(Bool.not(Nat.is_eq(x, last)), LBoolMisc.rp.notin(last, rest), nin)
      rp.back_sel(Bool.and(Nat.is_gt(Nat.max(backoff, R.server(x, ts)), 0n), Nat.is_le(Nat.max(backoff, R.server(x, ts)), max)), x, last, ts, backoff, max, R.pick.back(rest, ts, backoff, max), {==}, ne, rp.back_inv(rest, last, ts, backoff, max, nr))

def rp.fresh_good(m: Maybe<&2, R.Switch>, +last: Nat, +len: Nat, +ts: List<&2, R.Tried>, +p: R.Policy, +hf: {LBoolMisc.rp.fresh_ok(m, last, ts) == True{} : Bool}, elast: {last == R.last_at(ts) : Nat}, eok: {Nat.is_le(R.length(ts), R.Policy.switches(p)) == True{} : Bool}) -> LMaybe.rp.Good(m, len, ts, p):
  match m:
    case None{}:
      LMaybe.rp.good_none(len, ts, p)
    case Some{s}:
      match s:
        case R.Switch{+to, d}:
          match d:
            case 0n:
              nl = LBoolAnd.rp.and_l(Bool.not(Nat.is_eq(to, last)), Bool.not(R.seen(to, ts)), hf)
              +fr = LBoolAnd.rp.and_r(Bool.not(Nat.is_eq(to, last)), Bool.not(R.seen(to, ts)), hf)
              nl2 = LBoolMisc.rp.not_eq_move(to, last, R.last_at(ts), elast, nl)
              ff = LBoolMisc.rp.or_l(Bool.not(R.seen(to, ts)), R.all_seen(len, ts), fr)
              rw = LBoolMisc.rp.or_l(Bool.not(R.seen(to, ts)), Bool.and(Nat.is_gt(0n, 0n), Nat.is_ge(0n, R.server(to, ts))), fr)
              (nl2, (ff, (rw, (LNatIsLe.rp.le_zero(R.Policy.max(p)), eok))))
            case 1n+k:
              LBoolMisc.rp.absurdF(LMaybe.rp.Good(Some{R.Switch{to, 1n+k}}, len, ts, p), hf)

def rp.back_good(m: Maybe<&2, R.Switch>, +last: Nat, +len: Nat, +ts: List<&2, R.Tried>, +p: R.Policy, +backoff: Nat, +hb: {LBoolMisc.rp.back_ok(m, last, ts, backoff, R.Policy.max(p)) == True{} : Bool}, eall: {R.all_seen(len, ts) == True{} : Bool}, elast: {last == R.last_at(ts) : Nat}, eok: {Nat.is_le(R.length(ts), R.Policy.switches(p)) == True{} : Bool}) -> LMaybe.rp.Good(m, len, ts, p):
  match m:
    case None{}:
      LMaybe.rp.good_none(len, ts, p)
    case Some{s}:
      match s:
        case R.Switch{+to, +d}:
          +rest = LBoolAnd.rp.and_r(Nat.is_eq(Nat.max(backoff, R.server(to, ts)), d), Bool.and(Bool.not(Nat.is_eq(to, last)), Bool.and(Nat.is_gt(d, 0n), Nat.is_le(d, R.Policy.max(p)))), hb)
          deq = LNatIsEq.rp.eq_true(Nat.max(backoff, R.server(to, ts)), d, LBoolAnd.rp.and_l(Nat.is_eq(Nat.max(backoff, R.server(to, ts)), d), Bool.and(Bool.not(Nat.is_eq(to, last)), Bool.and(Nat.is_gt(d, 0n), Nat.is_le(d, R.Policy.max(p)))), hb))
          nl = LBoolAnd.rp.and_l(Bool.not(Nat.is_eq(to, last)), Bool.and(Nat.is_gt(d, 0n), Nat.is_le(d, R.Policy.max(p))), rest)
          +wc = LBoolAnd.rp.and_r(Bool.not(Nat.is_eq(to, last)), Bool.and(Nat.is_gt(d, 0n), Nat.is_le(d, R.Policy.max(p))), rest)
          pos = LBoolAnd.rp.and_l(Nat.is_gt(d, 0n), Nat.is_le(d, R.Policy.max(p)), wc)
          cap = LBoolAnd.rp.and_r(Nat.is_gt(d, 0n), Nat.is_le(d, R.Policy.max(p)), wc)
          nl2 = LBoolMisc.rp.not_eq_move(to, last, R.last_at(ts), elast, nl)
          ge = LNatMisc.rp.ge_move(Nat.max(backoff, R.server(to, ts)), d, R.server(to, ts), deq, Nat.max_ge_r(backoff, R.server(to, ts)))
          ff = LBoolMisc.rp.or_r(Bool.not(R.seen(to, ts)), R.all_seen(len, ts), eall)
          rw = LBoolMisc.rp.or_r(Bool.not(R.seen(to, ts)), Bool.and(Nat.is_gt(d, 0n), Nat.is_ge(d, R.server(to, ts))), LBoolAnd.rp.and_tt(Nat.is_gt(d, 0n), Nat.is_ge(d, R.server(to, ts)), pos, ge))
          (nl2, (ff, (rw, (cap, eok))))

def rp.mode_good(all: Bool, +last: Nat, +len: Nat, +ts: List<&2, R.Tried>, +p: R.Policy, eall: {R.all_seen(len, ts) == all : Bool}, elast: {last == R.last_at(ts) : Nat}, eok: {Nat.is_le(R.length(ts), R.Policy.switches(p)) == True{} : Bool}) -> LMaybe.rp.Good(R.next.mode(all, last, len, ts, p), len, ts, p):
  match all:
    case True{}:
      rp.back_good(R.pick.back(R.order(last, len), ts, R.backoff(p, len, ts), R.Policy.max(p)), last, len, ts, p, R.backoff(p, len, ts), rp.back_inv(R.order(last, len), last, ts, R.backoff(p, len, ts), R.Policy.max(p), rp.order_notin(last, len)), eall, elast, eok)
    case False{}:
      rp.fresh_good(R.pick.fresh(R.order(last, len), ts), last, len, ts, p, rp.fresh_inv(R.order(last, len), last, ts, rp.order_notin(last, len)), elast, eok)

def rp.budget_good(ok: Bool, +last: Nat, +len: Nat, +ts: List<&2, R.Tried>, +p: R.Policy, eok: {Nat.is_le(R.length(ts), R.Policy.switches(p)) == ok : Bool}, elast: {last == R.last_at(ts) : Nat}) -> LMaybe.rp.Good(R.next.budget(ok, last, len, ts, p), len, ts, p):
  match ok:
    case True{}:
      rp.mode_good(R.all_seen(len, ts), last, len, ts, p, {==}, elast, eok)
    case False{}:
      LMaybe.rp.good_none(len, ts, p)

def rp.last_good(m: Maybe<&2, R.Tried>, +len: Nat, +ts: List<&2, R.Tried>, +p: R.Policy, em: {m == R.last(ts) : Maybe<&2, R.Tried>}) -> LMaybe.rp.Good(R.next.last(m, len, ts, p), len, ts, p):
  match m:
    case None{}:
      LMaybe.rp.good_none(len, ts, p)
    case Some{+t}:
      rp.budget_good(Nat.is_le(R.length(ts), R.Policy.switches(p)), R.Tried.at(t), len, ts, p, {==}, Equal.cong(Maybe<&2, R.Tried>, Nat, R.at_of, Some{t}, R.last(ts), em))

def good(+len: Nat, +ts: List<&2, R.Tried>, +p: R.Policy) -> LMaybe.rp.Good(R.next(len, ts, p), len, ts, p):
  rp.last_good(R.last(ts), len, ts, p, {==})
