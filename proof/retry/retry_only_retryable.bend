# eukhe: the proof of LAW retry_only_retryable

import Base
import ../../bend/retry.bend as R
import ../../LAWS.bend as Laws
import ../base.bend as L

def rp.cmp_ge(c: Cmp, e: {Cmp.is_lt(c) == False{} : Bool}) -> {Cmp.is_ge(c) == True{} : Bool}:
  match c:
    case LT{}:
      L.rp.absurdT({False{} == True{} : Bool}, e)
    case EQ{}:
      {==}
    case GT{}:
      {==}

def rp.ge_of_not_lt(+a: Nat, +b: Nat, e: {Nat.is_lt(a, b) == False{} : Bool}) -> {Nat.is_ge(a, b) == True{} : Bool}:
  rp.cmp_ge(Nat.cmp(a, b), e)

def rp.only(lt: Bool, +s: Nat, elt: {Nat.is_lt(s, 500n) == lt : Bool}, r: {R.status.ok.go(lt, s) == True{} : Bool}) -> {Bool.or(Nat.is_ge(s, 500n), R.status.listed(s)) == True{} : Bool}:
  match lt:
    case True{}:
      L.rp.or_r(Nat.is_ge(s, 500n), R.status.listed(s), r)
    case False{}:
      L.rp.or_l(Nat.is_ge(s, 500n), R.status.listed(s), rp.ge_of_not_lt(s, 500n, elt))

def only_retryable(parked: Bool, limit: Bool, kind: Maybe<&2, R.Cause>, text: Bool, +s: Nat, retried: {R.retryable(R.Facts{parked, limit, Some{s}, kind, text}) == True{} : Bool}) -> {Bool.or(Nat.is_ge(s, 500n), R.status.listed(s)) == True{} : Bool}:
  match parked limit:
    case True{} l:
      L.rp.absurdF({Bool.or(Nat.is_ge(s, 500n), R.status.listed(s)) == True{} : Bool}, retried)
    case False{} True{}:
      L.rp.absurdF({Bool.or(Nat.is_ge(s, 500n), R.status.listed(s)) == True{} : Bool}, retried)
    case False{} False{}:
      rp.only(Nat.is_lt(s, 500n), s, {==}, retried)

def Laws.retry_only_retryable(parked, limit, kind, text, s, retried):
  only_retryable(parked, limit, kind, text, s, retried)
