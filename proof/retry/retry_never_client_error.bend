# eukhe: the proof of LAW retry_never_client_error

import Base
import ../../bend/retry.bend as R
import ../../LAWS.bend as Laws
import ../base.bend as L

def rp.or_ff(a: Bool, b: Bool, ea: {a == False{} : Bool}, eb: {b == False{} : Bool}) -> {Bool.or(a, b) == False{} : Bool}:
  match a:
    case True{}:
      L.rp.absurdT({Bool.or(True{}, b) == False{} : Bool}, ea)
    case False{}:
      eb

def rp.client(lt: Bool, +s: Nat, below: {lt == True{} : Bool}, n408: {Nat.is_eq(s, 408n) == False{} : Bool}, n409: {Nat.is_eq(s, 409n) == False{} : Bool}, n429: {Nat.is_eq(s, 429n) == False{} : Bool}) -> {R.status.ok.go(lt, s) == False{} : Bool}:
  match lt:
    case True{}:
      rp.or_ff(Nat.is_eq(s, 408n), Bool.or(Nat.is_eq(s, 409n), Nat.is_eq(s, 429n)), n408, rp.or_ff(Nat.is_eq(s, 409n), Nat.is_eq(s, 429n), n409, n429))
    case False{}:
      L.rp.absurdF({R.status.ok.go(False{}, s) == False{} : Bool}, below)

def never_client_error(parked: Bool, limit: Bool, kind: Maybe<&2, R.Cause>, text: Bool, +s: Nat, below: {Nat.is_lt(s, 500n) == True{} : Bool}, n408: {Nat.is_eq(s, 408n) == False{} : Bool}, n409: {Nat.is_eq(s, 409n) == False{} : Bool}, n429: {Nat.is_eq(s, 429n) == False{} : Bool}) -> {R.retryable(R.Facts{parked, limit, Some{s}, kind, text}) == False{} : Bool}:
  match parked limit:
    case True{} l:
      {==}
    case False{} True{}:
      {==}
    case False{} False{}:
      rp.client(Nat.is_lt(s, 500n), s, below, n408, n409, n429)

def Laws.retry_never_client_error(parked, limit, kind, text, s, below, not408, not409, not429):
  never_client_error(parked, limit, kind, text, s, below, not408, not409, not429)
