# eukhe: lemmas the proofs of area infer_guard share

import Base
import ../../bend/infer.bend as If
import ../../bend/infer_guard.bend as M
import ../../laws/infer_guard.bend as InferGuard
import ../base/nat.bend as LNat

# Each test of shortest is the spec's
# -----------------------------------

# one chunk x before a, as the spec reads it: the chunk 1+q places before
# x matches, and a agrees with what follows it
def gb.h(rest: List<&2, Nat>, q: Nat, -x: Nat, -a: List<&2, Nat>, -n: Nat) -> {Bool.and(If.back(rest, q, x), InferGuard.agree(n, a, InferGuard.skip(1n+q, rest))) == InferGuard.agree(1n+n, x <> a, InferGuard.skip(q, rest)) : Bool}:
  match rest q:
    case Nil{} 0n:
      {==}
    case Nil{} 1n+j:
      {==}
    case y <> r 0n:
      {==}
    case y <> r 1n+j:
      gb.h(r, j, x, a, n)

# one chunk more: the counter's test and the spec's take the same step
def gb.step(b: Bool, -x: Nat, -rest: List<&2, Nat>, -q: Nat, -n: Nat, ih: {Nat.is_le(n, If.cycle(rest, q)) == InferGuard.agree(n, rest, InferGuard.skip(1n+q, rest)) : Bool}) -> {Nat.is_le(1n+n, If.cycle.go(x <> rest, q, b)) == Bool.and(b, InferGuard.agree(n, rest, InferGuard.skip(1n+q, rest))) : Bool}:
  match b:
    case True{}:
      ih
    case False{}:
      {==}

# the counter of period 1+q is at least m exactly when the first m chunks
# each equal the chunk 1+q places before them
def gb.test(+s: List<&2, Nat>, +q: Nat, +m: Nat) -> {Nat.is_le(m, If.cycle(s, q)) == InferGuard.agree(m, s, InferGuard.skip(1n+q, s)) : Bool}:
  match s m:
    case _ 0n:
      LNat.pq.le0(If.cycle(s, q))
    case Nil{} 1n+n:
      {==}
    case x <> +rest 1n++n:
      Equal.trans(Bool, Nat.is_le(1n+n, If.cycle.go(x <> rest, q, If.back(rest, q, x))), Bool.and(If.back(rest, q, x), InferGuard.agree(n, rest, InferGuard.skip(1n+q, rest))), InferGuard.agree(1n+n, x <> rest, InferGuard.skip(q, rest)),
        gb.step(If.back(rest, q, x), x, rest, q, n, gb.test(rest, q, n)), gb.h(rest, q, x, rest, n))

# shortest is the spec's least
# ---------------------------

def gb.pick(m: Maybe<&2, Nat>, b: Bool, -q: Nat) -> {M.shortest.pick(m, b, q) == InferGuard.least.pick(m, b, 1n+q) : Maybe<&2, Nat>}:
  match m:
    case Some{d}:
      {==}
    case None{}:
      match b:
        case True{}:
          {==}
        case False{}:
          {==}

def gb.least(+s: List<&2, Nat>, +k: Nat, n: Nat) -> {M.shortest.go(s, k, n) == InferGuard.least(s, k, n) : Maybe<&2, Nat>}:
  match n:
    case 0n:
      {==}
    case 1n++q:
      %gb.test(s, q, Nat.sub(k, 1n+q)) : {M.shortest.pick(M.shortest.go(s, k, q), Nat.is_le(Nat.sub(k, 1n+q), If.cycle(s, q)), q) == InferGuard.least.pick(InferGuard.least(s, k, q), _, 1n+q) : Maybe<&2, Nat>}
      %gb.least(s, k, q) : {M.shortest.pick(M.shortest.go(s, k, q), Nat.is_le(Nat.sub(k, 1n+q), If.cycle(s, q)), q) == InferGuard.least.pick(_, Nat.is_le(Nat.sub(k, 1n+q), If.cycle(s, q)), 1n+q) : Maybe<&2, Nat>}
      gb.pick(M.shortest.go(s, k, q), Nat.is_le(Nat.sub(k, 1n+q), If.cycle(s, q)), q)

# periods is the spec's
# ---------------------

def gb.quarter(k: Nat) -> {If.quarter(k) == InferGuard.quarter_spec(k) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n:
      {==}
    case 2n:
      {==}
    case 3n:
      {==}
    case 4n+j:
      %gb.quarter(j) : {1n+If.quarter(j) == 1n+_ : Nat}
      {==}

def gb.periods.of(q: Nat) -> {If.periods.of(q) == InferGuard.periods_spec.of(q) : Nat}:
  match q:
    case 0n:
      {==}
    case 1n+j:
      {==}

def gb.periods(+k: Nat) -> {If.periods(k) == InferGuard.periods_spec(k) : Nat}:
  %gb.quarter(k) : {If.periods.of(If.quarter(k)) == InferGuard.periods_spec.of(_) : Nat}
  gb.periods.of(If.quarter(k))

# shortest fires as the counters do
# --------------------------------

def gb.some(m: Maybe<&2, Nat>) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{p}:
      True{}

def gb.some_pick(m: Maybe<&2, Nat>, t: Bool, -q: Nat) -> {gb.some(M.shortest.pick(m, t, q)) == Bool.or(t, gb.some(m)) : Bool}:
  match m:
    case Some{p}:
      match t:
        case True{}:
          {==}
        case False{}:
          {==}
    case None{}:
      match t:
        case True{}:
          {==}
        case False{}:
          {==}

def gb.fires(+s: List<&2, Nat>, +k: Nat, n: Nat) -> {gb.some(M.shortest.go(s, k, n)) == If.fires.go(s, k, n) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n++q:
      %gb.fires(s, k, q) : {gb.some(M.shortest.pick(M.shortest.go(s, k, q), Nat.is_le(Nat.sub(k, 1n+q), If.cycle(s, q)), q)) == Bool.or(Nat.is_le(Nat.sub(k, 1n+q), If.cycle(s, q)), _) : Bool}
      gb.some_pick(M.shortest.go(s, k, q), Nat.is_le(Nat.sub(k, 1n+q), If.cycle(s, q)), q)
