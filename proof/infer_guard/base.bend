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

# The periods: k/4 by its inverse
# -------------------------------

def gb.BD(b: Bool, G: Type) -> Type:
  match b:
    case True{}:
      G
    case False{}:
      Unit

# a False that is True proves anything
def gb.absurd_le(-G: Type, e: {False{} == True{} : Bool}) -> G:
  %e : gb.BD(_, G)
  Unit{}

# no count is below 0
def gb.lt_zero(-G: Type, j: Nat, e: {Nat.is_lt(j, 0n) == True{} : Bool}) -> G:
  match j:
    case 0n:
      gb.absurd_le(G, e)
    case 1n+i:
      gb.absurd_le(G, e)

# 4q <= k < 4(1 + q): k/4 is q
def gb.quarter_at(q: Nat, k: Nat, lo: {Nat.is_le(Nat.mul(q, 4n), k) == True{} : Bool}, hi: {Nat.is_lt(k, Nat.mul(1n+q, 4n)) == True{} : Bool}) -> {If.quarter(k) == q : Nat}:
  match q:
    case 0n:
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
          gb.lt_zero({If.quarter(4n+j) == 0n : Nat}, j, hi)
    case 1n+p:
      match k:
        case 0n:
          gb.absurd_le({If.quarter(0n) == 1n+p : Nat}, lo)
        case 1n:
          gb.absurd_le({If.quarter(1n) == 1n+p : Nat}, lo)
        case 2n:
          gb.absurd_le({If.quarter(2n) == 1n+p : Nat}, lo)
        case 3n:
          gb.absurd_le({If.quarter(3n) == 1n+p : Nat}, lo)
        case 4n+j:
          Equal.cong(Nat, Nat, x => 1n+x, If.quarter(j), p, gb.quarter_at(p, j, lo, hi))

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

# Fewer chunks than the window: no period fires
# ---------------------------------------------

def gb.if_false(b: Bool, G: Type) -> Type:
  match b:
    case False{}:
      G
    case True{}:
      Unit

def gb.if_true(b: Bool, G: Type) -> Type:
  match b:
    case True{}:
      G
    case False{}:
      Unit

# a True that is False proves anything
def gb.absurd_tf(-G: Type, e: {True{} == False{} : Bool}) -> G:
  %e : gb.if_false(_, G)
  Unit{}

# a False that is True proves anything
def gb.absurd_ft(-G: Type, e: {False{} == True{} : Bool}) -> G:
  %e : gb.if_true(_, G)
  Unit{}

def gb.and_false(b: Bool) -> {Bool.and(b, False{}) == False{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

# m items never agree with a list that holds fewer than m
def gb.agree_short(m: Nat, a: List<&2, Nat>, b: List<&2, Nat>, h: {M.covers(m, b) == False{} : Bool}) -> {InferGuard.agree(m, a, b) == False{} : Bool}:
  match m:
    case 0n:
      gb.absurd_tf({InferGuard.agree(0n, a, b) == False{} : Bool}, h)
    case 1n+j:
      match a:
        case Nil{}:
          {==}
        case x <> ra:
          match b:
            case Nil{}:
              {==}
            case y <> rb:
              %Equal.sym(Bool, InferGuard.agree(j, ra, rb), False{}, gb.agree_short(j, ra, rb, h)) : {Bool.and(Nat.is_eq(x, y), _) == False{} : Bool}
              gb.and_false(Nat.is_eq(x, y))

# k - j items, j < k, are more than no item
def gb.short_nil(j: Nat, k: Nat, h: {Nat.is_lt(j, k) == True{} : Bool}) -> {M.covers(Nat.sub(k, j), Nil{}) == False{} : Bool}:
  match j k:
    case 0n 0n:
      gb.absurd_ft({M.covers(0n, Nil{}) == False{} : Bool}, h)
    case 0n 1n+k1:
      {==}
    case 1n+j1 0n:
      gb.absurd_ft({M.covers(0n, Nil{}) == False{} : Bool}, h)
    case 1n+j1 1n+k1:
      gb.short_nil(j1, k1, h)

# s holds fewer than k chunks: what follows its first p, p < k, holds
# fewer than k - p
def gb.skip_short(p: Nat, k: Nat, s: List<&2, Nat>, h: {M.covers(k, s) == False{} : Bool}, hp: {Nat.is_lt(p, k) == True{} : Bool}) -> {M.covers(Nat.sub(k, p), InferGuard.skip(p, s)) == False{} : Bool}:
  match p k s:
    case 0n 0n _:
      gb.absurd_ft({M.covers(0n, InferGuard.skip(0n, s)) == False{} : Bool}, hp)
    case 0n 1n+k1 _:
      h
    case 1n+p1 0n _:
      gb.absurd_ft({M.covers(0n, InferGuard.skip(1n+p1, s)) == False{} : Bool}, hp)
    case 1n+p1 1n+k1 Nil{}:
      gb.short_nil(p1, k1, hp)
    case 1n+p1 1n+k1 y <> rest:
      gb.skip_short(p1, k1, rest, h, hp)

def gb.lt_pred(q: Nat, k: Nat, h: {Nat.is_lt(1n+q, k) == True{} : Bool}) -> {Nat.is_lt(q, k) == True{} : Bool}:
  match q k:
    case 0n 0n:
      gb.absurd_ft({Nat.is_lt(0n, 0n) == True{} : Bool}, h)
    case 0n 1n+k1:
      {==}
    case 1n+q1 0n:
      gb.absurd_ft({Nat.is_lt(1n+q1, 0n) == True{} : Bool}, h)
    case 1n+q1 1n+k1:
      gb.lt_pred(q1, k1, h)

def gb.lt_up(a: Nat, b: Nat, h: {Nat.is_lt(a, b) == True{} : Bool}) -> {Nat.is_lt(a, 1n+b) == True{} : Bool}:
  match a b:
    case 0n 0n:
      gb.absurd_ft({Nat.is_lt(0n, 1n) == True{} : Bool}, h)
    case 0n 1n+b1:
      {==}
    case 1n+a1 0n:
      gb.absurd_ft({Nat.is_lt(1n+a1, 1n) == True{} : Bool}, h)
    case 1n+a1 1n+b1:
      gb.lt_up(a1, b1, h)

# the period 1+q, 1+q < k, never fires on fewer than k chunks
def gb.test_false(+s: List<&2, Nat>, +q: Nat, +k: Nat, +h: {M.covers(k, s) == False{} : Bool}, +hq: {Nat.is_lt(1n+q, k) == True{} : Bool}) -> {Nat.is_le(Nat.sub(k, 1n+q), If.cycle(s, q)) == False{} : Bool}:
  Equal.trans(Bool, Nat.is_le(Nat.sub(k, 1n+q), If.cycle(s, q)), InferGuard.agree(Nat.sub(k, 1n+q), s, InferGuard.skip(1n+q, s)), False{},
    gb.test(s, q, Nat.sub(k, 1n+q)), gb.agree_short(Nat.sub(k, 1n+q), s, InferGuard.skip(1n+q, s), gb.skip_short(1n+q, k, s, h, hq)))

# no period below k fires on fewer than k chunks
def gb.none_go(+s: List<&2, Nat>, +k: Nat, n: Nat, +h: {M.covers(k, s) == False{} : Bool}, hn: {Nat.is_lt(n, k) == True{} : Bool}) -> {M.shortest.go(s, k, n) == None{} : Maybe<&2, Nat>}:
  match n:
    case 0n:
      {==}
    case 1n++q:
      +hq = hn
      %Equal.sym(Maybe<&2, Nat>, M.shortest.go(s, k, q), None{}, gb.none_go(s, k, q, h, gb.lt_pred(q, k, hq))) : {M.shortest.pick(_, Nat.is_le(Nat.sub(k, 1n+q), If.cycle(s, q)), q) == None{} : Maybe<&2, Nat>}
      %Equal.sym(Bool, Nat.is_le(Nat.sub(k, 1n+q), If.cycle(s, q)), False{}, gb.test_false(s, q, k, h, hq)) : {M.shortest.pick(None{}, _, q) == None{} : Maybe<&2, Nat>}
      {==}

# k/4 is below 1+k
def gb.quarter_lt(+d: Nat) -> {Nat.is_lt(If.quarter(d), 1n+d) == True{} : Bool}:
  match d:
    case 0n:
      {==}
    case 1n:
      {==}
    case 2n:
      {==}
    case 3n:
      {==}
    case 4n+e:
      gb.lt_up(If.quarter(e), 3n+e, gb.lt_up(If.quarter(e), 2n+e, gb.lt_up(If.quarter(e), 1n+e, gb.quarter_lt(e))))

# a window of at least 2 checks fewer periods than its chunks
def gb.periods_lt(+j: Nat) -> {Nat.is_lt(If.periods(2n+j), 2n+j) == True{} : Bool}:
  match j:
    case 0n:
      {==}
    case 1n:
      {==}
    case 2n+d:
      gb.lt_up(If.quarter(d), 2n+d, gb.lt_up(If.quarter(d), 1n+d, gb.quarter_lt(d)))

# chunks x <> seen fewer than the window: the periods' search finds none
def gb.cover.none(+x: Nat, +seen: List<&2, Nat>, +k: Nat, +e: {M.covers(k, x <> seen) == False{} : Bool}) -> {M.shortest.go(x <> seen, k, If.periods(k)) == None{} : Maybe<&2, Nat>}:
  match k:
    case 0n:
      gb.absurd_tf({M.shortest.go(x <> seen, 0n, If.periods(0n)) == None{} : Maybe<&2, Nat>}, e)
    case 1n:
      gb.absurd_tf({M.shortest.go(x <> seen, 1n, If.periods(1n)) == None{} : Maybe<&2, Nat>}, e)
    case 2n+j:
      gb.none_go(x <> seen, 2n+j, If.periods(2n+j), e, gb.periods_lt(j))

def gb.cover.of(b: Bool, +x: Nat, +seen: List<&2, Nat>, +k: Nat, e: {M.covers(k, x <> seen) == b : Bool}) -> {M.shortest.of(b, x <> seen, k) == M.shortest.go(x <> seen, k, If.periods(k)) : Maybe<&2, Nat>}:
  match b:
    case True{}:
      {==}
    case False{}:
      Equal.sym(Maybe<&2, Nat>, M.shortest.go(x <> seen, k, If.periods(k)), None{}, gb.cover.none(x, seen, k, e))

# the guard's search after a chunk is the periods' search: the gate on
# the window's chunks changes no answer
def gb.cover(+x: Nat, +seen: List<&2, Nat>, +k: Nat) -> {M.shortest(x <> seen, k) == M.shortest.go(x <> seen, k, If.periods(k)) : Maybe<&2, Nat>}:
  gb.cover.of(M.covers(k, x <> seen), x, seen, k, {==})
