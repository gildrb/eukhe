# eukhe: lemmas the proofs of area infer_threshold share

import Base
import ../../bend/infer.bend as If
import ../../bend/infer_threshold.bend as M
import ../../laws/infer_threshold.bend as InferThreshold
import ../base/nat.bend as LNat

# Numbers
# -------

def gt.lt_le(a: Nat, b: Nat) -> {Nat.is_lt(a, b) == Nat.is_le(1n+a, b) : Bool}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      Equal.sym(Bool, Nat.is_le(0n, q), True{}, LNat.pq.le0(q))
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      gt.lt_le(p, q)

# x - a <= t exactly when x <= a + t
def gt.sub(x: Nat, a: Nat, +t: Nat) -> {Nat.is_le(Nat.sub(x, a), t) == Nat.is_le(x, Nat.add(a, t)) : Bool}:
  match x a:
    case 0n _:
      Equal.trans(Bool, Nat.is_le(0n, t), True{}, Nat.is_le(0n, Nat.add(a, t)), LNat.pq.le0(t), Equal.sym(Bool, Nat.is_le(0n, Nat.add(a, t)), True{}, LNat.pq.le0(Nat.add(a, t))))
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      gt.sub(p, q, t)

# The thresholds are the spec's sums
# ----------------------------------

def gt.lim(-w: Nat, r: M.Z) -> {M.limit_at(w, r) == InferThreshold.lim_spec(w, r) : Nat}:
  match r:
    case M.Up{a}:
      {==}
    case M.Down{a}:
      {==}

# a context is over the limit: t + r > w
def gt.above(+w: Nat, r: M.Z, +t: Nat) -> {Nat.is_le(M.limit_at(w, r), t) == InferThreshold.above(t, r, w) : Bool}:
  match r:
    case M.Up{+a}:
      Equal.trans(Bool, Nat.is_le(Nat.sub(1n+w, a), t), Nat.is_le(1n+w, Nat.add(a, t)), Nat.is_lt(w, Nat.add(a, t)),
        gt.sub(1n+w, a, t), Equal.sym(Bool, Nat.is_lt(w, Nat.add(a, t)), Nat.is_le(1n+w, Nat.add(a, t)), gt.lt_le(w, Nat.add(a, t))))
    case M.Down{+a}:
      Equal.sym(Bool, Nat.is_lt(1n+Nat.add(a, w), t), Nat.is_le(2n+Nat.add(a, w), t), gt.lt_le(1n+Nat.add(a, w), t))

def gt.above_by.r(+w: Nat, r: M.Z, c: Nat, t: Nat) -> {Nat.is_le(M.limit_at(w, r), Nat.add(c, t)) == InferThreshold.above_by(t, r, c, w) : Bool}:
  match r:
    case M.Up{a}:
      gt.above(w, M.Up{a}, Nat.add(c, t))
    case M.Down{a}:
      gt.above(w, M.Down{a}, Nat.add(c, t))

# a context is over the background threshold: t + r + c > w
def gt.above_by(+w: Nat, +r: M.Z, +c: Nat, +t: Nat) -> {Nat.is_le(Nat.sub(M.limit_at(w, r), c), t) == InferThreshold.above_by(t, r, c, w) : Bool}:
  Equal.trans(Bool, Nat.is_le(Nat.sub(M.limit_at(w, r), c), t), Nat.is_le(M.limit_at(w, r), Nat.add(c, t)), InferThreshold.above_by(t, r, c, w),
    gt.sub(M.limit_at(w, r), c, t), gt.above_by.r(w, r, c, t))


# Which threshold, by its parts
# -----------------------------

def gt.early(b: Bool) -> {M.over.early(b) == InferThreshold.over_spec.early(b) : M.Over}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def gt.margin(+w: Nat, +r: M.Z, m: M.Z, +t: Nat) -> {M.over.margin(M.limit_at(w, r), t, m) == InferThreshold.over_spec.margin(t, r, m, w) : M.Over}:
  match m:
    case M.Up{c}:
      match c:
        case 0n:
          {==}
        case 1n++b:
          %gt.above_by(w, r, 1n+b, t) : {M.over.early(Nat.is_le(Nat.sub(M.limit_at(w, r), 1n+b), t)) == InferThreshold.over_spec.early(_) : M.Over}
          gt.early(Nat.is_le(Nat.sub(M.limit_at(w, r), 1n+b), t))
    case M.Down{c}:
      {==}

def gt.at(bl: Bool, +w: Nat, +r: M.Z, m: M.Z, +t: Nat) -> {M.over.at(bl, M.limit_at(w, r), t, m) == InferThreshold.over_spec.on(bl, t, r, m, w) : M.Over}:
  match bl:
    case True{}:
      {==}
    case False{}:
      gt.margin(w, r, m, t)

# The first request over a threshold
# ----------------------------------

def gt.nb_early(b: Bool) -> {InferThreshold.is_blocks(M.over.early(b)) == False{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def gt.nb(lim: Nat, t: Nat, m: M.Z) -> {InferThreshold.is_blocks(M.over.margin(lim, t, m)) == False{} : Bool}:
  match m:
    case M.Up{c}:
      match c:
        case 0n:
          {==}
        case 1n+b:
          gt.nb_early(Nat.is_le(Nat.sub(lim, 1n+b), t))
    case M.Down{c}:
      {==}

def gt.blocks_at(bl: Bool, lim: Nat, t: Nat, m: M.Z) -> {InferThreshold.is_blocks(M.over.at(bl, lim, t, m)) == bl : Bool}:
  match bl:
    case True{}:
      {==}
    case False{}:
      gt.nb(lim, t, m)

# a context is over the blocking threshold exactly when it reaches the limit
def gt.blocks(+w: Nat, +r: M.Z, m: M.Z, +x: Nat) -> {InferThreshold.is_blocks(M.over.at(Nat.is_le(M.limit_at(w, r), x), M.limit_at(w, r), x, m)) == Nat.is_le(InferThreshold.lim_spec(w, r), x) : Bool}:
  %gt.lim(w, r) : {InferThreshold.is_blocks(M.over.at(Nat.is_le(M.limit_at(w, r), x), M.limit_at(w, r), x, m)) == Nat.is_le(_, x) : Bool}
  gt.blocks_at(Nat.is_le(M.limit_at(w, r), x), M.limit_at(w, r), x, m)

def gt.oe(b: Bool) -> {InferThreshold.is_over(M.over.early(b)) == b : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def gt.over_at(bl: Bool, +lim: Nat, +x: Nat, +b: Nat, e: {Nat.is_le(lim, x) == bl : Bool}) -> {InferThreshold.is_over(M.over.at(bl, lim, x, M.Up{1n+b})) == Nat.is_le(Nat.sub(lim, 1n+b), x) : Bool}:
  match bl:
    case True{}:
      +up = LNat.wn_le_add(1n+b, lim, x, e)
      Equal.sym(Bool, Nat.is_le(Nat.sub(lim, 1n+b), x), True{}, Equal.trans(Bool, Nat.is_le(Nat.sub(lim, 1n+b), x), Nat.is_le(lim, Nat.add(1n+b, x)), True{}, gt.sub(lim, 1n+b, x), up))
    case False{}:
      gt.oe(Nat.is_le(Nat.sub(lim, 1n+b), x))

# a context is over any threshold exactly when it reaches the background one
def gt.over(+w: Nat, +r: M.Z, +b: Nat, +x: Nat) -> {InferThreshold.is_over(M.over.at(Nat.is_le(M.limit_at(w, r), x), M.limit_at(w, r), x, M.Up{1n+b})) == Nat.is_le(Nat.sub(InferThreshold.lim_spec(w, r), 1n+b), x) : Bool}:
  %gt.lim(w, r) : {InferThreshold.is_over(M.over.at(Nat.is_le(M.limit_at(w, r), x), M.limit_at(w, r), x, M.Up{1n+b})) == Nat.is_le(Nat.sub(_, 1n+b), x) : Bool}
  gt.over_at(Nat.is_le(M.limit_at(w, r), x), M.limit_at(w, r), x, b, {==})
