# eukhe: the proof of LAW infer_threshold_target_under
# An empty context under every threshold (`live`, through LAW
# infer_threshold_over_exact) puts the start s at 1 or more, and the target
# s / 2 below it (itu.half). A context t within the target is then below
# the start, so below every threshold, and the gate passes Under.

import Base
import ../../bend/infer_threshold.bend as M
import ../../laws/infer_threshold.bend as InferThreshold
import ../base/nat.bend as LNat
import ./base.bend as LAThreshold
import ./base/walk.bend as LAWalk
import ./infer_threshold_over_exact.bend as PInferThresholdOverExact

def itu.OIf(o: M.Over, G: Type) -> Type:
  match o:
    case M.Under{}:
      Unit
    case M.Early{}:
      G
    case M.Blocks{}:
      G

# Under is neither threshold
def itu.bu(-G: Type, e: {M.Blocks{} == M.Under{} : M.Over}) -> G:
  %Equal.sym(M.Over, M.Blocks{}, M.Under{}, e) : itu.OIf(_, G)
  Unit{}

def itu.eu(-G: Type, e: {M.Early{} == M.Under{} : M.Over}) -> G:
  %Equal.sym(M.Over, M.Early{}, M.Under{}, e) : itu.OIf(_, G)
  Unit{}

# Halves
# ------

def itu.dm(n: Nat, m: Nat, +d: Nat, +r: Nat) -> {Nat.is_le(Pair.fst(Nat, Nat, Nat.divmod.go(n, m, d, r)), Nat.add(n, d)) == True{} : Bool}:
  match n:
    case 0n:
      LNat.pu.le_refl(d)
    case 1n++np:
      match m:
        case 0n:
          %LNat.add_succ(np, d) : {Nat.is_le(Pair.fst(Nat, Nat, Nat.divmod.go(np, r, 1n+d, 0n)), _) == True{} : Bool}
          itu.dm(np, r, 1n+d, 0n)
        case 1n++mp:
          LNat.pu.le_succ_r(Pair.fst(Nat, Nat, Nat.divmod.go(np, mp, d, 1n+r)), Nat.add(np, d), itu.dm(np, mp, d, 1n+r))

# (1 + p) / 2 <= p
def itu.half(+p: Nat) -> {Nat.is_le(Nat.div(1n+p, 2n), p) == True{} : Bool}:
  %LNat.add_zero(p) : {Nat.is_le(Nat.div(1n+p, 2n), _) == True{} : Bool}
  itu.dm(p, 0n, 0n, 1n)

# t <= s / 2 with s > 0: t < s
def itu.below(s: Nat, +t: Nat, l0: {Nat.is_le(s, 0n) == False{} : Bool}, small: {Nat.is_le(t, Nat.div(s, 2n)) == True{} : Bool}) -> {Nat.is_lt(t, s) == True{} : Bool}:
  match s:
    case 0n:
      LAWalk.iw.tf({Nat.is_lt(t, 0n) == True{} : Bool}, l0)
    case 1n++p:
      %Equal.sym(Bool, Nat.is_lt(t, 1n+p), Nat.is_le(1n+t, 1n+p), LAThreshold.gt.lt_le(t, 1n+p)) : {_ == True{} : Bool}
      LNat.pu.le_trans(t, Nat.div(1n+p, 2n), p, small, itu.half(p))

# t < s <= l: t < l
def itu.lt_le(+t: Nat, +s: Nat, +l: Nat, ts: {Nat.is_lt(t, s) == True{} : Bool}, sl: {Nat.is_le(s, l) == True{} : Bool}) -> {Nat.is_lt(t, l) == True{} : Bool}:
  +a = Equal.trans(Bool, Nat.is_le(1n+t, s), Nat.is_lt(t, s), True{}, Equal.sym(Bool, Nat.is_lt(t, s), Nat.is_le(1n+t, s), LAThreshold.gt.lt_le(t, s)), ts)
  %Equal.sym(Bool, Nat.is_lt(t, l), Nat.is_le(1n+t, l), LAThreshold.gt.lt_le(t, l)) : {_ == True{} : Bool}
  LNat.pu.le_trans(1n+t, s, l, a, sl)

# The threshold
# -------------

# an empty context under the limit: the limit is 1 or more
def itu.pos(lim: Nat, -m: M.Z, live: {M.over.at(Nat.is_le(lim, 0n), lim, 0n, m) == M.Under{} : M.Over}) -> {Nat.is_le(lim, 0n) == False{} : Bool}:
  match lim:
    case 0n:
      itu.bu({Nat.is_le(0n, 0n) == False{} : Bool}, live)
    case 1n+p:
      {==}

def itu.early(x: Bool, e: {M.over.early(x) == M.Under{} : M.Over}) -> {x == False{} : Bool}:
  match x:
    case True{}:
      itu.eu({True{} == False{} : Bool}, e)
    case False{}:
      {==}

# no margin
def itu.flat(+lim: Nat, +t: Nat, m: M.Z, l0: {Nat.is_le(lim, 0n) == False{} : Bool}, small: {Nat.is_le(t, Nat.div(lim, 2n)) == True{} : Bool}, mu: {M.over.margin(lim, t, m) == M.Under{} : M.Over}) -> {M.over.at(Nat.is_le(lim, t), lim, t, m) == M.Under{} : M.Over}:
  %Equal.sym(Bool, Nat.is_le(lim, t), False{}, LNat.pi.lt_nle(t, lim, itu.below(lim, t, l0, small))) : {M.over.at(_, lim, t, m) == M.Under{} : M.Over}
  mu

def itu.up0(+lim: Nat, +t: Nat, live: {M.over.at(Nat.is_le(lim, 0n), lim, 0n, M.Up{0n}) == M.Under{} : M.Over}, small: {Nat.is_le(t, Nat.div(Nat.sub(lim, 0n), 2n)) == True{} : Bool}) -> {M.over.at(Nat.is_le(lim, t), lim, t, M.Up{0n}) == M.Under{} : M.Over}:
  +s2 = Equal.trans(Bool, Nat.is_le(t, Nat.div(lim, 2n)), Nat.is_le(t, Nat.div(Nat.sub(lim, 0n), 2n)), True{}, Equal.cong(Nat, Bool, z => Nat.is_le(t, Nat.div(z, 2n)), lim, Nat.sub(lim, 0n), LNat.pj.sub_zero(lim)), small)
  itu.flat(lim, t, M.Up{0n}, itu.pos(lim, M.Up{0n}, live), s2, {==})

def itu.down(+lim: Nat, +t: Nat, +c: Nat, live: {M.over.at(Nat.is_le(lim, 0n), lim, 0n, M.Down{c}) == M.Under{} : M.Over}, small: {Nat.is_le(t, Nat.div(lim, 2n)) == True{} : Bool}) -> {M.over.at(Nat.is_le(lim, t), lim, t, M.Down{c}) == M.Under{} : M.Over}:
  itu.flat(lim, t, M.Down{c}, itu.pos(lim, M.Down{c}, live), small, {==})

def itu.live1(+lim: Nat, +b: Nat, l0: {Nat.is_le(lim, 0n) == False{} : Bool}, live: {M.over.at(Nat.is_le(lim, 0n), lim, 0n, M.Up{1n+b}) == M.Under{} : M.Over}) -> {M.over.early(Nat.is_le(Nat.sub(lim, 1n+b), 0n)) == M.Under{} : M.Over}:
  %l0 : {M.over.at(_, lim, 0n, M.Up{1n+b}) == M.Under{} : M.Over}
  live

# a positive margin b + 1: the start lim - (b + 1) is 1 or more
def itu.up(+lim: Nat, +t: Nat, +b: Nat, +live: {M.over.at(Nat.is_le(lim, 0n), lim, 0n, M.Up{1n+b}) == M.Under{} : M.Over}, small: {Nat.is_le(t, Nat.div(Nat.sub(lim, 1n+b), 2n)) == True{} : Bool}) -> {M.over.at(Nat.is_le(lim, t), lim, t, M.Up{1n+b}) == M.Under{} : M.Over}:
  +s = Nat.sub(lim, 1n+b)
  +l0 = itu.pos(lim, M.Up{1n+b}, live)
  +live1 = itu.live1(lim, b, l0, live)
  +lts = itu.below(s, t, itu.early(Nat.is_le(s, 0n), live1), small)
  +ltl = itu.lt_le(t, s, lim, lts, LNat.pu.sub_le_self(lim, 1n+b))
  %Equal.sym(Bool, Nat.is_le(lim, t), False{}, LNat.pi.lt_nle(t, lim, ltl)) : {M.over.at(_, lim, t, M.Up{1n+b}) == M.Under{} : M.Over}
  %Equal.sym(Bool, Nat.is_le(s, t), False{}, LNat.pi.lt_nle(t, s, lts)) : {M.over.early(_) == M.Under{} : M.Over}
  {==}

def itu.over(+t: Nat, +v: Nat, +r: M.Z, m: M.Z, live: {M.over(True{}, 0n, 1n+v, r, m) == M.Under{} : M.Over}, small: {Nat.is_le(t, M.target(1n+v, r, m)) == True{} : Bool}) -> {M.over(True{}, t, 1n+v, r, m) == M.Under{} : M.Over}:
  match m:
    case M.Up{c}:
      match c:
        case 0n:
          itu.up0(M.limit_at(1n+v, r), t, live, small)
        case 1n+b:
          itu.up(M.limit_at(1n+v, r), t, b, live, small)
    case M.Down{c}:
      itu.down(M.limit_at(1n+v, r), t, c, live, small)

# The plan
# --------

def itu.gate(-o: M.Over, -c: Maybe<&2, Nat>, -xs: List<&2, Nat>, -base: Nat, -tgt: Nat, eo: {o == M.Under{} : M.Over}) -> {M.gate(o, c, xs, base, tgt) == M.Under{} : M.Over}:
  %Equal.sym(M.Over, o, M.Under{}, eo) : {M.gate(_, c, xs, base, tgt) == M.Under{} : M.Over}
  {==}

def InferThreshold.infer_threshold_target_under(t, v, r, m, keep, full, xs, cuts, live, small):
  +live2 = Equal.trans(M.Over, M.over(True{}, 0n, 1n+v, r, m), InferThreshold.over_spec(True{}, 0n, 1n+v, r, m), M.Under{}, InferThreshold.infer_threshold_over_exact(True{}, 0n, 1n+v, r, m), live)
  +small2 = Equal.trans(Bool, Nat.is_le(t, M.target(1n+v, r, m)), Nat.is_le(t, InferThreshold.target_spec(1n+v, r, m)), True{}, Equal.cong(Nat, Bool, z => Nat.is_le(t, z), M.target(1n+v, r, m), InferThreshold.target_spec(1n+v, r, m), LAThreshold.gt.target(1n+v, r, m)), small)
  +base = Nat.sub(t, M.total(xs))
  itu.gate(M.over(True{}, t, 1n+v, r, m), M.cut(xs, cuts, M.budget(1n+v, r, m, keep, base), full), xs, base, M.target(1n+v, r, m), itu.over(t, v, r, m, live2, small2))
