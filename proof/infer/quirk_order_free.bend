# eukhe: the proof of LAW quirk_order_free

import Base
import ../../bend/infer.bend as If
import ../../laws/infer.bend as Infer
import ../base/bool/and.bend as LBoolAnd
import ../base/bool/misc.bend as LBoolMisc
import ../base/nat/is_eq.bend as LNatIsEq
import ./base.bend as LA

def pq.lt_irrefl(k: Nat) -> {Nat.is_lt(k, k) == False{} : Bool}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      pq.lt_irrefl(p)

def pq.lt_trans(a: Nat, b: Nat, c: Nat, ab: {Nat.is_lt(a, b) == True{} : Bool}, bc: {Nat.is_lt(b, c) == True{} : Bool}) -> {Nat.is_lt(a, c) == True{} : Bool}:
  match a b c:
    case _ 0n _:
      LBoolMisc.pq.absurdF({Nat.is_lt(a, c) == True{} : Bool}, ab)
    case _ 1n+q 0n:
      LBoolMisc.pq.absurdF({Nat.is_lt(a, 0n) == True{} : Bool}, bc)
    case 0n 1n+q 1n+r:
      {==}
    case 1n+p 1n+q 1n+r:
      pq.lt_trans(p, q, r, ab, bc)

# k below x and not below y: x is not below y
def pq.lt_gap(+k: Nat, +x: Nat, +y: Nat, c: Bool, ec: {Nat.is_lt(x, y) == c : Bool}, kx: {Nat.is_lt(k, x) == True{} : Bool}, ky: {Nat.is_lt(k, y) == False{} : Bool}) -> {Nat.is_lt(x, y) == False{} : Bool}:
  match c:
    case True{}:
      LA.pq.flip({Nat.is_lt(x, y) == False{} : Bool}, Nat.is_lt(k, y), pq.lt_trans(k, x, y, kx, ec), ky)
    case False{}:
      ec

# the best of a then b is the best of b then a, from None
def pq.pair_swap(+a: If.Rule, +b: If.Rule, +q: If.Query, +d: Nat, c1: Bool, +e1: {Nat.is_lt(If.Rule.rank(b), If.Rule.rank(a)) == c1 : Bool}, c2: Bool, +e2: {Nat.is_lt(If.Rule.rank(a), If.Rule.rank(b)) == c2 : Bool}, nc: {If.clash(a, b) == False{} : Bool}, ha: {Bool.and(If.applies(q, a), Nat.is_eq(If.Rule.dir(a), d)) == True{} : Bool}, hb: {Bool.and(If.applies(q, b), Nat.is_eq(If.Rule.dir(b), d)) == True{} : Bool}) -> {If.better.at(c1, If.Best{If.Rule.rank(b), If.Rule.val(b)}, a) == If.better.at(c2, If.Best{If.Rule.rank(a), If.Rule.val(a)}, b) : Maybe<&2, If.Best>}:
  match c1 c2:
    case True{} True{}:
      +RA = If.Rule.rank(a)
      +RB = If.Rule.rank(b)
      LA.pq.flip({If.better.at(True{}, If.Best{RB, If.Rule.val(b)}, a) == If.better.at(True{}, If.Best{RA, If.Rule.val(a)}, b) : Maybe<&2, If.Best>}, Nat.is_lt(RA, RA), pq.lt_trans(RA, RB, RA, e2, e1), pq.lt_irrefl(RA))
    case True{} False{}:
      {==}
    case False{} True{}:
      {==}
    case False{} False{}:
      +RA = If.Rule.rank(a)
      +RB = If.Rule.rank(b)
      +VA = If.Rule.val(a)
      +VB = If.Rule.val(b)
      +er = LA.pq.tri(RA, RB, e1, e2)
      +ev = LA.pq.same_val(q, a, b, d, nc, ha, hb, er)
      +ek = LNatIsEq.pq.eq_true(RA, RB, er)
      %ek : {Some{If.Best{_, VB}} == Some{If.Best{RA, VA}} : Maybe<&2, If.Best>}
      %ev : {Some{If.Best{RA, _}} == Some{If.Best{RA, VA}} : Maybe<&2, If.Best>}
      {==}

# the same, from Some{Best{k, v}}
def pq.some_swap(+k: Nat, +v: Nat, +a: If.Rule, +b: If.Rule, +q: If.Query, +d: Nat, ca: Bool, +ea: {Nat.is_lt(k, If.Rule.rank(a)) == ca : Bool}, cb: Bool, +eb: {Nat.is_lt(k, If.Rule.rank(b)) == cb : Bool}, nc: {If.clash(a, b) == False{} : Bool}, ha: {Bool.and(If.applies(q, a), Nat.is_eq(If.Rule.dir(a), d)) == True{} : Bool}, hb: {Bool.and(If.applies(q, b), Nat.is_eq(If.Rule.dir(b), d)) == True{} : Bool}) -> {If.better(If.better.at(cb, If.Best{k, v}, b), a) == If.better(If.better.at(ca, If.Best{k, v}, a), b) : Maybe<&2, If.Best>}:
  match ca cb:
    case True{} True{}:
      +RA = If.Rule.rank(a)
      +RB = If.Rule.rank(b)
      pq.pair_swap(a, b, q, d, Nat.is_lt(RB, RA), {==}, Nat.is_lt(RA, RB), {==}, nc, ha, hb)
    case True{} False{}:
      +RA = If.Rule.rank(a)
      +RB = If.Rule.rank(b)
      +VA = If.Rule.val(a)
      %Equal.sym(Bool, Nat.is_lt(k, RA), True{}, ea) : {If.better.at(_, If.Best{k, v}, a) == If.better.at(Nat.is_lt(RA, RB), If.Best{RA, VA}, b) : Maybe<&2, If.Best>}
      %Equal.sym(Bool, Nat.is_lt(RA, RB), False{}, pq.lt_gap(k, RA, RB, Nat.is_lt(RA, RB), {==}, ea, eb)) : {If.better.at(True{}, If.Best{k, v}, a) == If.better.at(_, If.Best{RA, VA}, b) : Maybe<&2, If.Best>}
      {==}
    case False{} True{}:
      +RA = If.Rule.rank(a)
      +RB = If.Rule.rank(b)
      +VB = If.Rule.val(b)
      %Equal.sym(Bool, Nat.is_lt(RB, RA), False{}, pq.lt_gap(k, RB, RA, Nat.is_lt(RB, RA), {==}, eb, ea)) : {If.better.at(_, If.Best{RB, VB}, a) == If.better.at(Nat.is_lt(k, RB), If.Best{k, v}, b) : Maybe<&2, If.Best>}
      %Equal.sym(Bool, Nat.is_lt(k, RB), True{}, eb) : {If.better.at(False{}, If.Best{RB, VB}, a) == If.better.at(_, If.Best{k, v}, b) : Maybe<&2, If.Best>}
      {==}
    case False{} False{}:
      +RA = If.Rule.rank(a)
      +RB = If.Rule.rank(b)
      %Equal.sym(Bool, Nat.is_lt(k, RA), False{}, ea) : {If.better.at(_, If.Best{k, v}, a) == If.better.at(Nat.is_lt(k, RB), If.Best{k, v}, b) : Maybe<&2, If.Best>}
      %Equal.sym(Bool, Nat.is_lt(k, RB), False{}, eb) : {If.better.at(False{}, If.Best{k, v}, a) == If.better.at(_, If.Best{k, v}, b) : Maybe<&2, If.Best>}
      {==}

# two rules that apply and do not clash give one best in either order
def pq.better_swap(s: Maybe<&2, If.Best>, +a: If.Rule, +b: If.Rule, +q: If.Query, +d: Nat, nc: {If.clash(a, b) == False{} : Bool}, ha: {Bool.and(If.applies(q, a), Nat.is_eq(If.Rule.dir(a), d)) == True{} : Bool}, hb: {Bool.and(If.applies(q, b), Nat.is_eq(If.Rule.dir(b), d)) == True{} : Bool}) -> {If.better(If.better(s, b), a) == If.better(If.better(s, a), b) : Maybe<&2, If.Best>}:
  match s:
    case None{}:
      +RA = If.Rule.rank(a)
      +RB = If.Rule.rank(b)
      pq.pair_swap(a, b, q, d, Nat.is_lt(RB, RA), {==}, Nat.is_lt(RA, RB), {==}, nc, ha, hb)
    case Some{x}:
      match x:
        case If.Best{+k, +v}:
          pq.some_swap(k, v, a, b, q, d, Nat.is_lt(k, If.Rule.rank(a)), {==}, Nat.is_lt(k, If.Rule.rank(b)), {==}, nc, ha, hb)

def pq.swap_go(pre: List<&2, If.Rule>, +a: If.Rule, +b: If.Rule, +post: List<&2, If.Rule>, +q: If.Query, +d: Nat, +s: Maybe<&2, If.Best>, h1: Bool, h2: Bool, +e1: {If.use.at(List.append(&2, If.Rule, pre, b <> a <> post), q, d) == h1 : Bool}, +e2: {If.use.at(List.append(&2, If.Rule, pre, a <> b <> post), q, d) == h2 : Bool}, +nc: {If.clash(a, b) == False{} : Bool}) -> {If.look.go(List.append(&2, If.Rule, pre, b <> a <> post), q, d, s, h1) == If.look.go(List.append(&2, If.Rule, pre, a <> b <> post), q, d, s, h2) : Maybe<&2, If.Best>}:
  match pre:
    case Nil{}:
      match h1 h2:
        case True{} True{}:
          +Ha = Bool.and(If.applies(q, a), Nat.is_eq(If.Rule.dir(a), d))
          +Hb = Bool.and(If.applies(q, b), Nat.is_eq(If.Rule.dir(b), d))
          +U = If.use.at(post, q, d)
          %Equal.sym(Bool, Ha, True{}, e2) : {If.look.go(a <> post, q, d, If.better(s, b), _) == If.look.go(b <> post, q, d, If.better(s, a), Hb) : Maybe<&2, If.Best>}
          %Equal.sym(Bool, Hb, True{}, e1) : {If.look.go(a <> post, q, d, If.better(s, b), True{}) == If.look.go(b <> post, q, d, If.better(s, a), _) : Maybe<&2, If.Best>}
          %pq.better_swap(s, a, b, q, d, nc, e2, e1) : {If.look.go(post, q, d, If.better(If.better(s, b), a), U) == If.look.go(post, q, d, _, U) : Maybe<&2, If.Best>}
          {==}
        case True{} False{}:
          +Ha = Bool.and(If.applies(q, a), Nat.is_eq(If.Rule.dir(a), d))
          +Hb = Bool.and(If.applies(q, b), Nat.is_eq(If.Rule.dir(b), d))
          %Equal.sym(Bool, Ha, False{}, e2) : {If.look.go(a <> post, q, d, If.better(s, b), _) == If.look.go(b <> post, q, d, s, Hb) : Maybe<&2, If.Best>}
          %Equal.sym(Bool, Hb, True{}, e1) : {If.look.go(a <> post, q, d, If.better(s, b), False{}) == If.look.go(b <> post, q, d, s, _) : Maybe<&2, If.Best>}
          {==}
        case False{} True{}:
          +Ha = Bool.and(If.applies(q, a), Nat.is_eq(If.Rule.dir(a), d))
          +Hb = Bool.and(If.applies(q, b), Nat.is_eq(If.Rule.dir(b), d))
          %Equal.sym(Bool, Ha, True{}, e2) : {If.look.go(a <> post, q, d, s, _) == If.look.go(b <> post, q, d, If.better(s, a), Hb) : Maybe<&2, If.Best>}
          %Equal.sym(Bool, Hb, False{}, e1) : {If.look.go(a <> post, q, d, s, True{}) == If.look.go(b <> post, q, d, If.better(s, a), _) : Maybe<&2, If.Best>}
          {==}
        case False{} False{}:
          +Ha = Bool.and(If.applies(q, a), Nat.is_eq(If.Rule.dir(a), d))
          +Hb = Bool.and(If.applies(q, b), Nat.is_eq(If.Rule.dir(b), d))
          %Equal.sym(Bool, Ha, False{}, e2) : {If.look.go(a <> post, q, d, s, _) == If.look.go(b <> post, q, d, s, Hb) : Maybe<&2, If.Best>}
          %Equal.sym(Bool, Hb, False{}, e1) : {If.look.go(a <> post, q, d, s, False{}) == If.look.go(b <> post, q, d, s, _) : Maybe<&2, If.Best>}
          {==}
    case +h <> +t:
      match h1 h2:
        case True{} True{}:
          pq.swap_go(t, a, b, post, q, d, If.better(s, h), If.use.at(List.append(&2, If.Rule, t, b <> a <> post), q, d), If.use.at(List.append(&2, If.Rule, t, a <> b <> post), q, d), {==}, {==}, nc)
        case False{} False{}:
          pq.swap_go(t, a, b, post, q, d, s, If.use.at(List.append(&2, If.Rule, t, b <> a <> post), q, d), If.use.at(List.append(&2, If.Rule, t, a <> b <> post), q, d), {==}, {==}, nc)
        case True{} False{}:
          +X1 = List.append(&2, If.Rule, t, b <> a <> post)
          +X2 = List.append(&2, If.Rule, t, a <> b <> post)
          LA.pq.flip({If.look.go(h <> X1, q, d, s, True{}) == If.look.go(h <> X2, q, d, s, False{}) : Maybe<&2, If.Best>}, Bool.and(If.applies(q, h), Nat.is_eq(If.Rule.dir(h), d)), e1, e2)
        case False{} True{}:
          +X1 = List.append(&2, If.Rule, t, b <> a <> post)
          +X2 = List.append(&2, If.Rule, t, a <> b <> post)
          LA.pq.flip({If.look.go(h <> X1, q, d, s, False{}) == If.look.go(h <> X2, q, d, s, True{}) : Maybe<&2, If.Best>}, Bool.and(If.applies(q, h), Nat.is_eq(If.Rule.dir(h), d)), e2, e1)

def pq.amb_tail(pre: List<&2, If.Rule>, +X: List<&2, If.Rule>, h: {If.ambiguous(List.append(&2, If.Rule, pre, X)) == False{} : Bool}) -> {If.ambiguous(X) == False{} : Bool}:
  match pre:
    case Nil{}:
      h
    case +s <> +t:
      +Y = List.append(&2, If.Rule, t, X)
      pq.amb_tail(t, X, LA.pq.or_r(If.clashes(s, Y), If.ambiguous(Y), h))

def pq.quirk_order_free(+known: List<&2, Nat>, +pre: List<&2, If.Rule>, +a: If.Rule, +b: If.Rule, +post: List<&2, If.Rule>, +q: If.Query, +d: Nat, ok: {If.compiles(known, List.append(&2, If.Rule, pre, a <> b <> post)) == True{} : Bool}) -> {If.lookup(List.append(&2, If.Rule, pre, b <> a <> post), q, d) == If.lookup(List.append(&2, If.Rule, pre, a <> b <> post), q, d) : If.Ans}:
  +L1 = List.append(&2, If.Rule, pre, b <> a <> post)
  +L2 = List.append(&2, If.Rule, pre, a <> b <> post)
  +am = LA.pq.not_f(If.ambiguous(L2), LBoolAnd.pq.and_r(If.known_all(L2, known), Bool.not(If.ambiguous(L2)), ok))
  +ab = pq.amb_tail(pre, a <> b <> post, am)
  +nc = LA.pq.or_l(If.clash(a, b), If.clashes(a, post), LA.pq.or_l(Bool.or(If.clash(a, b), If.clashes(a, post)), If.ambiguous(b <> post), ab))
  +sw = pq.swap_go(pre, a, b, post, q, d, None{}, If.use.at(L1, q, d), If.use.at(L2, q, d), {==}, {==}, nc)
  Equal.cong(Maybe<&2, If.Best>, If.Ans, m => If.ans(m), If.look.go(L1, q, d, None{}, If.use.at(L1, q, d)), If.look.go(L2, q, d, None{}, If.use.at(L2, q, d)), sw)

def Infer.quirk_order_free(known, pre, a, b, post, q, d, ok):
  pq.quirk_order_free(known, pre, a, b, post, q, d, ok)
