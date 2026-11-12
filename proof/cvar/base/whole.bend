# eukhe: lemmas of the proofs of the registry, refusal and toggle laws:
# the registry is its input with some declarations left out (wh.reg), a
# declaration list kept whole runs the refusal through it (wh.ref), list
# and Boolean facts.

import Base
import ../../../bend/cvar.bend as Cv
import ../../../laws/cvar/resolution.bend as Cvar
import ../../../laws/cvar/whole.bend as CvarWhole
import ../base.bend as LA
import ./resolve.bend as LR

def wh.eq_comm(a: Nat, b: Nat) -> {Nat.is_eq(a, b) == Nat.is_eq(b, a) : Bool}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      wh.eq_comm(p, q)

def wh.assoc(b: List<&2, Cv.Decl>, +d: Cv.Decl, +rest: List<&2, Cv.Decl>) -> {List.append(&2, Cv.Decl, b, d <> rest) == List.append(&2, Cv.Decl, List.append(&2, Cv.Decl, b, [d]), rest) : List<&2, Cv.Decl>}:
  match b:
    case Nil{}:
      {==}
    case +h <> +t:
      Equal.cong(List<&2, Cv.Decl>, List<&2, Cv.Decl>, z => h <> z, List.append(&2, Cv.Decl, t, d <> rest), List.append(&2, Cv.Decl, List.append(&2, Cv.Decl, t, [d]), rest), wh.assoc(t, d, rest))

def wh.app_nil(b: List<&2, Cv.Decl>) -> {b == List.append(&2, Cv.Decl, b, Nil{}) : List<&2, Cv.Decl>}:
  match b:
    case Nil{}:
      {==}
    case +h <> +t:
      Equal.cong(List<&2, Cv.Decl>, List<&2, Cv.Decl>, z => h <> z, t, List.append(&2, Cv.Decl, t, Nil{}), wh.app_nil(t))

# the model's type test of a declaration is the laws'
def wh.typed(d: Cv.Decl) -> {Cv.Decl.typed(d) == Cvar.spec_good(d) : Bool}:
  match d:
    case Cv.Decl{i, +t, c, p, r, +v}:
      LR.rs.ty_eq(v, t)

# The registry
# ------------

def wh.reg.step(tk: Bool, g: Bool, +K: List<&2, Cv.Decl>, +d: Cv.Decl, +rest: List<&2, Cv.Decl>, r: &keep: List<&2, Bool> -> {List.append(&2, Cv.Decl, Cv.declare.at(tk, g, K, d), CvarWhole.spec_pick(rest, keep)) == Cv.registry.go(rest, Cv.declare.at(tk, g, K, d)) : List<&2, Cv.Decl>}) -> &keep: List<&2, Bool> -> {List.append(&2, Cv.Decl, K, CvarWhole.spec_pick(d <> rest, keep)) == Cv.registry.go(rest, Cv.declare.at(tk, g, K, d)) : List<&2, Cv.Decl>}:
  match tk:
    case True{}:
      (k, e) = r
      (False{} <> k, e)
    case False{}:
      match g:
        case True{}:
          (+k, e) = r
          (True{} <> k, Equal.trans(List<&2, Cv.Decl>, List.append(&2, Cv.Decl, K, d <> CvarWhole.spec_pick(rest, k)), List.append(&2, Cv.Decl, List.append(&2, Cv.Decl, K, [d]), CvarWhole.spec_pick(rest, k)), Cv.registry.go(rest, List.append(&2, Cv.Decl, K, [d])), wh.assoc(K, d, CvarWhole.spec_pick(rest, k)), e))
        case False{}:
          (k, e) = r
          (False{} <> k, e)

# the registry onto K is K, then some declarations of xs in order
def wh.reg(xs: List<&2, Cv.Decl>, +K: List<&2, Cv.Decl>) -> &keep: List<&2, Bool> -> {List.append(&2, Cv.Decl, K, CvarWhole.spec_pick(xs, keep)) == Cv.registry.go(xs, K) : List<&2, Cv.Decl>}:
  match xs:
    case Nil{}:
      (Nil{}, Equal.sym(List<&2, Cv.Decl>, K, List.append(&2, Cv.Decl, K, Nil{}), wh.app_nil(K)))
    case +d <> +rest:
      wh.reg.step(Maybe.is_some(&2, Cv.Decl, Cv.find(K, Cv.Decl.id(d))), Cv.Decl.typed(d), K, d, rest, wh.reg(rest, Cv.declare(K, d)))

def wh.reg_app(a: List<&2, Cv.Decl>, +b: List<&2, Cv.Decl>, +K: List<&2, Cv.Decl>) -> {Cv.registry.go(List.append(&2, Cv.Decl, a, b), K) == Cv.registry.go(b, Cv.registry.go(a, K)) : List<&2, Cv.Decl>}:
  match a:
    case Nil{}:
      {==}
    case +h <> +t:
      wh.reg_app(t, b, Cv.declare(K, h))

def wh.and_t(a: Bool, +b: Bool, ha: {a == True{} : Bool}, hb: {b == True{} : Bool}) -> {Bool.and(a, b) == True{} : Bool}:
  %Equal.sym(Bool, a, True{}, ha) : {Bool.and(_, b) == True{} : Bool}
  hb

def wh.and_assoc(a: Bool, +b: Bool, +c: Bool) -> {Bool.and(a, Bool.and(b, c)) == Bool.and(Bool.and(a, b), c) : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

# no declaration of K ++ [d] has id x: none of K and not d
def wh.no_id_snoc(K: List<&2, Cv.Decl>, +d: Cv.Decl, +x: Nat) -> {Cvar.spec_no_id(List.append(&2, Cv.Decl, K, [d]), x) == Bool.and(Cvar.spec_no_id(K, x), Bool.not(Nat.is_eq(Cvar.spec_id(d), x))) : Bool}:
  match K:
    case Nil{}:
      Equal.sym(Bool, Bool.not(Nat.is_eq(Cvar.spec_id(d), x)), Bool.and(Bool.not(Nat.is_eq(Cvar.spec_id(d), x)), True{}), LR.rs.and_true(Bool.not(Nat.is_eq(Cvar.spec_id(d), x))))
    case +h <> +t:
      %Equal.sym(Bool, Cvar.spec_no_id(List.append(&2, Cv.Decl, t, [d]), x), Bool.and(Cvar.spec_no_id(t, x), Bool.not(Nat.is_eq(Cvar.spec_id(d), x))), wh.no_id_snoc(t, d, x)) : {Bool.and(Bool.not(Nat.is_eq(Cvar.spec_id(h), x)), _) == Bool.and(Bool.and(Bool.not(Nat.is_eq(Cvar.spec_id(h), x)), Cvar.spec_no_id(t, x)), Bool.not(Nat.is_eq(Cvar.spec_id(d), x))) : Bool}
      wh.and_assoc(Bool.not(Nat.is_eq(Cvar.spec_id(h), x)), Cvar.spec_no_id(t, x), Bool.not(Nat.is_eq(Cvar.spec_id(d), x)))


def wh.nand_eq(a: Bool, +g: Bool, eg: {g == True{} : Bool}, h: {Bool.not(Bool.and(a, g)) == True{} : Bool}) -> {Bool.not(a) == True{} : Bool}:
  match a:
    case True{}:
      LA.pv.absurdF({Bool.not(True{}) == True{} : Bool}, Equal.trans(Bool, False{}, Bool.not(g), True{}, Equal.cong(Bool, Bool, b => Bool.not(b), True{}, g, Equal.sym(Bool, g, True{}, eg)), h))
    case False{}:
      {==}

def wh.decl_no_id(tk: Bool, g: Bool, +K: List<&2, Cv.Decl>, +d: Cv.Decl, +x: Nat, eg: {Cvar.spec_good(d) == g : Bool}, +nk: {Cvar.spec_no_id(K, x) == True{} : Bool}, nh: {Bool.not(Bool.and(Nat.is_eq(Cvar.spec_id(d), x), Cvar.spec_good(d))) == True{} : Bool}) -> {Cvar.spec_no_id(Cv.declare.at(tk, g, K, d), x) == True{} : Bool}:
  match tk:
    case True{}:
      nk
    case False{}:
      match g:
        case True{}:
          %Equal.sym(Bool, Cvar.spec_no_id(List.append(&2, Cv.Decl, K, [d]), x), Bool.and(Cvar.spec_no_id(K, x), Bool.not(Nat.is_eq(Cvar.spec_id(d), x))), wh.no_id_snoc(K, d, x)) : {_ == True{} : Bool}
          wh.and_t(Cvar.spec_no_id(K, x), Bool.not(Nat.is_eq(Cvar.spec_id(d), x)), nk, wh.nand_eq(Nat.is_eq(Cvar.spec_id(d), x), Cvar.spec_good(d), eg, nh))
        case False{}:
          nk

# no declaration the registry keeps onto K has id x, when K has none and
# xs has no good one
def wh.reg_no_id(xs: List<&2, Cv.Decl>, +K: List<&2, Cv.Decl>, +x: Nat, +nk: {Cvar.spec_no_id(K, x) == True{} : Bool}, +ng: {CvarWhole.spec_no_good_id(xs, x) == True{} : Bool}) -> {Cvar.spec_no_id(Cv.registry.go(xs, K), x) == True{} : Bool}:
  match xs:
    case Nil{}:
      nk
    case +d <> +rest:
      +nh = LA.cvar.pv.and_l(Bool.not(Bool.and(Nat.is_eq(Cvar.spec_id(d), x), Cvar.spec_good(d))), CvarWhole.spec_no_good_id(rest, x), ng)
      +nr = LA.cvar.pv.and_r(Bool.not(Bool.and(Nat.is_eq(Cvar.spec_id(d), x), Cvar.spec_good(d))), CvarWhole.spec_no_good_id(rest, x), ng)
      wh.reg_no_id(rest, Cv.declare(K, d), x, wh.decl_no_id(Maybe.is_some(&2, Cv.Decl, Cv.find(K, Cv.Decl.id(d))), Cv.Decl.typed(d), K, d, x, Equal.sym(Bool, Cv.Decl.typed(d), Cvar.spec_good(d), wh.typed(d)), nk, nh), nr)

def wh.declare_add(tk: Bool, g: Bool, +K: List<&2, Cv.Decl>, +d: Cv.Decl, et: {tk == False{} : Bool}, eg: {g == True{} : Bool}) -> {Cv.declare.at(tk, g, K, d) == List.append(&2, Cv.Decl, K, [d]) : List<&2, Cv.Decl>}:
  match tk:
    case True{}:
      LA.pv.absurdF({K == List.append(&2, Cv.Decl, K, [d]) : List<&2, Cv.Decl>}, Equal.sym(Bool, True{}, False{}, et))
    case False{}:
      match g:
        case True{}:
          {==}
        case False{}:
          LA.pv.absurdF({K == List.append(&2, Cv.Decl, K, [d]) : List<&2, Cv.Decl>}, eg)

# an id no declaration of K has is free: declare adds a good declaration
def wh.declare_free(+K: List<&2, Cv.Decl>, +d: Cv.Decl, nk: {Cvar.spec_no_id(K, Cvar.spec_id(d)) == True{} : Bool}, good: {Cvar.spec_good(d) == True{} : Bool}) -> {Cv.declare(K, d) == List.append(&2, Cv.Decl, K, [d]) : List<&2, Cv.Decl>}:
  +x = Cvar.spec_id(d)
  +et = Equal.trans(Bool, Maybe.is_some(&2, Cv.Decl, Cv.find(K, Cv.Decl.id(d))), Maybe.is_some(&2, Cv.Decl, Cv.find(K, x)), False{},
    Equal.cong(Nat, Bool, y => Maybe.is_some(&2, Cv.Decl, Cv.find(K, y)), Cv.Decl.id(d), x, LR.rs.decl_id(d)),
    Equal.trans(Bool, Maybe.is_some(&2, Cv.Decl, Cv.find(K, x)), Bool.not(Cvar.spec_no_id(K, x)), False{}, LR.rs.some_no_id(K, x), Equal.cong(Bool, Bool, b => Bool.not(b), Cvar.spec_no_id(K, x), True{}, nk)))
  wh.declare_add(Maybe.is_some(&2, Cv.Decl, Cv.find(K, Cv.Decl.id(d))), Cv.Decl.typed(d), K, d, et, Equal.trans(Bool, Cv.Decl.typed(d), Cvar.spec_good(d), True{}, wh.typed(d), good))

def wh.kf_fin(+R: List<&2, Cv.Decl>, +d: Cv.Decl, +post: List<&2, Cv.Decl>, +x: Nat, ed: {Cvar.spec_id(d) == x : Nat}, nr: {Cvar.spec_no_id(R, x) == True{} : Bool}, r: &keep: List<&2, Bool> -> {List.append(&2, Cv.Decl, List.append(&2, Cv.Decl, R, [d]), CvarWhole.spec_pick(post, keep)) == Cv.registry.go(post, List.append(&2, Cv.Decl, R, [d])) : List<&2, Cv.Decl>}) -> {Cv.find(Cv.registry.go(post, List.append(&2, Cv.Decl, R, [d])), x) == Some{d} : Maybe<&2, Cv.Decl>}:
  (+k, e) = r
  +S = CvarWhole.spec_pick(post, k)
  Equal.trans(Maybe<&2, Cv.Decl>, Cv.find(Cv.registry.go(post, List.append(&2, Cv.Decl, R, [d])), x), Cv.find(List.append(&2, Cv.Decl, List.append(&2, Cv.Decl, R, [d]), S), x), Some{d},
    Equal.cong(List<&2, Cv.Decl>, Maybe<&2, Cv.Decl>, z => Cv.find(z, x), Cv.registry.go(post, List.append(&2, Cv.Decl, R, [d])), List.append(&2, Cv.Decl, List.append(&2, Cv.Decl, R, [d]), S), Equal.sym(List<&2, Cv.Decl>, List.append(&2, Cv.Decl, List.append(&2, Cv.Decl, R, [d]), S), Cv.registry.go(post, List.append(&2, Cv.Decl, R, [d])), e)),
    Equal.trans(Maybe<&2, Cv.Decl>, Cv.find(List.append(&2, Cv.Decl, List.append(&2, Cv.Decl, R, [d]), S), x), Cv.find(List.append(&2, Cv.Decl, R, d <> S), x), Some{d},
      Equal.cong(List<&2, Cv.Decl>, Maybe<&2, Cv.Decl>, z => Cv.find(z, x), List.append(&2, Cv.Decl, List.append(&2, Cv.Decl, R, [d]), S), List.append(&2, Cv.Decl, R, d <> S), Equal.sym(List<&2, Cv.Decl>, List.append(&2, Cv.Decl, R, d <> S), List.append(&2, Cv.Decl, List.append(&2, Cv.Decl, R, [d]), S), wh.assoc(R, d, S))),
      LR.rs.find_first(R, x, d, S, ed, nr)))

# The refusal
# -----------

# no declaration of xs has an id of K
def wh.fresh(+K: List<&2, Cv.Decl>, xs: List<&2, Cv.Decl>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case e <> rest:
      Bool.and(Cvar.spec_no_id(K, Cvar.spec_id(e)), wh.fresh(K, rest))

def wh.fresh_nil(xs: List<&2, Cv.Decl>) -> {wh.fresh(Nil{}, xs) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case e <> rest:
      wh.fresh_nil(rest)

def wh.not_eq_comm(+a: Nat, +b: Nat, h: {Bool.not(Nat.is_eq(a, b)) == True{} : Bool}) -> {Bool.not(Nat.is_eq(b, a)) == True{} : Bool}:
  %wh.eq_comm(a, b) : {Bool.not(_) == True{} : Bool}
  h

def wh.fresh_snoc(+K: List<&2, Cv.Decl>, +d: Cv.Decl, xs: List<&2, Cv.Decl>, +fr: {wh.fresh(K, xs) == True{} : Bool}, +nd: {Cvar.spec_no_id(xs, Cvar.spec_id(d)) == True{} : Bool}) -> {wh.fresh(List.append(&2, Cv.Decl, K, [d]), xs) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case +e <> +rest:
      +ie = Cvar.spec_id(e)
      +id = Cvar.spec_id(d)
      +f1 = LA.cvar.pv.and_l(Cvar.spec_no_id(K, ie), wh.fresh(K, rest), fr)
      +f2 = LA.cvar.pv.and_r(Cvar.spec_no_id(K, ie), wh.fresh(K, rest), fr)
      +n1 = LA.cvar.pv.and_l(Bool.not(Nat.is_eq(ie, id)), Cvar.spec_no_id(rest, id), nd)
      +n2 = LA.cvar.pv.and_r(Bool.not(Nat.is_eq(ie, id)), Cvar.spec_no_id(rest, id), nd)
      %Equal.sym(Bool, Cvar.spec_no_id(List.append(&2, Cv.Decl, K, [d]), ie), Bool.and(Cvar.spec_no_id(K, ie), Bool.not(Nat.is_eq(id, ie))), wh.no_id_snoc(K, d, ie)) : {Bool.and(_, wh.fresh(List.append(&2, Cv.Decl, K, [d]), rest)) == True{} : Bool}
      wh.and_t(Bool.and(Cvar.spec_no_id(K, ie), Bool.not(Nat.is_eq(id, ie))), wh.fresh(List.append(&2, Cv.Decl, K, [d]), rest), wh.and_t(Cvar.spec_no_id(K, ie), Bool.not(Nat.is_eq(id, ie)), f1, wh.not_eq_comm(ie, id, n1)), wh.fresh_snoc(K, d, rest, f2, n2))

# a declaration list kept whole, its ids not in K: the refusal passes it,
# keeping it after K
def wh.ref(pre: List<&2, Cv.Decl>, +K: List<&2, Cv.Decl>, +rest: List<&2, Cv.Decl>, +whole: {CvarWhole.spec_whole(pre) == True{} : Bool}, +fr: {wh.fresh(K, pre) == True{} : Bool}) -> {Cv.refusal.go(List.append(&2, Cv.Decl, pre, rest), K, Cv.taken.at(List.append(&2, Cv.Decl, pre, rest), K), Cv.typed.first(List.append(&2, Cv.Decl, pre, rest))) == Cv.refusal.go(rest, List.append(&2, Cv.Decl, K, pre), Cv.taken.at(rest, List.append(&2, Cv.Decl, K, pre)), Cv.typed.first(rest)) : Cv.Refusal}:
  match pre:
    case Nil{}:
      %wh.app_nil(K) : {Cv.refusal.go(rest, K, Cv.taken.at(rest, K), Cv.typed.first(rest)) == Cv.refusal.go(rest, _, Cv.taken.at(rest, _), Cv.typed.first(rest)) : Cv.Refusal}
      {==}
    case +d <> +p:
      +x = Cvar.spec_id(d)
      +g1 = LA.cvar.pv.and_l(Cvar.spec_good(d), Bool.and(Cvar.spec_no_id(p, x), CvarWhole.spec_whole(p)), whole)
      +g2 = LA.cvar.pv.and_r(Cvar.spec_good(d), Bool.and(Cvar.spec_no_id(p, x), CvarWhole.spec_whole(p)), whole)
      +nd = LA.cvar.pv.and_l(Cvar.spec_no_id(p, x), CvarWhole.spec_whole(p), g2)
      +wp = LA.cvar.pv.and_r(Cvar.spec_no_id(p, x), CvarWhole.spec_whole(p), g2)
      +f1 = LA.cvar.pv.and_l(Cvar.spec_no_id(K, x), wh.fresh(K, p), fr)
      +f2 = LA.cvar.pv.and_r(Cvar.spec_no_id(K, x), wh.fresh(K, p), fr)
      +et = Equal.trans(Bool, Maybe.is_some(&2, Cv.Decl, Cv.find(K, Cv.Decl.id(d))), Maybe.is_some(&2, Cv.Decl, Cv.find(K, x)), False{},
        Equal.cong(Nat, Bool, y => Maybe.is_some(&2, Cv.Decl, Cv.find(K, y)), Cv.Decl.id(d), x, LR.rs.decl_id(d)),
        Equal.trans(Bool, Maybe.is_some(&2, Cv.Decl, Cv.find(K, x)), Bool.not(Cvar.spec_no_id(K, x)), False{}, LR.rs.some_no_id(K, x), Equal.cong(Bool, Bool, b => Bool.not(b), Cvar.spec_no_id(K, x), True{}, f1)))
      +eg = Equal.trans(Bool, Cv.Decl.typed(d), Cvar.spec_good(d), True{}, wh.typed(d), g1)
      %Equal.sym(Bool, Maybe.is_some(&2, Cv.Decl, Cv.find(K, Cv.Decl.id(d))), False{}, et) : {Cv.refusal.go(d <> List.append(&2, Cv.Decl, p, rest), K, _, Cv.Decl.typed(d)) == Cv.refusal.go(rest, List.append(&2, Cv.Decl, K, d <> p), Cv.taken.at(rest, List.append(&2, Cv.Decl, K, d <> p)), Cv.typed.first(rest)) : Cv.Refusal}
      %Equal.sym(Bool, Cv.Decl.typed(d), True{}, eg) : {Cv.refusal.go(d <> List.append(&2, Cv.Decl, p, rest), K, False{}, _) == Cv.refusal.go(rest, List.append(&2, Cv.Decl, K, d <> p), Cv.taken.at(rest, List.append(&2, Cv.Decl, K, d <> p)), Cv.typed.first(rest)) : Cv.Refusal}
      %Equal.sym(List<&2, Cv.Decl>, List.append(&2, Cv.Decl, K, d <> p), List.append(&2, Cv.Decl, List.append(&2, Cv.Decl, K, [d]), p), wh.assoc(K, d, p)) : {Cv.refusal.go(d <> List.append(&2, Cv.Decl, p, rest), K, False{}, True{}) == Cv.refusal.go(rest, _, Cv.taken.at(rest, _), Cv.typed.first(rest)) : Cv.Refusal}
      wh.ref(p, List.append(&2, Cv.Decl, K, [d]), rest, wp, wh.fresh_snoc(K, d, p, f2, nd))

def wh.reason(n: Bool, g: Bool, +i: Nat, +t: Cv.Ty, +c: Cv.Scope, +q: Bool, +r: Bool, +v: Cv.Val, +post: List<&2, Cv.Decl>, +pre: List<&2, Cv.Decl>, drop: {Bool.and(n, g) == False{} : Bool}) -> {Cv.refusal.go(Cv.Decl{i, t, c, q, r, v} <> post, pre, Bool.not(n), g) == CvarWhole.spec_reason(n, i) : Cv.Refusal}:
  match n:
    case True{}:
      match g:
        case True{}:
          LA.pv.absurdF({Cv.refusal.go(Cv.Decl{i, t, c, q, r, v} <> post, pre, False{}, True{}) == Cv.BadInit{i} : Cv.Refusal}, Equal.sym(Bool, True{}, False{}, drop))
        case False{}:
          {==}
    case False{}:
      {==}
