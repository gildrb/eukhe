# eukhe: lemmas the proofs of two or more areas share: tree

import Base
import ../../bend/tree.bend as Tr
import ./bool/and.bend as LBoolAnd
import ./bool/misc.bend as LBoolMisc
import ./list.bend as LList
import ./nat/is_eq.bend as LNatIsEq
import ./nat/is_lt.bend as LNatIsLt
import ./nat/misc.bend as LNatMisc
import ./pair.bend as LPair

def tc.bst_l(+mid: Nat, +mp: Nat, +l: Tr.KMap, +r: Tr.KMap, +h: {LBoolMisc.tc.bst(Tr.KFork{mid, mp, l, r}) == True{} : Bool}) -> {LBoolMisc.tc.bst(l) == True{} : Bool}:
  LBoolAnd.tree.pt.and_l(LBoolMisc.tc.bst(l), Bool.and(LBoolMisc.tc.bst(r), Bool.and(LBoolMisc.tc.lt(Tr.KMap.read(l), mid), LBoolMisc.tc.ge(Tr.KMap.read(r), mid))), h)

def tc.bst_r(+mid: Nat, +mp: Nat, +l: Tr.KMap, +r: Tr.KMap, +h: {LBoolMisc.tc.bst(Tr.KFork{mid, mp, l, r}) == True{} : Bool}) -> {LBoolMisc.tc.bst(r) == True{} : Bool}:
  LBoolAnd.tree.pt.and_l(LBoolMisc.tc.bst(r), Bool.and(LBoolMisc.tc.lt(Tr.KMap.read(l), mid), LBoolMisc.tc.ge(Tr.KMap.read(r), mid)), LBoolAnd.tc.bst_rest(mid, mp, l, r, h))

def tc.bst_lt(+mid: Nat, +mp: Nat, +l: Tr.KMap, +r: Tr.KMap, +h: {LBoolMisc.tc.bst(Tr.KFork{mid, mp, l, r}) == True{} : Bool}) -> {LBoolMisc.tc.lt(Tr.KMap.read(l), mid) == True{} : Bool}:
  +h2 = LBoolAnd.tree.pt.and_r(LBoolMisc.tc.bst(r), Bool.and(LBoolMisc.tc.lt(Tr.KMap.read(l), mid), LBoolMisc.tc.ge(Tr.KMap.read(r), mid)), LBoolAnd.tc.bst_rest(mid, mp, l, r, h))
  LBoolAnd.tree.pt.and_l(LBoolMisc.tc.lt(Tr.KMap.read(l), mid), LBoolMisc.tc.ge(Tr.KMap.read(r), mid), h2)

def tc.bst_ge(+mid: Nat, +mp: Nat, +l: Tr.KMap, +r: Tr.KMap, +h: {LBoolMisc.tc.bst(Tr.KFork{mid, mp, l, r}) == True{} : Bool}) -> {LBoolMisc.tc.ge(Tr.KMap.read(r), mid) == True{} : Bool}:
  +h2 = LBoolAnd.tree.pt.and_r(LBoolMisc.tc.bst(r), Bool.and(LBoolMisc.tc.lt(Tr.KMap.read(l), mid), LBoolMisc.tc.ge(Tr.KMap.read(r), mid)), LBoolAnd.tc.bst_rest(mid, mp, l, r, h))
  LBoolAnd.tree.pt.and_r(LBoolMisc.tc.lt(Tr.KMap.read(l), mid), LBoolMisc.tc.ge(Tr.KMap.read(r), mid), h2)

def tc.bst_fork(+mid: Nat, +l: Tr.KMap, +r: Tr.KMap, +bl: {LBoolMisc.tc.bst(l) == True{} : Bool}, +br: {LBoolMisc.tc.bst(r) == True{} : Bool}, +ll: {LBoolMisc.tc.lt(Tr.KMap.read(l), mid) == True{} : Bool}, +gr: {LBoolMisc.tc.ge(Tr.KMap.read(r), mid) == True{} : Bool}) -> {LBoolMisc.tc.bst(Tr.KMap.fork(mid, l, r)) == True{} : Bool}:
  LBoolAnd.tree.pt.and_t(LBoolMisc.tc.bst(l), Bool.and(LBoolMisc.tc.bst(r), Bool.and(LBoolMisc.tc.lt(Tr.KMap.read(l), mid), LBoolMisc.tc.ge(Tr.KMap.read(r), mid))), bl, LBoolAnd.tree.pt.and_t(LBoolMisc.tc.bst(r), Bool.and(LBoolMisc.tc.lt(Tr.KMap.read(l), mid), LBoolMisc.tc.ge(Tr.KMap.read(r), mid)), br, LBoolAnd.tree.pt.and_t(LBoolMisc.tc.lt(Tr.KMap.read(l), mid), LBoolMisc.tc.ge(Tr.KMap.read(r), mid), ll, gr)))

# the first key test of a list before a list above the key
def tc.first_app(A: List<&2, Tr.Ent>, +B: List<&2, Tr.Ent>, +b: Nat, +e: Tr.Ent, +gb: {LBoolMisc.tc.ge(B, b) == True{} : Bool}, +eb: {Nat.is_lt(Tr.Ent.k(e), b) == True{} : Bool}) -> {Tr.first(Tr.Ent.k(e), List.append(&2, Tr.Ent, A, B)) == Tr.first(Tr.Ent.k(e), A) : Cmp}:
  match A:
    case Nil{}:
      match B:
        case Nil{}:
          {==}
        case +f <> s:
          LNatMisc.tc.cmp_lt(Tr.Ent.k(e), Tr.Ent.k(f), LNatIsLt.tc.lt_le(Tr.Ent.k(e), b, Tr.Ent.k(f), eb, LNatIsLt.tc.ge_head(f, s, b, gb)))
    case a <> r:
      {==}

def tc.set_go_lt(B: List<&2, Tr.Ent>, +e: Tr.Ent) -> {Tr.set.go(B, e, LT{}) == e <> B : List<&2, Tr.Ent>}:
  match B:
    case Nil{}:
      {==}
    case f <> s:
      {==}

def tc.set_go_app_l(A: List<&2, Tr.Ent>, +B: List<&2, Tr.Ent>, +b: Nat, +e: Tr.Ent, c: Cmp, +ec: {Tr.first(Tr.Ent.k(e), A) == c : Cmp}, +gb: {LBoolMisc.tc.ge(B, b) == True{} : Bool}, +eb: {Nat.is_lt(Tr.Ent.k(e), b) == True{} : Bool}) -> {Tr.set.go(List.append(&2, Tr.Ent, A, B), e, c) == List.append(&2, Tr.Ent, Tr.set.go(A, e, c), B) : List<&2, Tr.Ent>}:
  match A:
    case Nil{}:
      %ec : {Tr.set.go(B, e, _) == List.append(&2, Tr.Ent, Tr.set.go(Nil{}, e, _), B) : List<&2, Tr.Ent>}
      tc.set_go_lt(B, e)
    case +a <> +r:
      match c:
        case LT{}:
          {==}
        case EQ{}:
          {==}
        case GT{}:
          +R = List.append(&2, Tr.Ent, r, B)
          %Equal.sym(Cmp, Tr.first(Tr.Ent.k(e), List.append(&2, Tr.Ent, r, B)), Tr.first(Tr.Ent.k(e), r), tc.first_app(r, B, b, e, gb, eb)) : {a <> Tr.set.go(R, e, _) == List.append(&2, Tr.Ent, a <> Tr.set.go(r, e, Tr.first(Tr.Ent.k(e), r)), B) : List<&2, Tr.Ent>}
          Equal.cong(List<&2, Tr.Ent>, List<&2, Tr.Ent>, ys => a <> ys, Tr.set.go(R, e, Tr.first(Tr.Ent.k(e), r)), List.append(&2, Tr.Ent, Tr.set.go(r, e, Tr.first(Tr.Ent.k(e), r)), B), tc.set_go_app_l(r, B, b, e, Tr.first(Tr.Ent.k(e), r), {==}, gb, eb))

# a set below a bound sets the part below it
def tc.set_app_l(+A: List<&2, Tr.Ent>, +B: List<&2, Tr.Ent>, +b: Nat, +e: Tr.Ent, +gb: {LBoolMisc.tc.ge(B, b) == True{} : Bool}, +eb: {Nat.is_lt(Tr.Ent.k(e), b) == True{} : Bool}) -> {Tr.set(List.append(&2, Tr.Ent, A, B), e) == List.append(&2, Tr.Ent, Tr.set(A, e), B) : List<&2, Tr.Ent>}:
  %Equal.sym(Cmp, Tr.first(Tr.Ent.k(e), List.append(&2, Tr.Ent, A, B)), Tr.first(Tr.Ent.k(e), A), tc.first_app(A, B, b, e, gb, eb)) : {Tr.set.go(List.append(&2, Tr.Ent, A, B), e, _) == List.append(&2, Tr.Ent, Tr.set(A, e), B) : List<&2, Tr.Ent>}
  tc.set_go_app_l(A, B, b, e, Tr.first(Tr.Ent.k(e), A), {==}, gb, eb)

# a set at or above a bound sets the part above it
def tc.set_app_r(A: List<&2, Tr.Ent>, +B: List<&2, Tr.Ent>, +b: Nat, +e: Tr.Ent, +la: {LBoolMisc.tc.lt(A, b) == True{} : Bool}, +eb: {Nat.is_lt(Tr.Ent.k(e), b) == False{} : Bool}) -> {Tr.set(List.append(&2, Tr.Ent, A, B), e) == List.append(&2, Tr.Ent, A, Tr.set(B, e)) : List<&2, Tr.Ent>}:
  match A:
    case Nil{}:
      {==}
    case +a <> +r:
      +R = List.append(&2, Tr.Ent, r, B)
      +gt = LNatMisc.tc.cmp_gt(Tr.Ent.k(e), Tr.Ent.k(a), LNatIsLt.tc.lt_le(Tr.Ent.k(a), b, Tr.Ent.k(e), LNatIsLt.tc.lt_head(a, r, b, la), eb))
      %Equal.sym(Cmp, Nat.cmp(Tr.Ent.k(e), Tr.Ent.k(a)), GT{}, gt) : {Tr.set.go(a <> R, e, _) == a <> List.append(&2, Tr.Ent, r, Tr.set(B, e)) : List<&2, Tr.Ent>}
      Equal.cong(List<&2, Tr.Ent>, List<&2, Tr.Ent>, ys => a <> ys, Tr.set(R, e), List.append(&2, Tr.Ent, r, Tr.set(B, e)), tc.set_app_r(r, B, b, e, LBoolAnd.tc.lt_tail(a, r, b, la), eb))

# an unset of a key at or above a bound unsets the part above it
def tc.unset_app_r(A: List<&2, Tr.Ent>, +B: List<&2, Tr.Ent>, +b: Nat, +x: Nat, +la: {LBoolMisc.tc.lt(A, b) == True{} : Bool}, +xb: {Nat.is_lt(x, b) == False{} : Bool}) -> {Tr.unset(List.append(&2, Tr.Ent, A, B), x) == List.append(&2, Tr.Ent, A, Tr.unset(B, x)) : List<&2, Tr.Ent>}:
  match A:
    case Nil{}:
      {==}
    case +a <> +r:
      +R = List.append(&2, Tr.Ent, r, B)
      +ne = LNatIsLt.tc.lt_miss(a, b, x, LNatIsLt.tc.lt_head(a, r, b, la), xb)
      %Equal.sym(Bool, Nat.is_eq(Tr.Ent.k(a), x), False{}, ne) : {Tr.unset.go(a <> R, x, _) == a <> List.append(&2, Tr.Ent, r, Tr.unset(B, x)) : List<&2, Tr.Ent>}
      Equal.cong(List<&2, Tr.Ent>, List<&2, Tr.Ent>, ys => a <> ys, Tr.unset(R, x), List.append(&2, Tr.Ent, r, Tr.unset(B, x)), tc.unset_app_r(r, B, b, x, LBoolAnd.tc.lt_tail(a, r, b, la), xb))

# an unset of a key below every key changes nothing
def tc.unset_miss(B: List<&2, Tr.Ent>, +b: Nat, +x: Nat, +gb: {LBoolMisc.tc.ge(B, b) == True{} : Bool}, +xb: {Nat.is_lt(x, b) == True{} : Bool}) -> {Tr.unset(B, x) == B : List<&2, Tr.Ent>}:
  match B:
    case Nil{}:
      {==}
    case +f <> +r:
      +ne = LNatIsLt.tc.ge_miss(f, b, x, LNatIsLt.tc.ge_head(f, r, b, gb), xb)
      %Equal.sym(Bool, Nat.is_eq(Tr.Ent.k(f), x), False{}, ne) : {Tr.unset.go(f <> r, x, _) == f <> r : List<&2, Tr.Ent>}
      Equal.cong(List<&2, Tr.Ent>, List<&2, Tr.Ent>, ys => f <> ys, Tr.unset(r, x), r, tc.unset_miss(r, b, x, LBoolAnd.tc.ge_tail(f, r, b, gb), xb))

def tc.unset_step(+a: Tr.Ent, +r: List<&2, Tr.Ent>, +B: List<&2, Tr.Ent>, +x: Nat, c: Bool, +ih: {Tr.unset(List.append(&2, Tr.Ent, r, B), x) == List.append(&2, Tr.Ent, Tr.unset(r, x), B) : List<&2, Tr.Ent>}) -> {Tr.unset.go(a <> List.append(&2, Tr.Ent, r, B), x, c) == List.append(&2, Tr.Ent, Tr.unset.go(a <> r, x, c), B) : List<&2, Tr.Ent>}:
  match c:
    case True{}:
      ih
    case False{}:
      Equal.cong(List<&2, Tr.Ent>, List<&2, Tr.Ent>, ys => a <> ys, Tr.unset(List.append(&2, Tr.Ent, r, B), x), List.append(&2, Tr.Ent, Tr.unset(r, x), B), ih)

# an unset of a key below a bound unsets the part below it
def tc.unset_app_l(A: List<&2, Tr.Ent>, +B: List<&2, Tr.Ent>, +b: Nat, +x: Nat, +gb: {LBoolMisc.tc.ge(B, b) == True{} : Bool}, +xb: {Nat.is_lt(x, b) == True{} : Bool}) -> {Tr.unset(List.append(&2, Tr.Ent, A, B), x) == List.append(&2, Tr.Ent, Tr.unset(A, x), B) : List<&2, Tr.Ent>}:
  match A:
    case Nil{}:
      tc.unset_miss(B, b, x, gb, xb)
    case +a <> +r:
      tc.unset_step(a, r, B, x, Nat.is_eq(Tr.Ent.k(a), x), tc.unset_app_l(r, B, b, x, gb, xb))

# bounds over set and unset

def tc.lt_set(t: List<&2, Tr.Ent>, +e: Tr.Ent, c: Cmp, +b: Nat, +lt: {LBoolMisc.tc.lt(t, b) == True{} : Bool}, +eb: {Nat.is_lt(Tr.Ent.k(e), b) == True{} : Bool}) -> {LBoolMisc.tc.lt(Tr.set.go(t, e, c), b) == True{} : Bool}:
  match t:
    case Nil{}:
      LNatIsLt.tc.lt_cons(e, Nil{}, b, eb, {==})
    case +h <> +r:
      match c:
        case LT{}:
          LNatIsLt.tc.lt_cons(e, h <> r, b, eb, lt)
        case EQ{}:
          LNatIsLt.tc.lt_cons(e, r, b, eb, LBoolAnd.tc.lt_tail(h, r, b, lt))
        case GT{}:
          LNatIsLt.tc.lt_cons(h, Tr.set.go(r, e, Tr.first(Tr.Ent.k(e), r)), b, LNatIsLt.tc.lt_head(h, r, b, lt), tc.lt_set(r, e, Tr.first(Tr.Ent.k(e), r), b, LBoolAnd.tc.lt_tail(h, r, b, lt), eb))

def tc.ge_set(t: List<&2, Tr.Ent>, +e: Tr.Ent, c: Cmp, +b: Nat, +ge: {LBoolMisc.tc.ge(t, b) == True{} : Bool}, +eb: {Nat.is_lt(Tr.Ent.k(e), b) == False{} : Bool}) -> {LBoolMisc.tc.ge(Tr.set.go(t, e, c), b) == True{} : Bool}:
  match t:
    case Nil{}:
      LNatIsLt.tc.ge_cons(e, Nil{}, b, eb, {==})
    case +h <> +r:
      match c:
        case LT{}:
          LNatIsLt.tc.ge_cons(e, h <> r, b, eb, ge)
        case EQ{}:
          LNatIsLt.tc.ge_cons(e, r, b, eb, LBoolAnd.tc.ge_tail(h, r, b, ge))
        case GT{}:
          LNatIsLt.tc.ge_cons(h, Tr.set.go(r, e, Tr.first(Tr.Ent.k(e), r)), b, LNatIsLt.tc.ge_head(h, r, b, ge), tc.ge_set(r, e, Tr.first(Tr.Ent.k(e), r), b, LBoolAnd.tc.ge_tail(h, r, b, ge), eb))

def tc.lt_unset(t: List<&2, Tr.Ent>, +x: Nat, hit: Bool, +b: Nat, +lt: {LBoolMisc.tc.lt(t, b) == True{} : Bool}) -> {LBoolMisc.tc.lt(Tr.unset.go(t, x, hit), b) == True{} : Bool}:
  match t:
    case Nil{}:
      {==}
    case +h <> +r:
      match hit:
        case True{}:
          tc.lt_unset(r, x, Tr.key.at(r, x), b, LBoolAnd.tc.lt_tail(h, r, b, lt))
        case False{}:
          LNatIsLt.tc.lt_cons(h, Tr.unset.go(r, x, Tr.key.at(r, x)), b, LNatIsLt.tc.lt_head(h, r, b, lt), tc.lt_unset(r, x, Tr.key.at(r, x), b, LBoolAnd.tc.lt_tail(h, r, b, lt)))

def tc.ge_unset(t: List<&2, Tr.Ent>, +x: Nat, hit: Bool, +b: Nat, +ge: {LBoolMisc.tc.ge(t, b) == True{} : Bool}) -> {LBoolMisc.tc.ge(Tr.unset.go(t, x, hit), b) == True{} : Bool}:
  match t:
    case Nil{}:
      {==}
    case +h <> +r:
      match hit:
        case True{}:
          tc.ge_unset(r, x, Tr.key.at(r, x), b, LBoolAnd.tc.ge_tail(h, r, b, ge))
        case False{}:
          LNatIsLt.tc.ge_cons(h, Tr.unset.go(r, x, Tr.key.at(r, x)), b, LNatIsLt.tc.ge_head(h, r, b, ge), tc.ge_unset(r, x, Tr.key.at(r, x), b, LBoolAnd.tc.ge_tail(h, r, b, ge)))

def tc.split_read(+a: Tr.Ent, +b: Tr.Ent, c: Bool) -> {Tr.KMap.read(Tr.KMap.split(a, b, c)) == LList.tc.pair(c, a, b) : List<&2, Tr.Ent>}:
  match c:
    case True{}:
      {==}
    case False{}:
      {==}

def tc.split_bst(+a: Tr.Ent, +b: Tr.Ent, c: Bool, +ec: {Nat.is_lt(Tr.Ent.k(a), Tr.Ent.k(b)) == c : Bool}, +ne: {Nat.is_eq(Tr.Ent.k(a), Tr.Ent.k(b)) == False{} : Bool}) -> {LBoolMisc.tc.bst(Tr.KMap.split(a, b, c)) == True{} : Bool}:
  match c:
    case True{}:
      tc.bst_fork(Tr.Ent.k(b), Tr.KOne{a}, Tr.KOne{b}, {==}, {==}, LNatIsLt.tc.lt_cons(a, Nil{}, Tr.Ent.k(b), ec, {==}), LNatIsLt.tc.ge_cons(b, Nil{}, Tr.Ent.k(b), LNatIsLt.pt.lt_irrefl(Tr.Ent.k(b)), {==}))
    case False{}:
      +ba = LNatIsLt.tc.lt_total(Tr.Ent.k(a), Tr.Ent.k(b), ec, ne)
      tc.bst_fork(Tr.Ent.k(a), Tr.KOne{b}, Tr.KOne{a}, {==}, {==}, LNatIsLt.tc.lt_cons(b, Nil{}, Tr.Ent.k(a), ba, {==}), LNatIsLt.tc.ge_cons(a, Nil{}, Tr.Ent.k(a), LNatIsLt.pt.lt_irrefl(Tr.Ent.k(a)), {==}))

def tc.two_read(hs: List<&2, Nat>, +lo: Nat, +a: Tr.Ent, +b: Tr.Ent, ca: Bool, cb: Bool, +eca: {Nat.is_lt(Tr.Ent.k(a), Nat.add(lo, Tr.KMap.half(hs))) == ca : Bool}, +ecb: {Nat.is_lt(Tr.Ent.k(b), Nat.add(lo, Tr.KMap.half(hs))) == cb : Bool}) -> {Tr.KMap.read(Tr.KMap.two(hs, lo, a, b, ca, cb)) == LList.tc.pair(Nat.is_lt(Tr.Ent.k(a), Tr.Ent.k(b)), a, b) : List<&2, Tr.Ent>}:
  match hs:
    case Nil{}:
      tc.split_read(a, b, Nat.is_lt(Tr.Ent.k(a), Tr.Ent.k(b)))
    case +h <> +rest:
      match ca cb:
        case True{} True{}:
          +g = Tr.KMap.half(rest)
          +X = Tr.KMap.two(rest, lo, a, b, Nat.is_lt(Tr.Ent.k(a), Nat.add(lo, g)), Nat.is_lt(Tr.Ent.k(b), Nat.add(lo, g)))
          Equal.trans(List<&2, Tr.Ent>, List.append(&2, Tr.Ent, Tr.KMap.read(X), Nil{}), Tr.KMap.read(X), LList.tc.pair(Nat.is_lt(Tr.Ent.k(a), Tr.Ent.k(b)), a, b), LList.tc.app_nil(Tr.KMap.read(X)), tc.two_read(rest, lo, a, b, Nat.is_lt(Tr.Ent.k(a), Nat.add(lo, g)), Nat.is_lt(Tr.Ent.k(b), Nat.add(lo, g)), {==}, {==}))
        case True{} False{}:
          +lt = LNatIsLt.tc.lt_le(Tr.Ent.k(a), Nat.add(lo, h), Tr.Ent.k(b), eca, ecb)
          %Equal.sym(Bool, Nat.is_lt(Tr.Ent.k(a), Tr.Ent.k(b)), True{}, lt) : {[a, b] == LList.tc.pair(_, a, b) : List<&2, Tr.Ent>}
          {==}
        case False{} True{}:
          +ba = LNatIsLt.tc.lt_le(Tr.Ent.k(b), Nat.add(lo, h), Tr.Ent.k(a), ecb, eca)
          +nab = LNatIsLt.tc.lt_asym(Tr.Ent.k(b), Tr.Ent.k(a), ba)
          %Equal.sym(Bool, Nat.is_lt(Tr.Ent.k(a), Tr.Ent.k(b)), False{}, nab) : {[b, a] == LList.tc.pair(_, a, b) : List<&2, Tr.Ent>}
          {==}
        case False{} False{}:
          +g = Tr.KMap.half(rest)
          +n = Nat.add(lo, h)
          tc.two_read(rest, n, a, b, Nat.is_lt(Tr.Ent.k(a), Nat.add(n, g)), Nat.is_lt(Tr.Ent.k(b), Nat.add(n, g)), {==}, {==})

def tc.two_bst(hs: List<&2, Nat>, +lo: Nat, +a: Tr.Ent, +b: Tr.Ent, ca: Bool, cb: Bool, +eca: {Nat.is_lt(Tr.Ent.k(a), Nat.add(lo, Tr.KMap.half(hs))) == ca : Bool}, +ecb: {Nat.is_lt(Tr.Ent.k(b), Nat.add(lo, Tr.KMap.half(hs))) == cb : Bool}, +ne: {Nat.is_eq(Tr.Ent.k(a), Tr.Ent.k(b)) == False{} : Bool}) -> {LBoolMisc.tc.bst(Tr.KMap.two(hs, lo, a, b, ca, cb)) == True{} : Bool}:
  match hs:
    case Nil{}:
      tc.split_bst(a, b, Nat.is_lt(Tr.Ent.k(a), Tr.Ent.k(b)), {==}, ne)
    case +h <> +rest:
      match ca cb:
        case True{} True{}:
          +g = Tr.KMap.half(rest)
          +X = Tr.KMap.two(rest, lo, a, b, Nat.is_lt(Tr.Ent.k(a), Nat.add(lo, g)), Nat.is_lt(Tr.Ent.k(b), Nat.add(lo, g)))
          +rx = tc.two_read(rest, lo, a, b, Nat.is_lt(Tr.Ent.k(a), Nat.add(lo, g)), Nat.is_lt(Tr.Ent.k(b), Nat.add(lo, g)), {==}, {==})
          +lx = LList.tc.pair_lt(Nat.is_lt(Tr.Ent.k(a), Tr.Ent.k(b)), a, b, Nat.add(lo, h), eca, ecb)
          +P = LList.tc.pair(Nat.is_lt(Tr.Ent.k(a), Tr.Ent.k(b)), a, b)
          +ll = Equal.trans(Bool, LBoolMisc.tc.lt(Tr.KMap.read(X), Nat.add(lo, h)), LBoolMisc.tc.lt(P, Nat.add(lo, h)), True{}, Equal.cong(List<&2, Tr.Ent>, Bool, y => LBoolMisc.tc.lt(y, Nat.add(lo, h)), Tr.KMap.read(X), P, rx), lx)
          tc.bst_fork(Nat.add(lo, h), X, Tr.KNil{}, tc.two_bst(rest, lo, a, b, Nat.is_lt(Tr.Ent.k(a), Nat.add(lo, g)), Nat.is_lt(Tr.Ent.k(b), Nat.add(lo, g)), {==}, {==}, ne), {==}, ll, {==})
        case True{} False{}:
          tc.bst_fork(Nat.add(lo, h), Tr.KOne{a}, Tr.KOne{b}, {==}, {==}, LNatIsLt.tc.lt_cons(a, Nil{}, Nat.add(lo, h), eca, {==}), LNatIsLt.tc.ge_cons(b, Nil{}, Nat.add(lo, h), ecb, {==}))
        case False{} True{}:
          tc.bst_fork(Nat.add(lo, h), Tr.KOne{b}, Tr.KOne{a}, {==}, {==}, LNatIsLt.tc.lt_cons(b, Nil{}, Nat.add(lo, h), ecb, {==}), LNatIsLt.tc.ge_cons(a, Nil{}, Nat.add(lo, h), eca, {==}))
        case False{} False{}:
          +g = Tr.KMap.half(rest)
          +n = Nat.add(lo, h)
          +X = Tr.KMap.two(rest, n, a, b, Nat.is_lt(Tr.Ent.k(a), Nat.add(n, g)), Nat.is_lt(Tr.Ent.k(b), Nat.add(n, g)))
          +rx = tc.two_read(rest, n, a, b, Nat.is_lt(Tr.Ent.k(a), Nat.add(n, g)), Nat.is_lt(Tr.Ent.k(b), Nat.add(n, g)), {==}, {==})
          +gx = LList.tc.pair_ge(Nat.is_lt(Tr.Ent.k(a), Tr.Ent.k(b)), a, b, n, eca, ecb)
          +P = LList.tc.pair(Nat.is_lt(Tr.Ent.k(a), Tr.Ent.k(b)), a, b)
          +gg = Equal.trans(Bool, LBoolMisc.tc.ge(Tr.KMap.read(X), n), LBoolMisc.tc.ge(P, n), True{}, Equal.cong(List<&2, Tr.Ent>, Bool, y => LBoolMisc.tc.ge(y, n), Tr.KMap.read(X), P, rx), gx)
          tc.bst_fork(n, Tr.KNil{}, X, {==}, tc.two_bst(rest, n, a, b, Nat.is_lt(Tr.Ent.k(a), Nat.add(n, g)), Nat.is_lt(Tr.Ent.k(b), Nat.add(n, g)), {==}, {==}, ne), {==}, gg)

def tc.set_one(+f: Tr.Ent, +e: Tr.Ent, c: Bool, +ec: {Nat.is_lt(Tr.Ent.k(f), Tr.Ent.k(e)) == c : Bool}, +ne: {Nat.is_eq(Tr.Ent.k(f), Tr.Ent.k(e)) == False{} : Bool}) -> {Tr.set([f], e) == LList.tc.pair(c, f, e) : List<&2, Tr.Ent>}:
  match c:
    case True{}:
      +gt = LNatMisc.tc.cmp_gt(Tr.Ent.k(e), Tr.Ent.k(f), ec)
      %Equal.sym(Cmp, Nat.cmp(Tr.Ent.k(e), Tr.Ent.k(f)), GT{}, gt) : {Tr.set.go([f], e, _) == [f, e] : List<&2, Tr.Ent>}
      {==}
    case False{}:
      +lt = LNatMisc.tc.cmp_lt(Tr.Ent.k(e), Tr.Ent.k(f), LNatIsLt.tc.lt_total(Tr.Ent.k(f), Tr.Ent.k(e), ec, ne))
      %Equal.sym(Cmp, Nat.cmp(Tr.Ent.k(e), Tr.Ent.k(f)), LT{}, lt) : {Tr.set.go([f], e, _) == [e, f] : List<&2, Tr.Ent>}
      {==}

def tc.put_read(m: Tr.KMap, +hs: List<&2, Nat>, +lo: Nat, +e: Tr.Ent, b: Bool, +eb: {Tr.KMap.at(m, Tr.Ent.k(e)) == b : Bool}, +bt: {LBoolMisc.tc.bst(m) == True{} : Bool}) -> {Tr.KMap.read(Tr.KMap.put(m, hs, lo, e, b)) == Tr.set(Tr.KMap.read(m), e) : List<&2, Tr.Ent>}:
  match m b:
    case Tr.KNil{} True{}:
      {==}
    case Tr.KNil{} False{}:
      {==}
    case Tr.KOne{+f} True{}:
      +eq = Equal.trans(Bool, Nat.is_eq(Tr.Ent.k(e), Tr.Ent.k(f)), Nat.is_eq(Tr.Ent.k(f), Tr.Ent.k(e)), True{}, LNatIsEq.pt.eq_comm(Tr.Ent.k(e), Tr.Ent.k(f)), eb)
      %Equal.sym(Cmp, Nat.cmp(Tr.Ent.k(e), Tr.Ent.k(f)), EQ{}, LNatMisc.tc.cmp_eq(Tr.Ent.k(e), Tr.Ent.k(f), eq)) : {[e] == Tr.set.go([f], e, _) : List<&2, Tr.Ent>}
      {==}
    case Tr.KOne{+f} False{}:
      +c = Nat.is_lt(Tr.Ent.k(f), Tr.Ent.k(e))
      +r2 = tc.two_read(hs, lo, f, e, Nat.is_lt(Tr.Ent.k(f), Nat.add(lo, Tr.KMap.half(hs))), Nat.is_lt(Tr.Ent.k(e), Nat.add(lo, Tr.KMap.half(hs))), {==}, {==})
      Equal.trans(List<&2, Tr.Ent>, Tr.KMap.read(Tr.KMap.two(hs, lo, f, e, Nat.is_lt(Tr.Ent.k(f), Nat.add(lo, Tr.KMap.half(hs))), Nat.is_lt(Tr.Ent.k(e), Nat.add(lo, Tr.KMap.half(hs))))), LList.tc.pair(c, f, e), Tr.set([f], e), r2, Equal.sym(List<&2, Tr.Ent>, Tr.set([f], e), LList.tc.pair(c, f, e), tc.set_one(f, e, c, {==}, eb)))
    case Tr.KFork{+mid, +mp, +l, +r} True{}:
      +L = Tr.KMap.read(l)
      +R = Tr.KMap.read(r)
      +P = Tr.KMap.put(l, Tr.KMap.below(hs), lo, e, Tr.KMap.at(l, Tr.Ent.k(e)))
      +ih = tc.put_read(l, Tr.KMap.below(hs), lo, e, Tr.KMap.at(l, Tr.Ent.k(e)), {==}, tc.bst_l(mid, mp, l, r, bt))
      +s1 = Equal.cong(List<&2, Tr.Ent>, List<&2, Tr.Ent>, y => List.append(&2, Tr.Ent, y, R), Tr.KMap.read(P), Tr.set(L, e), ih)
      Equal.trans(List<&2, Tr.Ent>, List.append(&2, Tr.Ent, Tr.KMap.read(P), R), List.append(&2, Tr.Ent, Tr.set(L, e), R), Tr.set(List.append(&2, Tr.Ent, L, R), e), s1, Equal.sym(List<&2, Tr.Ent>, Tr.set(List.append(&2, Tr.Ent, L, R), e), List.append(&2, Tr.Ent, Tr.set(L, e), R), tc.set_app_l(L, R, mid, e, tc.bst_ge(mid, mp, l, r, bt), eb)))
    case Tr.KFork{+mid, +mp, +l, +r} False{}:
      +L = Tr.KMap.read(l)
      +R = Tr.KMap.read(r)
      +P = Tr.KMap.put(r, Tr.KMap.below(hs), mid, e, Tr.KMap.at(r, Tr.Ent.k(e)))
      +ih = tc.put_read(r, Tr.KMap.below(hs), mid, e, Tr.KMap.at(r, Tr.Ent.k(e)), {==}, tc.bst_r(mid, mp, l, r, bt))
      +s1 = Equal.cong(List<&2, Tr.Ent>, List<&2, Tr.Ent>, y => List.append(&2, Tr.Ent, L, y), Tr.KMap.read(P), Tr.set(R, e), ih)
      Equal.trans(List<&2, Tr.Ent>, List.append(&2, Tr.Ent, L, Tr.KMap.read(P)), List.append(&2, Tr.Ent, L, Tr.set(R, e)), Tr.set(List.append(&2, Tr.Ent, L, R), e), s1, Equal.sym(List<&2, Tr.Ent>, Tr.set(List.append(&2, Tr.Ent, L, R), e), List.append(&2, Tr.Ent, L, Tr.set(R, e)), tc.set_app_r(L, R, mid, e, tc.bst_lt(mid, mp, l, r, bt), eb)))

def tc.put_bst(m: Tr.KMap, +hs: List<&2, Nat>, +lo: Nat, +e: Tr.Ent, b: Bool, +eb: {Tr.KMap.at(m, Tr.Ent.k(e)) == b : Bool}, +bt: {LBoolMisc.tc.bst(m) == True{} : Bool}) -> {LBoolMisc.tc.bst(Tr.KMap.put(m, hs, lo, e, b)) == True{} : Bool}:
  match m b:
    case Tr.KNil{} True{}:
      {==}
    case Tr.KNil{} False{}:
      {==}
    case Tr.KOne{+f} True{}:
      {==}
    case Tr.KOne{+f} False{}:
      tc.two_bst(hs, lo, f, e, Nat.is_lt(Tr.Ent.k(f), Nat.add(lo, Tr.KMap.half(hs))), Nat.is_lt(Tr.Ent.k(e), Nat.add(lo, Tr.KMap.half(hs))), {==}, {==}, eb)
    case Tr.KFork{+mid, +mp, +l, +r} True{}:
      +P = Tr.KMap.put(l, Tr.KMap.below(hs), lo, e, Tr.KMap.at(l, Tr.Ent.k(e)))
      +bl = tc.bst_l(mid, mp, l, r, bt)
      +rd = tc.put_read(l, Tr.KMap.below(hs), lo, e, Tr.KMap.at(l, Tr.Ent.k(e)), {==}, bl)
      +S = Tr.set(Tr.KMap.read(l), e)
      +ls = tc.lt_set(Tr.KMap.read(l), e, Tr.first(Tr.Ent.k(e), Tr.KMap.read(l)), mid, tc.bst_lt(mid, mp, l, r, bt), eb)
      +ll = Equal.trans(Bool, LBoolMisc.tc.lt(Tr.KMap.read(P), mid), LBoolMisc.tc.lt(S, mid), True{}, Equal.cong(List<&2, Tr.Ent>, Bool, y => LBoolMisc.tc.lt(y, mid), Tr.KMap.read(P), S, rd), ls)
      tc.bst_fork(mid, P, r, tc.put_bst(l, Tr.KMap.below(hs), lo, e, Tr.KMap.at(l, Tr.Ent.k(e)), {==}, bl), tc.bst_r(mid, mp, l, r, bt), ll, tc.bst_ge(mid, mp, l, r, bt))
    case Tr.KFork{+mid, +mp, +l, +r} False{}:
      +P = Tr.KMap.put(r, Tr.KMap.below(hs), mid, e, Tr.KMap.at(r, Tr.Ent.k(e)))
      +br = tc.bst_r(mid, mp, l, r, bt)
      +rd = tc.put_read(r, Tr.KMap.below(hs), mid, e, Tr.KMap.at(r, Tr.Ent.k(e)), {==}, br)
      +S = Tr.set(Tr.KMap.read(r), e)
      +gs = tc.ge_set(Tr.KMap.read(r), e, Tr.first(Tr.Ent.k(e), Tr.KMap.read(r)), mid, tc.bst_ge(mid, mp, l, r, bt), eb)
      +gg = Equal.trans(Bool, LBoolMisc.tc.ge(Tr.KMap.read(P), mid), LBoolMisc.tc.ge(S, mid), True{}, Equal.cong(List<&2, Tr.Ent>, Bool, y => LBoolMisc.tc.ge(y, mid), Tr.KMap.read(P), S, rd), gs)
      tc.bst_fork(mid, l, P, tc.bst_l(mid, mp, l, r, bt), tc.put_bst(r, Tr.KMap.below(hs), mid, e, Tr.KMap.at(r, Tr.Ent.k(e)), {==}, br), tc.bst_lt(mid, mp, l, r, bt), gg)

def tc.unset_read(m: Tr.KMap, +x: Nat, b: Bool, +eb: {Tr.KMap.at(m, x) == b : Bool}, +bt: {LBoolMisc.tc.bst(m) == True{} : Bool}) -> {Tr.KMap.read(Tr.KMap.unset(m, x, b)) == Tr.unset(Tr.KMap.read(m), x) : List<&2, Tr.Ent>}:
  match m b:
    case Tr.KNil{} True{}:
      {==}
    case Tr.KNil{} False{}:
      {==}
    case Tr.KOne{+e} True{}:
      %Equal.sym(Bool, Nat.is_eq(Tr.Ent.k(e), x), True{}, eb) : {Nil{} == Tr.unset.go([e], x, _) : List<&2, Tr.Ent>}
      {==}
    case Tr.KOne{+e} False{}:
      %Equal.sym(Bool, Nat.is_eq(Tr.Ent.k(e), x), False{}, eb) : {[e] == Tr.unset.go([e], x, _) : List<&2, Tr.Ent>}
      {==}
    case Tr.KFork{+mid, +mp, +l, +r} True{}:
      +L = Tr.KMap.read(l)
      +R = Tr.KMap.read(r)
      +U = Tr.KMap.unset(l, x, Tr.KMap.at(l, x))
      +ih = tc.unset_read(l, x, Tr.KMap.at(l, x), {==}, tc.bst_l(mid, mp, l, r, bt))
      +s1 = Equal.cong(List<&2, Tr.Ent>, List<&2, Tr.Ent>, y => List.append(&2, Tr.Ent, y, R), Tr.KMap.read(U), Tr.unset(L, x), ih)
      Equal.trans(List<&2, Tr.Ent>, List.append(&2, Tr.Ent, Tr.KMap.read(U), R), List.append(&2, Tr.Ent, Tr.unset(L, x), R), Tr.unset(List.append(&2, Tr.Ent, L, R), x), s1, Equal.sym(List<&2, Tr.Ent>, Tr.unset(List.append(&2, Tr.Ent, L, R), x), List.append(&2, Tr.Ent, Tr.unset(L, x), R), tc.unset_app_l(L, R, mid, x, tc.bst_ge(mid, mp, l, r, bt), eb)))
    case Tr.KFork{+mid, +mp, +l, +r} False{}:
      +L = Tr.KMap.read(l)
      +R = Tr.KMap.read(r)
      +U = Tr.KMap.unset(r, x, Tr.KMap.at(r, x))
      +ih = tc.unset_read(r, x, Tr.KMap.at(r, x), {==}, tc.bst_r(mid, mp, l, r, bt))
      +s1 = Equal.cong(List<&2, Tr.Ent>, List<&2, Tr.Ent>, y => List.append(&2, Tr.Ent, L, y), Tr.KMap.read(U), Tr.unset(R, x), ih)
      Equal.trans(List<&2, Tr.Ent>, List.append(&2, Tr.Ent, L, Tr.KMap.read(U)), List.append(&2, Tr.Ent, L, Tr.unset(R, x)), Tr.unset(List.append(&2, Tr.Ent, L, R), x), s1, Equal.sym(List<&2, Tr.Ent>, Tr.unset(List.append(&2, Tr.Ent, L, R), x), List.append(&2, Tr.Ent, L, Tr.unset(R, x)), tc.unset_app_r(L, R, mid, x, tc.bst_lt(mid, mp, l, r, bt), eb)))

def tc.unset_bst(m: Tr.KMap, +x: Nat, b: Bool, +eb: {Tr.KMap.at(m, x) == b : Bool}, +bt: {LBoolMisc.tc.bst(m) == True{} : Bool}) -> {LBoolMisc.tc.bst(Tr.KMap.unset(m, x, b)) == True{} : Bool}:
  match m b:
    case Tr.KNil{} True{}:
      {==}
    case Tr.KNil{} False{}:
      {==}
    case Tr.KOne{+e} True{}:
      {==}
    case Tr.KOne{+e} False{}:
      {==}
    case Tr.KFork{+mid, +mp, +l, +r} True{}:
      +U = Tr.KMap.unset(l, x, Tr.KMap.at(l, x))
      +bl = tc.bst_l(mid, mp, l, r, bt)
      +rd = tc.unset_read(l, x, Tr.KMap.at(l, x), {==}, bl)
      +S = Tr.unset(Tr.KMap.read(l), x)
      +ls = tc.lt_unset(Tr.KMap.read(l), x, Tr.key.at(Tr.KMap.read(l), x), mid, tc.bst_lt(mid, mp, l, r, bt))
      +ll = Equal.trans(Bool, LBoolMisc.tc.lt(Tr.KMap.read(U), mid), LBoolMisc.tc.lt(S, mid), True{}, Equal.cong(List<&2, Tr.Ent>, Bool, y => LBoolMisc.tc.lt(y, mid), Tr.KMap.read(U), S, rd), ls)
      tc.bst_fork(mid, U, r, tc.unset_bst(l, x, Tr.KMap.at(l, x), {==}, bl), tc.bst_r(mid, mp, l, r, bt), ll, tc.bst_ge(mid, mp, l, r, bt))
    case Tr.KFork{+mid, +mp, +l, +r} False{}:
      +U = Tr.KMap.unset(r, x, Tr.KMap.at(r, x))
      +br = tc.bst_r(mid, mp, l, r, bt)
      +rd = tc.unset_read(r, x, Tr.KMap.at(r, x), {==}, br)
      +S = Tr.unset(Tr.KMap.read(r), x)
      +gs = tc.ge_unset(Tr.KMap.read(r), x, Tr.key.at(Tr.KMap.read(r), x), mid, tc.bst_ge(mid, mp, l, r, bt))
      +gg = Equal.trans(Bool, LBoolMisc.tc.ge(Tr.KMap.read(U), mid), LBoolMisc.tc.ge(S, mid), True{}, Equal.cong(List<&2, Tr.Ent>, Bool, y => LBoolMisc.tc.ge(y, mid), Tr.KMap.read(U), S, rd), gs)
      tc.bst_fork(mid, l, U, tc.bst_l(mid, mp, l, r, bt), tc.unset_bst(r, x, Tr.KMap.at(r, x), {==}, br), tc.bst_lt(mid, mp, l, r, bt), gg)

def tc.set_bst(+m: Tr.KMap, +hs: List<&2, Nat>, +e: Tr.Ent, +bt: {LBoolMisc.tc.bst(m) == True{} : Bool}) -> {LBoolMisc.tc.bst(Tr.KMap.set(m, hs, e)) == True{} : Bool}:
  tc.put_bst(m, hs, 0n, e, Tr.KMap.at(m, Tr.Ent.k(e)), {==}, bt)

def tc.del_bst(+m: Tr.KMap, +x: Nat, +bt: {LBoolMisc.tc.bst(m) == True{} : Bool}) -> {LBoolMisc.tc.bst(Tr.KMap.del(m, x)) == True{} : Bool}:
  tc.unset_bst(m, x, Tr.KMap.at(m, x), {==}, bt)

def tc.drop_bst(ks: List<&2, Nat>, +m: Tr.KMap, +bt: {LBoolMisc.tc.bst(m) == True{} : Bool}) -> {LBoolMisc.tc.bst(Tr.KMap.drop(ks, m)) == True{} : Bool}:
  match ks:
    case Nil{}:
      bt
    case +k <> rest:
      tc.drop_bst(rest, Tr.KMap.del(m, k), tc.del_bst(m, k, bt))

def tc.exact_bst(+m: Tr.KMap, +hs: List<&2, Nat>, o: Tr.Op, +bt: {LBoolMisc.tc.bst(m) == True{} : Bool}) -> {LBoolMisc.tc.bst(Tr.KMap.exact(m, hs, o)) == True{} : Bool}:
  match o:
    case Tr.Put{+k, +p, +v}:
      tc.set_bst(m, hs, Tr.Ent{k, p, v}, bt)
    case Tr.Del{+x}:
      tc.del_bst(m, x, bt)

def tc.patch_bst(ops: List<&2, Tr.Op>, +hs: List<&2, Nat>, +m: Tr.KMap, +bt: {LBoolMisc.tc.bst(m) == True{} : Bool}) -> {LBoolMisc.tc.bst(Tr.KMap.patch(ops, hs, m)) == True{} : Bool}:
  match ops:
    case Nil{}:
      bt
    case +o <> rest:
      tc.patch_bst(rest, hs, Tr.KMap.exact(m, hs, o), tc.exact_bst(m, hs, o, bt))

def tc.put_case_bst(b: Bool, +m: Tr.KMap, +hs: List<&2, Nat>, +e: Tr.Ent, +bt: {LBoolMisc.tc.bst(m) == True{} : Bool}) -> {LBoolMisc.tc.bst(Pair.fst(Tr.KMap, Tr.Ans, Tr.put.ans(b, m, hs, e))) == True{} : Bool}:
  match b:
    case True{}:
      tc.set_bst(m, hs, e, bt)
    case False{}:
      bt

def tc.rec_bst(+m: Tr.KMap, +hs: List<&2, Nat>, r: Tr.Rec, +bt: {LBoolMisc.tc.bst(m) == True{} : Bool}) -> {LBoolMisc.tc.bst(Pair.fst(Tr.KMap, Tr.Ans, Tr.KMap.rec(m, hs, r))) == True{} : Bool}:
  match r:
    case Tr.Do{o}:
      match o:
        case Tr.Put{+k, +p, +v}:
          tc.put_case_bst(Bool.and(Nat.is_lt(p, k), Bool.or(Nat.is_eq(p, 0n), Tr.KMap.has(m, p))), m, hs, Tr.Ent{k, p, v}, bt)
        case Tr.Del{x}:
          match x:
            case 0n:
              bt
            case 1n++y:
              +F = Tr.KMap.ups(m, 1n+y, Nil{}, Tr.KMap.gl(m, 1n+y), Tr.KMap.gr(m, 1n+y))
              tc.drop_bst(Tr.drops(F, hs, 1n+y), m, bt)
    case Tr.Rewind{+ops}:
      +n = Tr.KMap.patch(ops, hs, m)
      LPair.tc.keep_case_bst(Tr.KMap.hangs(Tr.KMap.onto(n, Nil{}), n), m, n, bt, tc.patch_bst(ops, hs, m, bt))

# Journals

def tc.go_bst(rs: List<&2, Tr.Rec>, +hs: List<&2, Nat>, +m: Tr.KMap, +bt: {LBoolMisc.tc.bst(m) == True{} : Bool}) -> {LBoolMisc.tc.bst(Tr.KMap.go(rs, hs, m)) == True{} : Bool}:
  match rs:
    case Nil{}:
      bt
    case +r <> rest:
      tc.go_bst(rest, hs, Pair.fst(Tr.KMap, Tr.Ans, Tr.KMap.rec(m, hs, r)), tc.rec_bst(m, hs, r, bt))

def tc.at_bst(+hs: List<&2, Nat>, +rs: List<&2, Tr.Rec>, +n: Nat) -> {LBoolMisc.tc.bst(Tr.St.at(List.reverse.go(&2, Tr.Rec, rs, Nil{}), hs, n)) == True{} : Bool}:
  tc.go_bst(List.take(&2, Tr.Rec, List.reverse(&2, Tr.Rec, List.reverse.go(&2, Tr.Rec, rs, Nil{})), n), hs, Tr.KNil{}, {==})
