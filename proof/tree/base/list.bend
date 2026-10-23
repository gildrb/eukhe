# eukhe: lemmas the proofs of area tree share: list

import Base
import ../../../bend/tree.bend as Tr
import ../../base/bool/and.bend as LBoolAnd
import ../../base/bool/misc.bend as LBoolMisc
import ./bool.bend as LABool
import ./nat.bend as LANat

def pt.app_snoc(A: List<&2, Tr.Ent>, +e: Tr.Ent, +C: List<&2, Tr.Ent>) -> {List.append(&2, Tr.Ent, List.append(&2, Tr.Ent, A, [e]), C) == List.append(&2, Tr.Ent, A, e <> C) : List<&2, Tr.Ent>}:
  match A:
    case Nil{}:
      {==}
    case +a <> +r:
      Equal.cong(List<&2, Tr.Ent>, List<&2, Tr.Ent>, l => a <> l, List.append(&2, Tr.Ent, List.append(&2, Tr.Ent, r, [e]), C), List.append(&2, Tr.Ent, r, e <> C), pt.app_snoc(r, e, C))

def pt.cov_app(A: List<&2, Tr.Ent>, +C: List<&2, Tr.Ent>, +b: List<&2, Tr.Ent>, +g: List<&2, Nat>, +ca: {LABool.pt.cov(A, b, g) == True{} : Bool}, +cc: {LABool.pt.cov(C, b, g) == True{} : Bool}) -> {LABool.pt.cov(List.append(&2, Tr.Ent, A, C), b, g) == True{} : Bool}:
  match A:
    case Nil{}:
      cc
    case +a <> +r:
      +i = Bool.or(Tr.has(b, Tr.Ent.k(a)), Tr.elem(g, Tr.Ent.k(a)))
      LBoolAnd.tree.pt.and_t(i, LABool.pt.cov(List.append(&2, Tr.Ent, r, C), b, g), LBoolAnd.tree.pt.and_l(i, LABool.pt.cov(r, b, g), ca), pt.cov_app(r, C, b, g, LBoolAnd.tree.pt.and_r(i, LABool.pt.cov(r, b, g), ca), cc))

# l1 and l2 hold the same node at the key of each node of es
def pt.Agree(es: List<&2, Tr.Ent>, +l1: List<&2, Tr.Ent>, +l2: List<&2, Tr.Ent>) -> Type:
  match es:
    case Nil{}:
      Unit
    case +e <> rest:
      ({Tr.get(l1, Tr.Ent.k(e)) == Tr.get(l2, Tr.Ent.k(e)) : Maybe<&2, Tr.Ent>} & pt.Agree(rest, l1, l2))

# The compiled core
# -----------------
# The key map refines the sorted list: a fork's left keys are below its
# split and its right keys at or above it (`tc.bst`), so its nodes in
# order are sorted (`tc.sorted_read`), a lookup down the map is the list
# lookup (`tc.get`), and a put, an unset and a drop are the list's set,
# unset and unset of each key (`tc.put_read`, `tc.unset_read`). A record
# on the map is apply on the list (`tc.rec_read`), with the model's answer
# (`tc.rec_ans`); a delete walks only the nodes from its key on, and the
# nodes before them never go (`tc.drops_ge`). The plan merges two sorted
# lists; the merge is diff (`tc.diff_m`).

# the keys of the nodes that prune.go removes from s, in order: the walk
# of a delete with its gone keys as a list (the core keeps them in a key
# map, `Tr.drops.s`; `tc.drops` shows the two walks drop the same keys)
def tc.dgo(s: List<&2, Tr.Ent>, +gone: List<&2, Nat>, hit: Bool) -> List<&2, Nat>:
  match s:
    case Nil{}:
      Nil{}
    case +e <> +rest:
      match hit:
        case True{}:
          Tr.Ent.k(e) <> tc.dgo(rest, Tr.Ent.k(e) <> gone, Tr.gone.at(rest, Tr.Ent.k(e) <> gone))
        case False{}:
          tc.dgo(rest, gone, Tr.gone.at(rest, gone))

def tc.app_assoc(a: List<&2, Tr.Ent>, +b: List<&2, Tr.Ent>, +c: List<&2, Tr.Ent>) -> {List.append(&2, Tr.Ent, List.append(&2, Tr.Ent, a, b), c) == List.append(&2, Tr.Ent, a, List.append(&2, Tr.Ent, b, c)) : List<&2, Tr.Ent>}:
  match a:
    case Nil{}:
      {==}
    case h <> t:
      Equal.cong(List<&2, Tr.Ent>, List<&2, Tr.Ent>, ys => h <> ys, List.append(&2, Tr.Ent, List.append(&2, Tr.Ent, t, b), c), List.append(&2, Tr.Ent, t, List.append(&2, Tr.Ent, b, c)), tc.app_assoc(t, b, c))

# t less the nodes of keys ks, one by one
def tc.unsets(ks: List<&2, Nat>, t: List<&2, Tr.Ent>) -> List<&2, Tr.Ent>:
  match ks:
    case Nil{}:
      t
    case k <> rest:
      tc.unsets(rest, Tr.unset(t, k))

def tc.ple_app(A: List<&2, Tr.Ent>, +B: List<&2, Tr.Ent>, +b: Nat, +pa: {LABool.tc.ple(A, b) == True{} : Bool}, +pb: {LABool.tc.ple(B, b) == True{} : Bool}) -> {LABool.tc.ple(List.append(&2, Tr.Ent, A, B), b) == True{} : Bool}:
  match A:
    case Nil{}:
      pb
    case +e <> +r:
      LBoolAnd.tree.pt.and_t(Nat.is_ge(b, Tr.Ent.p(e)), LABool.tc.ple(List.append(&2, Tr.Ent, r, B), b), LBoolAnd.tree.pt.and_l(Nat.is_ge(b, Tr.Ent.p(e)), LABool.tc.ple(r, b), pa), tc.ple_app(r, B, b, LBoolAnd.tree.pt.and_r(Nat.is_ge(b, Tr.Ent.p(e)), LABool.tc.ple(r, b), pa), pb))

# The nodes a delete of x may remove: its node, and the nodes with a
# parent of x or more

def tc.fx.at(c: Bool, +e: Tr.Ent, rest: List<&2, Tr.Ent>) -> List<&2, Tr.Ent>:
  match c:
    case True{}:
      e <> rest
    case False{}:
      rest

def tc.fx(t: List<&2, Tr.Ent>, +x: Nat) -> List<&2, Tr.Ent>:
  match t:
    case Nil{}:
      Nil{}
    case +e <> r:
      tc.fx.at(Bool.or(Nat.is_eq(Tr.Ent.k(e), x), Bool.not(Nat.is_lt(Tr.Ent.p(e), x))), e, tc.fx(r, x))

def tc.fx_at_app(c: Bool, +e: Tr.Ent, +X: List<&2, Tr.Ent>, +Y: List<&2, Tr.Ent>) -> {List.append(&2, Tr.Ent, tc.fx.at(c, e, X), Y) == tc.fx.at(c, e, List.append(&2, Tr.Ent, X, Y)) : List<&2, Tr.Ent>}:
  match c:
    case True{}:
      {==}
    case False{}:
      {==}

def tc.fx_app(A: List<&2, Tr.Ent>, +B: List<&2, Tr.Ent>, +x: Nat) -> {tc.fx(List.append(&2, Tr.Ent, A, B), x) == List.append(&2, Tr.Ent, tc.fx(A, x), tc.fx(B, x)) : List<&2, Tr.Ent>}:
  match A:
    case Nil{}:
      {==}
    case +e <> +r:
      +c = Bool.or(Nat.is_eq(Tr.Ent.k(e), x), Bool.not(Nat.is_lt(Tr.Ent.p(e), x)))
      +ih = tc.fx_app(r, B, x)
      %Equal.sym(List<&2, Tr.Ent>, tc.fx(List.append(&2, Tr.Ent, r, B), x), List.append(&2, Tr.Ent, tc.fx(r, x), tc.fx(B, x)), ih) : {tc.fx.at(c, e, _) == List.append(&2, Tr.Ent, tc.fx.at(c, e, tc.fx(r, x)), tc.fx(B, x)) : List<&2, Tr.Ent>}
      Equal.sym(List<&2, Tr.Ent>, List.append(&2, Tr.Ent, tc.fx.at(c, e, tc.fx(r, x)), tc.fx(B, x)), tc.fx.at(c, e, List.append(&2, Tr.Ent, tc.fx(r, x), tc.fx(B, x))), tc.fx_at_app(c, e, tc.fx(r, x), tc.fx(B, x)))

def tc.fx_drop(+e: Tr.Ent, +r: List<&2, Tr.Ent>, +x: Nat, +ne: {Nat.is_eq(Tr.Ent.k(e), x) == False{} : Bool}, +px: {Nat.is_lt(Tr.Ent.p(e), x) == True{} : Bool}) -> {tc.fx(e <> r, x) == tc.fx(r, x) : List<&2, Tr.Ent>}:
  %Equal.sym(Bool, Nat.is_eq(Tr.Ent.k(e), x), False{}, ne) : {tc.fx.at(Bool.or(_, Bool.not(Nat.is_lt(Tr.Ent.p(e), x))), e, tc.fx(r, x)) == tc.fx(r, x) : List<&2, Tr.Ent>}
  %Equal.sym(Bool, Nat.is_lt(Tr.Ent.p(e), x), True{}, px) : {tc.fx.at(Bool.or(False{}, Bool.not(_)), e, tc.fx(r, x)) == tc.fx(r, x) : List<&2, Tr.Ent>}
  {==}

# a list with no key x and every parent at most b below x has no node a
# delete of x may remove
def tc.fx_nil(t: List<&2, Tr.Ent>, +x: Nat, +b: Nat, +nk: {LABool.tc.nokey(t, x) == True{} : Bool}, +pb: {LABool.tc.ple(t, b) == True{} : Bool}, +bx: {Nat.is_lt(b, x) == True{} : Bool}) -> {tc.fx(t, x) == Nil{} : List<&2, Tr.Ent>}:
  match t:
    case Nil{}:
      {==}
    case +e <> +r:
      +ne = LBoolMisc.pt.not_f(Nat.is_eq(Tr.Ent.k(e), x), LBoolAnd.tree.pt.and_l(Bool.not(Nat.is_eq(Tr.Ent.k(e), x)), LABool.tc.nokey(r, x), nk))
      +px = LANat.tc.ge_lt(b, Tr.Ent.p(e), x, LBoolAnd.tree.pt.and_l(Nat.is_ge(b, Tr.Ent.p(e)), LABool.tc.ple(r, b), pb), bx)
      Equal.trans(List<&2, Tr.Ent>, tc.fx(e <> r, x), tc.fx(r, x), Nil{}, tc.fx_drop(e, r, x, ne, px), tc.fx_nil(r, x, b, LBoolAnd.tree.pt.and_r(Bool.not(Nat.is_eq(Tr.Ent.k(e), x)), LABool.tc.nokey(r, x), nk), LBoolAnd.tree.pt.and_r(Nat.is_ge(b, Tr.Ent.p(e)), LABool.tc.ple(r, b), pb), bx))

# The gone map
# the gone keys of a list, as the gone map holds them
def tc.bld(gone: List<&2, Nat>) -> List<&2, Tr.Ent>:
  match gone:
    case Nil{}:
      Nil{}
    case k <> rest:
      Tr.set(tc.bld(rest), Tr.Ent{k, 0n, 0n})

def tc.app_nil_rec(xs: List<&2, Tr.Rec>) -> {List.append(&2, Tr.Rec, xs, Nil{}) == xs : List<&2, Tr.Rec>}:
  match xs:
    case Nil{}:
      {==}
    case h <> t:
      Equal.cong(List<&2, Tr.Rec>, List<&2, Tr.Rec>, ys => h <> ys, List.append(&2, Tr.Rec, t, Nil{}), t, tc.app_nil_rec(t))

def tc.rev_app(xs: List<&2, Tr.Rec>, +a: List<&2, Tr.Rec>, +b: List<&2, Tr.Rec>) -> {List.reverse.go(&2, Tr.Rec, List.reverse.go(&2, Tr.Rec, xs, a), b) == List.reverse.go(&2, Tr.Rec, a, List.append(&2, Tr.Rec, xs, b)) : List<&2, Tr.Rec>}:
  match xs:
    case Nil{}:
      {==}
    case +h <> t:
      tc.rev_app(t, h <> a, b)

def tc.rev_rev(+xs: List<&2, Tr.Rec>) -> {List.reverse(&2, Tr.Rec, List.reverse.go(&2, Tr.Rec, xs, Nil{})) == xs : List<&2, Tr.Rec>}:
  Equal.trans(List<&2, Tr.Rec>, List.reverse.go(&2, Tr.Rec, List.reverse.go(&2, Tr.Rec, xs, Nil{}), Nil{}), List.append(&2, Tr.Rec, xs, Nil{}), xs, tc.rev_app(xs, Nil{}, Nil{}), tc.app_nil_rec(xs))

def pd.lt_all_app(A: List<&2, Tr.Ent>, +B: List<&2, Tr.Ent>, +m: Nat, +ha: {LABool.pd.lt_all(A, m) == True{} : Bool}, hb: {LABool.pd.lt_all(B, m) == True{} : Bool}) -> {LABool.pd.lt_all(List.append(&2, Tr.Ent, A, B), m) == True{} : Bool}:
  match A:
    case Nil{}:
      hb
    case +e <> +r:
      LBoolAnd.tree.pt.and_t(Nat.is_lt(Tr.Ent.k(e), m), LABool.pd.lt_all(List.append(&2, Tr.Ent, r, B), m), LBoolAnd.tree.pt.and_l(Nat.is_lt(Tr.Ent.k(e), m), LABool.pd.lt_all(r, m), ha), pd.lt_all_app(r, B, m, LBoolAnd.tree.pt.and_r(Nat.is_lt(Tr.Ent.k(e), m), LABool.pd.lt_all(r, m), ha), hb))
