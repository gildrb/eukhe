# eukhe: lemmas the proofs of area tree share: tree/sorted

import Base
import ../../../../bend/tree.bend as Tr
import ../../../base/bool/and.bend as LBoolAnd
import ../../../base/bool/misc.bend as LBoolMisc
import ../../../base/list.bend as LList
import ../../../base/nat/is_lt.bend as LNatIsLt
import ../../../base/tree.bend as LTree
import ../bool.bend as LABool
import ../list.bend as LAList
import ../nat.bend as LANat
import ./Ent.bend as LATreeEnt
import ./KMap.bend as LATreeKMap
import ./above.bend as LATreeAbove
import ./get.bend as LATreeGet
import ./has.bend as LATreeHas
import ./misc.bend as LATreeMisc
import ./rooted.bend as LATreeRooted

def pt.sorted_set_go(t: List<&2, Tr.Ent>, +e: Tr.Ent, c: Cmp, ec: {Tr.first(Tr.Ent.k(e), t) == c : Cmp}, +st: {Tr.sorted(t) == True{} : Bool}) -> {Tr.sorted(Tr.set.go(t, e, c)) == True{} : Bool}:
  match t:
    case Nil{}:
      {==}
    case +h <> +r:
      match c:
        case LT{}:
          LBoolAnd.tree.pt.and_t(Nat.is_lt(Tr.Ent.k(e), Tr.Ent.k(h)), Tr.sorted(h <> r), LANat.pt.cmp_lt(Tr.Ent.k(e), Tr.Ent.k(h), ec), st)
        case EQ{}:
          %Equal.sym(Nat, Tr.Ent.k(e), Tr.Ent.k(h), LANat.pt.cmp_eq(Tr.Ent.k(e), Tr.Ent.k(h), ec)) : {Bool.and(Tr.above(_, r), Tr.sorted(r)) == True{} : Bool}
          st
        case GT{}:
          +s = Tr.set.go(r, e, Tr.first(Tr.Ent.k(e), r))
          +al = LBoolAnd.tree.pt.and_l(Tr.above(Tr.Ent.k(h), r), Tr.sorted(r), st)
          +sr = LBoolAnd.tree.pt.and_r(Tr.above(Tr.Ent.k(h), r), Tr.sorted(r), st)
          LBoolAnd.tree.pt.and_t(Tr.above(Tr.Ent.k(h), s), Tr.sorted(s), LATreeAbove.pt.above_set_go(r, e, Tr.first(Tr.Ent.k(e), r), Tr.Ent.k(h), al, LANat.pt.cmp_gt(Tr.Ent.k(e), Tr.Ent.k(h), ec)), pt.sorted_set_go(r, e, Tr.first(Tr.Ent.k(e), r), {==}, sr))

def pt.sorted_unset_go(t: List<&2, Tr.Ent>, +x: Nat, hit: Bool, +st: {Tr.sorted(t) == True{} : Bool}) -> {Tr.sorted(Tr.unset.go(t, x, hit)) == True{} : Bool}:
  match t:
    case Nil{}:
      {==}
    case +h <> +r:
      match hit:
        case True{}:
          pt.sorted_unset_go(r, x, Tr.key.at(r, x), LBoolAnd.tree.pt.and_r(Tr.above(Tr.Ent.k(h), r), Tr.sorted(r), st))
        case False{}:
          +sr = LBoolAnd.tree.pt.and_r(Tr.above(Tr.Ent.k(h), r), Tr.sorted(r), st)
          +u = Tr.unset.go(r, x, Tr.key.at(r, x))
          LBoolAnd.tree.pt.and_t(Tr.above(Tr.Ent.k(h), u), Tr.sorted(u), LATreeAbove.pt.above_unset_go(r, x, Tr.key.at(r, x), Tr.Ent.k(h), LBoolAnd.tree.pt.and_l(Tr.above(Tr.Ent.k(h), r), Tr.sorted(r), st), sr), pt.sorted_unset_go(r, x, Tr.key.at(r, x), sr))

def pt.sorted_exact(+t: List<&2, Tr.Ent>, o: Tr.Op, st: {Tr.sorted(t) == True{} : Bool}) -> {Tr.sorted(Tr.exact(t, o)) == True{} : Bool}:
  match o:
    case Tr.Put{+k, +p, +v}:
      pt.sorted_set_go(t, Tr.Ent{k, p, v}, Tr.first(k, t), {==}, st)
    case Tr.Del{+x}:
      pt.sorted_unset_go(t, x, Tr.key.at(t, x), st)

def pt.sorted_patch(ops: List<&2, Tr.Op>, +t: List<&2, Tr.Ent>, st: {Tr.sorted(t) == True{} : Bool}) -> {Tr.sorted(Tr.patch(ops, t)) == True{} : Bool}:
  match ops:
    case Nil{}:
      st
    case +o <> rest:
      pt.sorted_patch(rest, Tr.exact(t, o), pt.sorted_exact(t, o, st))

def pt.sorted_app_r(A: List<&2, Tr.Ent>, +C: List<&2, Tr.Ent>, st: {Tr.sorted(List.append(&2, Tr.Ent, A, C)) == True{} : Bool}) -> {Tr.sorted(C) == True{} : Bool}:
  match A:
    case Nil{}:
      st
    case +a <> +r:
      pt.sorted_app_r(r, C, LBoolAnd.tree.pt.and_r(Tr.above(Tr.Ent.k(a), List.append(&2, Tr.Ent, r, C)), Tr.sorted(List.append(&2, Tr.Ent, r, C)), st))

def pt.put_sound(+t: List<&2, Tr.Ent>, +k: Nat, +p: Nat, +v: Nat, b: Bool, eb: {Tr.ok(t, k, p) == b : Bool}, +st: {Tr.sound(t) == True{} : Bool}) -> {Tr.sound(Tr.put.at(b, t, Tr.Ent{k, p, v})) == True{} : Bool}:
  match b:
    case True{}:
      +e = {Tr.Ent{k, p, v} : Tr.Ent}
      +s = Tr.set(t, e)
      LBoolAnd.tree.pt.and_t(Tr.sorted(s), Tr.rooted(s), pt.sorted_set_go(t, e, Tr.first(k, t), {==}, LBoolAnd.tree.pt.and_l(Tr.sorted(t), Tr.rooted(t), st)), LATreeRooted.pt.rooted_set_go(t, t, e, Tr.first(k, t), LBoolAnd.tree.pt.and_r(Tr.sorted(t), Tr.rooted(t), st), eb))
    case False{}:
      st

def pt.sorted_prune_go(t: List<&2, Tr.Ent>, +gone: List<&2, Nat>, hit: Bool, +st: {Tr.sorted(t) == True{} : Bool}) -> {Tr.sorted(Tr.prune.go(t, gone, hit)) == True{} : Bool}:
  match t:
    case Nil{}:
      {==}
    case +h <> +r:
      match hit:
        case True{}:
          +g2 = {Tr.Ent.k(h) <> gone : List<&2, Nat>}
          pt.sorted_prune_go(r, g2, Tr.gone.at(r, g2), LBoolAnd.tree.pt.and_r(Tr.above(Tr.Ent.k(h), r), Tr.sorted(r), st))
        case False{}:
          +sr = LBoolAnd.tree.pt.and_r(Tr.above(Tr.Ent.k(h), r), Tr.sorted(r), st)
          +u = Tr.prune.go(r, gone, Tr.gone.at(r, gone))
          LBoolAnd.tree.pt.and_t(Tr.above(Tr.Ent.k(h), u), Tr.sorted(u), LATreeAbove.pt.above_prune_go(r, gone, Tr.gone.at(r, gone), Tr.Ent.k(h), LBoolAnd.tree.pt.and_l(Tr.above(Tr.Ent.k(h), r), Tr.sorted(r), st), sr), pt.sorted_prune_go(r, gone, Tr.gone.at(r, gone), sr))

def pt.upl_of(s: List<&2, Tr.Ent>, +pre: List<&2, Tr.Ent>, +rs: {Tr.rooted.go(s, List.append(&2, Tr.Ent, pre, s)) == True{} : Bool}, +st: {Tr.sorted(List.append(&2, Tr.Ent, pre, s)) == True{} : Bool}) -> {LABool.pt.upl(s, pre) == True{} : Bool}:
  match s:
    case Nil{}:
      {==}
    case +e <> +r:
      +k = Tr.Ent.k(e)
      +p = Tr.Ent.p(e)
      +X = {e <> r : List<&2, Tr.Ent>}
      +A = List.append(&2, Tr.Ent, pre, X)
      +pre2 = List.append(&2, Tr.Ent, pre, [e])
      +oA = LBoolAnd.tree.pt.and_l(Tr.ok(A, k, p), Tr.rooted.go(r, A), rs)
      +lt = LBoolAnd.tree.pt.and_l(Nat.is_lt(p, k), Bool.or(Nat.is_eq(p, 0n), Tr.has(A, p)), oA)
      +hx = LATreeHas.pt.has_below(X, p, lt, pt.sorted_app_r(pre, X, st))
      +hp = Equal.trans(Bool, Tr.has(A, p), Bool.or(Tr.has(pre, p), Tr.has(X, p)), Tr.has(pre, p), LATreeHas.pt.has_app(pre, X, p), Equal.trans(Bool, Bool.or(Tr.has(pre, p), Tr.has(X, p)), Bool.or(Tr.has(pre, p), False{}), Tr.has(pre, p), Equal.cong(Bool, Bool, z => Bool.or(Tr.has(pre, p), z), Tr.has(X, p), False{}, hx), LABool.tree.pt.or_false_r(Tr.has(pre, p))))
      +okp = Equal.trans(Bool, Tr.ok(pre, k, p), Tr.ok(A, k, p), True{}, Equal.cong(Bool, Bool, z => Bool.and(Nat.is_lt(p, k), Bool.or(Nat.is_eq(p, 0n), z)), Tr.has(pre, p), Tr.has(A, p), Equal.sym(Bool, Tr.has(A, p), Tr.has(pre, p), hp)), oA)
      +eq = LAList.pt.app_snoc(pre, e, r)
      +rs2 = Equal.trans(Bool, Tr.rooted.go(r, List.append(&2, Tr.Ent, pre2, r)), Tr.rooted.go(r, A), True{}, Equal.cong(List<&2, Tr.Ent>, Bool, l => Tr.rooted.go(r, l), List.append(&2, Tr.Ent, pre2, r), A, eq), LBoolAnd.tree.pt.and_r(Tr.ok(A, k, p), Tr.rooted.go(r, A), rs))
      +st2 = Equal.trans(Bool, Tr.sorted(List.append(&2, Tr.Ent, pre2, r)), Tr.sorted(A), True{}, Equal.cong(List<&2, Tr.Ent>, Bool, l => Tr.sorted(l), List.append(&2, Tr.Ent, pre2, r), A, eq), st)
      LBoolAnd.tree.pt.and_t(Tr.ok(pre, k, p), LABool.pt.upl(r, pre2), okp, pt.upl_of(r, pre2, rs2, st2))

def pt.del_sound(+t: List<&2, Tr.Ent>, +x: Nat, +st: {Tr.sound(t) == True{} : Bool}) -> {Tr.sound(Tr.prune(t, x)) == True{} : Bool}:
  +R = Tr.prune(t, x)
  +so = LBoolAnd.tree.pt.and_l(Tr.sorted(t), Tr.rooted(t), st)
  +ro = LBoolAnd.tree.pt.and_r(Tr.sorted(t), Tr.rooted(t), st)
  LBoolAnd.tree.pt.and_t(Tr.sorted(R), Tr.rooted(R), pt.sorted_prune_go(t, [x], Tr.gone.at(t, [x]), so), LATreeRooted.pt.rooted_prune_go(t, [x], Tr.gone.at(t, [x]), {==}, Nil{}, Nil{}, {==}, pt.upl_of(t, Nil{}, ro, so)))

# The journal
# -----------

def apply_sound(+t: List<&2, Tr.Ent>, +good: {Tr.sound(t) == True{} : Bool}, r: Tr.Rec) -> {Tr.sound(Tr.apply(t, r)) == True{} : Bool}:
  match r:
    case Tr.Do{o}:
      match o:
        case Tr.Put{+k, +p, +v}:
          pt.put_sound(t, k, p, v, Tr.ok(t, k, p), {==}, good)
        case Tr.Del{+x}:
          match x:
            case 0n:
              good
            case 1n+y:
              pt.del_sound(t, 1n+y, good)
    case Tr.Rewind{+ops}:
      LATreeMisc.pt.keep_sound(t, Tr.patch(ops, t), Tr.sound(Tr.patch(ops, t)), {==}, good)

def pt.go_sound(rs: List<&2, Tr.Rec>, +t: List<&2, Tr.Ent>, +st: {Tr.sound(t) == True{} : Bool}) -> {Tr.sound(Tr.go(rs, t)) == True{} : Bool}:
  match rs:
    case Nil{}:
      st
    case +r <> rest:
      pt.go_sound(rest, Tr.apply(t, r), apply_sound(t, st, r))

def replay_sound(+rs: List<&2, Tr.Rec>) -> {Tr.sound(Tr.replay(rs)) == True{} : Bool}:
  pt.go_sound(rs, Nil{}, {==})

# two sorted lists that agree on their keys are equal
def pt.ext(l1: List<&2, Tr.Ent>, l2: List<&2, Tr.Ent>, +s1: {Tr.sorted(l1) == True{} : Bool}, +s2: {Tr.sorted(l2) == True{} : Bool}, A1: LAList.pt.Agree(l1, l1, l2), A2: LAList.pt.Agree(l2, l1, l2)) -> {l1 == l2 : List<&2, Tr.Ent>}:
  match l1 l2:
    case Nil{} Nil{}:
      {==}
    case Nil{} Con{+h2, +r2}:
      (e2, t2) = A2
      LATreeEnt.tree.pt.none_some({Nil{} == h2 <> r2 : List<&2, Tr.Ent>}, h2, Equal.trans(Maybe<&2, Tr.Ent>, None{}, Tr.get(h2 <> r2, Tr.Ent.k(h2)), Some{h2}, e2, LATreeGet.pt.get_head(h2, r2)))
    case Con{+h1, +r1} Nil{}:
      (e1, t1) = A1
      LATreeEnt.pt.some_none({h1 <> r1 == Nil{} : List<&2, Tr.Ent>}, h1, Equal.trans(Maybe<&2, Tr.Ent>, Some{h1}, Tr.get(h1 <> r1, Tr.Ent.k(h1)), None{}, Equal.sym(Maybe<&2, Tr.Ent>, Tr.get(h1 <> r1, Tr.Ent.k(h1)), Some{h1}, LATreeGet.pt.get_head(h1, r1)), e1))
    case Con{+h1, +r1} Con{+h2, +r2}:
      (+e1, t1) = A1
      (+e2, t2) = A2
      +keq = LATreeGet.pt.ext_head(h1, r1, h2, r2, Nat.cmp(Tr.Ent.k(h1), Tr.Ent.k(h2)), {==}, e1, e2, s1, s2)
      +s1t = LBoolAnd.tree.pt.and_r(Tr.above(Tr.Ent.k(h1), r1), Tr.sorted(r1), s1)
      +s2t = LBoolAnd.tree.pt.and_r(Tr.above(Tr.Ent.k(h2), r2), Tr.sorted(r2), s2)
      +al1 = LBoolAnd.tree.pt.and_l(Tr.above(Tr.Ent.k(h1), r1), Tr.sorted(r1), s1)
      +al2 = Equal.trans(Bool, Tr.above(Tr.Ent.k(h1), r2), Tr.above(Tr.Ent.k(h2), r2), True{}, Equal.cong(Nat, Bool, n => Tr.above(n, r2), Tr.Ent.k(h1), Tr.Ent.k(h2), keq), LBoolAnd.tree.pt.and_l(Tr.above(Tr.Ent.k(h2), r2), Tr.sorted(r2), s2))
      +ih = pt.ext(r1, r2, s1t, s2t, LATreeGet.pt.agree_strip(r1, h1, r1, h2, r2, t1, al1, s1t, keq), LATreeGet.pt.agree_strip(r2, h1, r1, h2, r2, t2, al2, s2t, keq))
      +hs = Equal.trans(Maybe<&2, Tr.Ent>, Some{h1}, Tr.get(h1 <> r1, Tr.Ent.k(h1)), Some{h2}, Equal.sym(Maybe<&2, Tr.Ent>, Tr.get(h1 <> r1, Tr.Ent.k(h1)), Some{h1}, LATreeGet.pt.get_head(h1, r1)), Equal.trans(Maybe<&2, Tr.Ent>, Tr.get(h1 <> r1, Tr.Ent.k(h1)), Tr.get(h2 <> r2, Tr.Ent.k(h1)), Some{h2}, e1, LATreeGet.pt.get_hit(h2, r2, Tr.Ent.k(h1), LANat.pt.eq_of(Tr.Ent.k(h1), Tr.Ent.k(h2), keq))))
      %LATreeEnt.tree.pt.some_inj(h1, h2, hs) : {h1 <> r1 == _ <> r2 : List<&2, Tr.Ent>}
      %ih : {h1 <> r1 == h1 <> _ : List<&2, Tr.Ent>}
      {==}

def rewind_reaches(+a: List<&2, Tr.Ent>, +b: List<&2, Tr.Ent>, ga: {Tr.sound(a) == True{} : Bool}, +gb: {Tr.sound(b) == True{} : Bool}) -> {Tr.apply(a, Tr.Rewind{Tr.diff(a, b)}) == b : List<&2, Tr.Ent>}:
  +n = Tr.patch(Tr.diff(a, b), a)
  +sb = LBoolAnd.tree.pt.and_l(Tr.sorted(b), Tr.rooted(b), gb)
  +sn = pt.sorted_patch(Tr.diff(a, b), a, LBoolAnd.tree.pt.and_l(Tr.sorted(a), Tr.rooted(a), ga))
  +eq = pt.ext(n, b, sn, sb, LATreeGet.pt.agree_reach(n, a, b, sb), LATreeGet.pt.agree_reach(b, a, b, sb))
  %Equal.sym(List<&2, Tr.Ent>, n, b, eq) : {Tr.keep.at(Tr.sound(_), a, _) == b : List<&2, Tr.Ent>}
  %Equal.sym(Bool, Tr.sound(b), True{}, gb) : {Tr.keep.at(_, a, b) == b : List<&2, Tr.Ent>}
  {==}

def tc.sorted_app(A: List<&2, Tr.Ent>, +B: List<&2, Tr.Ent>, +b: Nat, +sa: {Tr.sorted(A) == True{} : Bool}, +sb: {Tr.sorted(B) == True{} : Bool}, +la: {LBoolMisc.tc.lt(A, b) == True{} : Bool}, +gb: {LBoolMisc.tc.ge(B, b) == True{} : Bool}) -> {Tr.sorted(List.append(&2, Tr.Ent, A, B)) == True{} : Bool}:
  match A:
    case Nil{}:
      sb
    case +e <> +r:
      +ar = LBoolAnd.tree.pt.and_l(Tr.above(Tr.Ent.k(e), r), Tr.sorted(r), sa)
      +sr = LBoolAnd.tree.pt.and_r(Tr.above(Tr.Ent.k(e), r), Tr.sorted(r), sa)
      +R = List.append(&2, Tr.Ent, r, B)
      LBoolAnd.tree.pt.and_t(Tr.above(Tr.Ent.k(e), R), Tr.sorted(R), LATreeAbove.tc.above_app(Tr.Ent.k(e), r, B, b, ar, LNatIsLt.tc.lt_head(e, r, b, la), gb), tc.sorted_app(r, B, b, sr, sb, LBoolAnd.tc.lt_tail(e, r, b, la), gb))

# The key map: order, lookup, put, unset

def tc.sorted_read(m: Tr.KMap, +bt: {LBoolMisc.tc.bst(m) == True{} : Bool}) -> {Tr.sorted(Tr.KMap.read(m)) == True{} : Bool}:
  match m:
    case Tr.KNil{}:
      {==}
    case Tr.KOne{e}:
      {==}
    case Tr.KFork{+mid, +mp, +l, +r}:
      tc.sorted_app(Tr.KMap.read(l), Tr.KMap.read(r), mid, tc.sorted_read(l, LTree.tc.bst_l(mid, mp, l, r, bt)), tc.sorted_read(r, LTree.tc.bst_r(mid, mp, l, r, bt)), LTree.tc.bst_lt(mid, mp, l, r, bt), LTree.tc.bst_ge(mid, mp, l, r, bt))

def tc.gb_tail(gone: List<&2, Nat>, +x: Nat, +e: Tr.Ent, +r: List<&2, Tr.Ent>, +g: {LABool.tc.gb(gone, x, e <> r) == True{} : Bool}, +st: {Tr.sorted(e <> r) == True{} : Bool}) -> {LABool.tc.gb(gone, x, r) == True{} : Bool}:
  match gone:
    case Nil{}:
      {==}
    case +z <> +rest:
      +hd = LBoolAnd.tree.pt.and_l(Bool.or(Nat.is_eq(z, x), Tr.above(z, e <> r)), LABool.tc.gb(rest, x, e <> r), g)
      +tl = LBoolAnd.tree.pt.and_r(Bool.or(Nat.is_eq(z, x), Tr.above(z, e <> r)), LABool.tc.gb(rest, x, e <> r), g)
      LBoolAnd.tree.pt.and_t(Bool.or(Nat.is_eq(z, x), Tr.above(z, r)), LABool.tc.gb(rest, x, r), LATreeAbove.pt.or_above_tail(Nat.is_eq(z, x), z, e, r, hd, st), tc.gb_tail(rest, x, e, r, tl, st))

# a delete's walk over the nodes it may remove drops the keys of the walk
# over every node
def tc.drops_fx(s: List<&2, Tr.Ent>, +gone: List<&2, Nat>, hit: Bool, +eh: {Tr.gone.at(s, gone) == hit : Bool}, +x: Nat, +ng: {LABool.tc.nall(gone, x) == True{} : Bool}, +g: {LABool.tc.gb(gone, x, s) == True{} : Bool}, +st: {Tr.sorted(s) == True{} : Bool}, +dk: {LABool.tc.desc(s) == True{} : Bool}) -> {LAList.tc.dgo(s, gone, hit) == LAList.tc.dgo(LAList.tc.fx(s, x), gone, Tr.gone.at(LAList.tc.fx(s, x), gone)) : List<&2, Nat>}:
  match s:
    case Nil{}:
      {==}
    case +e <> +r:
      +pk = LBoolAnd.tree.pt.and_l(Nat.is_lt(Tr.Ent.p(e), Tr.Ent.k(e)), LABool.tc.desc(r), dk)
      +dr = LBoolAnd.tree.pt.and_r(Nat.is_lt(Tr.Ent.p(e), Tr.Ent.k(e)), LABool.tc.desc(r), dk)
      +sr = LBoolAnd.tree.pt.and_r(Tr.above(Tr.Ent.k(e), r), Tr.sorted(r), st)
      +ar = LBoolAnd.tree.pt.and_l(Tr.above(Tr.Ent.k(e), r), Tr.sorted(r), st)
      +g1 = tc.gb_tail(gone, x, e, r, g, st)
      +g2 = LBoolAnd.tree.pt.and_t(Bool.or(Nat.is_eq(Tr.Ent.k(e), x), Tr.above(Tr.Ent.k(e), r)), LABool.tc.gb(gone, x, r), LABool.pt.or_tr(Nat.is_eq(Tr.Ent.k(e), x), Tr.above(Tr.Ent.k(e), r), ar), g1)
      +ih1 = tc.drops_fx(r, gone, Tr.gone.at(r, gone), {==}, x, ng, g1, sr, dr)
      LATreeEnt.tc.fd_at(e, r, gone, hit, eh, x, Bool.or(Nat.is_eq(Tr.Ent.k(e), x), Bool.not(Nat.is_lt(Tr.Ent.p(e), x))), {==}, ng, g, pk, ih1, kx => tc.drops_fx(r, Tr.Ent.k(e) <> gone, Tr.gone.at(r, Tr.Ent.k(e) <> gone), {==}, x, LANat.tc.nall_cons(Tr.Ent.k(e), gone, x, kx, ng), g2, sr, dr))

# the test of a rewind on the map is sound on the list
def tc.good_rewind(+ops: List<&2, Tr.Op>, +hs: List<&2, Nat>, +m: Tr.KMap, +bt: {LBoolMisc.tc.bst(m) == True{} : Bool}) -> {Tr.KMap.hangs(Tr.KMap.onto(Tr.KMap.patch(ops, hs, m), Nil{}), Tr.KMap.patch(ops, hs, m)) == Tr.sound(Tr.patch(ops, Tr.KMap.read(m))) : Bool}:
  +n = Tr.KMap.patch(ops, hs, m)
  +bn = LTree.tc.patch_bst(ops, hs, m, bt)
  +N = Tr.KMap.read(n)
  %Equal.sym(List<&2, Tr.Ent>, Tr.KMap.onto(n, Nil{}), N, LATreeKMap.tc.onto_nil(n)) : {Tr.KMap.hangs(_, n) == Tr.sound(Tr.patch(ops, Tr.KMap.read(m))) : Bool}
  %Equal.sym(Bool, Tr.KMap.hangs(N, n), Tr.rooted.go(N, N), LATreeGet.tc.hangs(N, n, bn)) : {_ == Tr.sound(Tr.patch(ops, Tr.KMap.read(m))) : Bool}
  %LATreeKMap.tc.patch_read(ops, hs, m, bt) : {Tr.rooted.go(N, N) == Tr.sound(_) : Bool}
  %Equal.sym(Bool, Tr.sorted(N), True{}, tc.sorted_read(n, bn)) : {Tr.rooted.go(N, N) == Bool.and(_, Tr.rooted(N)) : Bool}
  {==}

# the keys a delete of x cuts on the map are the keys the walk drops
def tc.del_keys(+m: Tr.KMap, +x: Nat, +bt: {LBoolMisc.tc.bst(m) == True{} : Bool}, +mk: {LABool.tc.mpok(m) == True{} : Bool}, +sd: {Tr.sound(Tr.KMap.read(m)) == True{} : Bool}) -> {LAList.tc.dgo(Tr.KMap.ups(m, x, Nil{}, Tr.KMap.gl(m, x), Tr.KMap.gr(m, x)), [x], Tr.gone.at(Tr.KMap.ups(m, x, Nil{}, Tr.KMap.gl(m, x), Tr.KMap.gr(m, x)), [x])) == LAList.tc.dgo(Tr.KMap.read(m), [x], Tr.gone.at(Tr.KMap.read(m), [x])) : List<&2, Nat>}:
  +t = Tr.KMap.read(m)
  +U = Tr.KMap.ups(m, x, Nil{}, Tr.KMap.gl(m, x), Tr.KMap.gr(m, x))
  +rf = Equal.trans(List<&2, Tr.Ent>, U, List.append(&2, Tr.Ent, LAList.tc.fx(t, x), Nil{}), LAList.tc.fx(t, x), LATreeKMap.tc.ups_read(m, x, Nil{}, Tr.KMap.gl(m, x), Tr.KMap.gr(m, x), {==}, {==}, bt, mk), LList.tc.app_nil(LAList.tc.fx(t, x)))
  +ng = LBoolAnd.tree.pt.and_t(Bool.not(Nat.is_lt(x, x)), True{}, LBoolMisc.pt.not_t(Nat.is_lt(x, x), LNatIsLt.pt.lt_irrefl(x)), {==})
  +g = LBoolAnd.tree.pt.and_t(Bool.or(Nat.is_eq(x, x), Tr.above(x, t)), True{}, LABool.pt.or_tl(Nat.is_eq(x, x), Tr.above(x, t), Equal.sym(Bool, True{}, Nat.is_eq(x, x), LANat.pt.eq_refl(x))), {==})
  +dk = LATreeRooted.tc.desc_of(t, t, LBoolAnd.tree.pt.and_r(Tr.sorted(t), Tr.rooted(t), sd))
  %Equal.sym(List<&2, Tr.Ent>, U, LAList.tc.fx(t, x), rf) : {LAList.tc.dgo(_, [x], Tr.gone.at(_, [x])) == LAList.tc.dgo(t, [x], Tr.gone.at(t, [x])) : List<&2, Nat>}
  Equal.sym(List<&2, Nat>, LAList.tc.dgo(t, [x], Tr.gone.at(t, [x])), LAList.tc.dgo(LAList.tc.fx(t, x), [x], Tr.gone.at(LAList.tc.fx(t, x), [x])), tc.drops_fx(t, [x], Tr.gone.at(t, [x]), {==}, x, ng, g, tc.sorted_read(m, bt), dk))

def tc.rec_read(+m: Tr.KMap, +hs: List<&2, Nat>, r: Tr.Rec, +bt: {LBoolMisc.tc.bst(m) == True{} : Bool}, +mk: {LABool.tc.mpok(m) == True{} : Bool}, +sd: {Tr.sound(Tr.KMap.read(m)) == True{} : Bool}) -> {Tr.KMap.read(Pair.fst(Tr.KMap, Tr.Ans, Tr.KMap.rec(m, hs, r))) == Tr.apply(Tr.KMap.read(m), r) : List<&2, Tr.Ent>}:
  match r:
    case Tr.Do{o}:
      match o:
        case Tr.Put{+k, +p, +v}:
          +e = {Tr.Ent{k, p, v} : Tr.Ent}
          +G = Bool.and(Nat.is_lt(p, k), Bool.or(Nat.is_eq(p, 0n), Tr.KMap.has(m, p)))
          %Equal.sym(Bool, G, Tr.ok(Tr.KMap.read(m), k, p), LATreeGet.tc.good_put(m, k, p, bt)) : {Tr.KMap.read(Pair.fst(Tr.KMap, Tr.Ans, Tr.put.ans(_, m, hs, e))) == Tr.put.at(Tr.ok(Tr.KMap.read(m), k, p), Tr.KMap.read(m), e) : List<&2, Tr.Ent>}
          LATreeKMap.tc.put_case(Tr.ok(Tr.KMap.read(m), k, p), m, hs, e, bt)
        case Tr.Del{x}:
          match x:
            case 0n:
              {==}
            case 1n++y:
              +t = Tr.KMap.read(m)
              +F = Tr.KMap.ups(m, 1n+y, Nil{}, Tr.KMap.gl(m, 1n+y), Tr.KMap.gr(m, 1n+y))
              +KS = Tr.drops(F, hs, 1n+y)
              +K2 = LAList.tc.dgo(F, [1n+y], Tr.gone.at(F, [1n+y]))
              +D = LAList.tc.dgo(t, [1n+y], Tr.gone.at(t, [1n+y]))
              +s1 = LATreeKMap.tc.drop_read(KS, m, bt)
              +s2 = Equal.cong(List<&2, Nat>, List<&2, Tr.Ent>, z => LAList.tc.unsets(z, t), KS, D, Equal.trans(List<&2, Nat>, KS, K2, D, LATreeHas.tc.drops(F, hs, 1n+y), tc.del_keys(m, 1n+y, bt, mk, sd)))
              +s3 = LATreeAbove.tc.unsets_drops(t, [1n+y], Tr.gone.at(t, [1n+y]), tc.sorted_read(m, bt))
              Equal.trans(List<&2, Tr.Ent>, Tr.KMap.read(Tr.KMap.drop(KS, m)), LAList.tc.unsets(KS, t), Tr.prune(t, 1n+y), s1, Equal.trans(List<&2, Tr.Ent>, LAList.tc.unsets(KS, t), LAList.tc.unsets(D, t), Tr.prune(t, 1n+y), s2, s3))
    case Tr.Rewind{+ops}:
      +n = Tr.KMap.patch(ops, hs, m)
      +G = Tr.KMap.hangs(Tr.KMap.onto(n, Nil{}), n)
      +N = Tr.patch(ops, Tr.KMap.read(m))
      %Equal.sym(Bool, G, Tr.sound(N), tc.good_rewind(ops, hs, m, bt)) : {Tr.KMap.read(Pair.fst(Tr.KMap, Tr.Ans, Tr.keep.ans(_, m, n))) == Tr.keep.at(Tr.sound(N), Tr.KMap.read(m), N) : List<&2, Tr.Ent>}
      LATreeKMap.tc.keep_case(Tr.sound(N), m, n, N, LATreeKMap.tc.patch_read(ops, hs, m, bt))

def tc.go_read(rs: List<&2, Tr.Rec>, +hs: List<&2, Nat>, +m: Tr.KMap, +bt: {LBoolMisc.tc.bst(m) == True{} : Bool}, +mk: {LABool.tc.mpok(m) == True{} : Bool}, +sd: {Tr.sound(Tr.KMap.read(m)) == True{} : Bool}) -> {Tr.KMap.read(Tr.KMap.go(rs, hs, m)) == Tr.go(rs, Tr.KMap.read(m)) : List<&2, Tr.Ent>}:
  match rs:
    case Nil{}:
      {==}
    case +r <> rest:
      +m2 = Pair.fst(Tr.KMap, Tr.Ans, Tr.KMap.rec(m, hs, r))
      +rr = tc.rec_read(m, hs, r, bt, mk, sd)
      +s2 = Equal.trans(Bool, Tr.sound(Tr.KMap.read(m2)), Tr.sound(Tr.apply(Tr.KMap.read(m), r)), True{}, Equal.cong(List<&2, Tr.Ent>, Bool, z => Tr.sound(z), Tr.KMap.read(m2), Tr.apply(Tr.KMap.read(m), r), rr), apply_sound(Tr.KMap.read(m), sd, r))
      %rr : {Tr.KMap.read(Tr.KMap.go(rest, hs, m2)) == Tr.go(rest, _) : List<&2, Tr.Ent>}
      tc.go_read(rest, hs, m2, LTree.tc.rec_bst(m, hs, r, bt), LATreeKMap.tc.rec_mpok(m, hs, r, mk), s2)

def tc.live_read(+hs: List<&2, Nat>, +rs: List<&2, Tr.Rec>) -> {Tr.KMap.read(Tr.KMap.go(rs, hs, Tr.KNil{})) == Tr.replay(rs) : List<&2, Tr.Ent>}:
  tc.go_read(rs, hs, Tr.KNil{}, {==}, {==}, {==})

# the map after the first n records of the journal log of rs
def tc.at_read(+hs: List<&2, Nat>, +rs: List<&2, Tr.Rec>, +n: Nat) -> {Tr.KMap.read(Tr.St.at(List.reverse.go(&2, Tr.Rec, rs, Nil{}), hs, n)) == Tr.replay(List.take(&2, Tr.Rec, rs, n)) : List<&2, Tr.Ent>}:
  %Equal.sym(List<&2, Tr.Rec>, List.reverse(&2, Tr.Rec, List.reverse.go(&2, Tr.Rec, rs, Nil{})), rs, LAList.tc.rev_rev(rs)) : {Tr.KMap.read(Tr.KMap.go(List.take(&2, Tr.Rec, _, n), hs, Tr.KNil{})) == Tr.replay(List.take(&2, Tr.Rec, rs, n)) : List<&2, Tr.Ent>}
  tc.live_read(hs, List.take(&2, Tr.Rec, rs, n))

# a sorted list, then sorted nodes above all its keys, is sorted
def pd.sorted_snoc(A: List<&2, Tr.Ent>, +x: Tr.Ent, +C: List<&2, Tr.Ent>, +sa: {Tr.sorted(A) == True{} : Bool}, sc: {Tr.sorted(x <> C) == True{} : Bool}, +la: {LABool.pd.lt_all(A, Tr.Ent.k(x)) == True{} : Bool}) -> {Tr.sorted(List.append(&2, Tr.Ent, A, x <> C)) == True{} : Bool}:
  match A:
    case Nil{}:
      sc
    case +e <> +r:
      +sr = LBoolAnd.tree.pt.and_r(Tr.above(Tr.Ent.k(e), r), Tr.sorted(r), sa)
      +lr = LBoolAnd.tree.pt.and_r(Nat.is_lt(Tr.Ent.k(e), Tr.Ent.k(x)), LABool.pd.lt_all(r, Tr.Ent.k(x)), la)
      LBoolAnd.tree.pt.and_t(Tr.above(Tr.Ent.k(e), List.append(&2, Tr.Ent, r, x <> C)), Tr.sorted(List.append(&2, Tr.Ent, r, x <> C)), LATreeAbove.pd.above_app(e, r, x, C, sa, la), pd.sorted_snoc(r, x, C, sr, sc, lr))
