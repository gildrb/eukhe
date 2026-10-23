# eukhe: the proof of LAW tree_delete_only_below

import Base
import ../../bend/tree.bend as Tr
import ../../laws/tree.bend as Tree
import ../base/bool/and.bend as LBoolAnd
import ../base/bool/misc.bend as LBoolMisc
import ../base/nat/is_eq.bend as LNatIsEq
import ../base/nat/is_lt.bend as LNatIsLt
import ../base/retry.bend as LRetry
import ./base/bool.bend as LABool
import ./base/list.bend as LAList
import ./base/nat.bend as LANat
import ./base/tree/above.bend as LATreeAbove
import ./base/tree/has.bend as LATreeHas
import ./base/tree/sorted.bend as LATreeSorted

# Delete: only below
# ------------------
# While prune walks the tree, every key in gone is x or below the rest
# of the walk, is not 0 (x is not the root; a node's key is above its
# parent's), and is not a key of the kept nodes; and every kept key is
# below the rest of the walk.

# f holds for every key of gone
def pt.All(gone: List<&2, Nat>, -f: Nat -> Bool) -> Data:
  match gone:
    case Nil{}:
      Unit
    case +g <> rest:
      Sigma<&2, &2, {f(g) == True{} : Bool}, _ => pt.All(rest, f)>

def pt.ah_go(+g: Nat, +gs: List<&2, Nat>, -f: Nat -> Bool, +y: Nat, c: Bool, ec: {Nat.is_eq(g, y) == c : Bool}, hd: {f(g) == True{} : Bool}, ih: {Tr.elem(gs, y) == True{} : Bool} -> {f(y) == True{} : Bool}, el: {Tr.elem(g <> gs, y) == True{} : Bool}) -> {f(y) == True{} : Bool}:
  match c:
    case True{}:
      %LANat.pt.eq_true(g, y, ec) : {f(_) == True{} : Bool}
      hd
    case False{}:
      ih(Equal.trans(Bool, Tr.elem(gs, y), Bool.or(Nat.is_eq(g, y), Tr.elem(gs, y)), True{}, Equal.cong(Bool, Bool, w => Bool.or(w, Tr.elem(gs, y)), False{}, Nat.is_eq(g, y), Equal.sym(Bool, Nat.is_eq(g, y), False{}, ec)), el))

def pt.all_hit(gone: List<&2, Nat>, -f: Nat -> Bool, +y: Nat, a: pt.All(gone, f)) -> {Tr.elem(gone, y) == True{} : Bool} -> {f(y) == True{} : Bool}:
  match gone:
    case Nil{}:
      el => LBoolMisc.tree.pt.absurdF({f(y) == True{} : Bool}, el)
    case +g <> +gs:
      (hd, tl) = a
      ih = pt.all_hit(gs, f, y, tl)
      el => pt.ah_go(g, gs, f, y, Nat.is_eq(g, y), {==}, hd, ih, el)

def pt.gl_tail(gone: List<&2, Nat>, +x: Nat, +e: Tr.Ent, +r: List<&2, Tr.Ent>, a: pt.All(gone, z => Bool.or(Nat.is_eq(z, x), Tr.above(z, e <> r))), +st: {Tr.sorted(e <> r) == True{} : Bool}) -> pt.All(gone, z => Bool.or(Nat.is_eq(z, x), Tr.above(z, r))):
  match gone:
    case Nil{}:
      Unit{}
    case +g <> +gs:
      (hd, tl) = a
      (LATreeAbove.pt.or_above_tail(Nat.is_eq(g, x), g, e, r, hd, st), pt.gl_tail(gs, x, e, r, tl, st))

def pt.not_has_app(+B: List<&2, Tr.Ent>, +C: List<&2, Tr.Ent>, +y: Nat, nb: {Tr.has(B, y) == False{} : Bool}, nc: {Tr.has(C, y) == False{} : Bool}) -> {Bool.not(Tr.has(List.append(&2, Tr.Ent, B, C), y)) == True{} : Bool}:
  %Equal.sym(Bool, Tr.has(List.append(&2, Tr.Ent, B, C), y), Bool.or(Tr.has(B, y), Tr.has(C, y)), LATreeHas.pt.has_app(B, C, y)) : {Bool.not(_) == True{} : Bool}
  %Equal.sym(Bool, Tr.has(B, y), False{}, nb) : {Bool.not(Bool.or(_, Tr.has(C, y))) == True{} : Bool}
  %Equal.sym(Bool, Tr.has(C, y), False{}, nc) : {Bool.not(Bool.or(False{}, _)) == True{} : Bool}
  {==}

def pt.ng_snoc(gone: List<&2, Nat>, +B: List<&2, Tr.Ent>, +e: Tr.Ent, a: pt.All(gone, z => Bool.not(Tr.has(B, z))), +ne: {Tr.elem(gone, Tr.Ent.k(e)) == False{} : Bool}) -> pt.All(gone, z => Bool.not(Tr.has(List.append(&2, Tr.Ent, B, [e]), z))):
  match gone:
    case Nil{}:
      Unit{}
    case +g <> +gs:
      (hd, tl) = a
      +ng = LABool.pt.or_l(Nat.is_eq(g, Tr.Ent.k(e)), Tr.elem(gs, Tr.Ent.k(e)), ne)
      +nc = LATreeHas.pt.has_miss(e, Nil{}, g, LNatIsEq.pt.ne_comm(g, Tr.Ent.k(e), ng))
      (pt.not_has_app(B, [e], g, LBoolMisc.pt.not_f(Tr.has(B, g), hd), nc), pt.ng_snoc(gs, B, e, tl, LABool.pt.or_r(Nat.is_eq(g, Tr.Ent.k(e)), Tr.elem(gs, Tr.Ent.k(e)), ne)))

# every kept node is below the rest of the walk
def pt.blw(B: List<&2, Tr.Ent>, +s: List<&2, Tr.Ent>) -> Bool:
  match B:
    case Nil{}:
      True{}
    case +b <> rest:
      Bool.and(Tr.above(Tr.Ent.k(b), s), pt.blw(rest, s))

def pt.blw_tail(B: List<&2, Tr.Ent>, +e: Tr.Ent, +r: List<&2, Tr.Ent>, +bw: {pt.blw(B, e <> r) == True{} : Bool}, +st: {Tr.sorted(e <> r) == True{} : Bool}) -> {pt.blw(B, r) == True{} : Bool}:
  match B:
    case Nil{}:
      {==}
    case +b <> +bs:
      +i = Tr.above(Tr.Ent.k(b), e <> r)
      LBoolAnd.tree.pt.and_t(Tr.above(Tr.Ent.k(b), r), pt.blw(bs, r), LATreeAbove.pt.above_tail(Tr.Ent.k(b), e, r, LBoolAnd.tree.pt.and_l(i, pt.blw(bs, e <> r), bw), st), pt.blw_tail(bs, e, r, LBoolAnd.tree.pt.and_r(i, pt.blw(bs, e <> r), bw), st))

def pt.blw_snoc(B: List<&2, Tr.Ent>, +e: Tr.Ent, +r: List<&2, Tr.Ent>, +bw: {pt.blw(B, r) == True{} : Bool}, +ae: {Tr.above(Tr.Ent.k(e), r) == True{} : Bool}) -> {pt.blw(List.append(&2, Tr.Ent, B, [e]), r) == True{} : Bool}:
  match B:
    case Nil{}:
      LBoolAnd.tree.pt.and_t(Tr.above(Tr.Ent.k(e), r), True{}, ae, {==})
    case +b <> +bs:
      +i = Tr.above(Tr.Ent.k(b), r)
      LBoolAnd.tree.pt.and_t(i, pt.blw(List.append(&2, Tr.Ent, bs, [e]), r), LBoolAnd.tree.pt.and_l(i, pt.blw(bs, r), bw), pt.blw_snoc(bs, e, r, LBoolAnd.tree.pt.and_r(i, pt.blw(bs, r), bw), ae))

def pt.blw_has(B: List<&2, Tr.Ent>, +e: Tr.Ent, +r: List<&2, Tr.Ent>, +bw: {pt.blw(B, e <> r) == True{} : Bool}) -> {Tr.has(B, Tr.Ent.k(e)) == False{} : Bool}:
  match B:
    case Nil{}:
      {==}
    case +b <> +bs:
      +i = Tr.above(Tr.Ent.k(b), e <> r)
      +ne = LNatIsEq.pt.lt_ne(Tr.Ent.k(b), Tr.Ent.k(e), LBoolAnd.tree.pt.and_l(i, pt.blw(bs, e <> r), bw))
      Equal.trans(Bool, Tr.has(b <> bs, Tr.Ent.k(e)), Tr.has(bs, Tr.Ent.k(e)), False{}, LATreeHas.pt.has_miss(b, bs, Tr.Ent.k(e), ne), pt.blw_has(bs, e, r, LBoolAnd.tree.pt.and_r(i, pt.blw(bs, e <> r), bw)))

# a key above a parent is not the root
def pt.lt_nz(+p: Nat, k: Nat, lt: {Nat.is_lt(p, k) == True{} : Bool}) -> {Bool.not(Nat.is_eq(k, 0n)) == True{} : Bool}:
  match k:
    case 0n:
      LNatIsLt.pt.lt_zero({Bool.not(Nat.is_eq(0n, 0n)) == True{} : Bool}, p, lt)
    case 1n+q:
      {==}

def pt.ob_drop(+gone: List<&2, Nat>, +x: Nat, +B: List<&2, Tr.Ent>, +e: Tr.Ent, +r: List<&2, Tr.Ent>, c: Bool, ec: {Tr.elem(gone, Tr.Ent.k(e)) == c : Bool}, +eh: {Bool.or(c, Tr.elem(gone, Tr.Ent.p(e))) == True{} : Bool}, +i1: pt.All(gone, z => Bool.or(Nat.is_eq(z, x), Tr.above(z, e <> r))), +i2: pt.All(gone, z => Bool.not(Nat.is_eq(z, 0n))), +i3: pt.All(gone, z => Bool.not(Tr.has(B, z))), +lt: {Nat.is_lt(Tr.Ent.p(e), Tr.Ent.k(e)) == True{} : Bool}, +st: {Tr.sorted(e <> r) == True{} : Bool}) -> {Bool.or(Nat.is_eq(Tr.Ent.k(e), x), Bool.and(Bool.not(Nat.is_eq(Tr.Ent.p(e), 0n)), Bool.not(Tr.has(List.append(&2, Tr.Ent, B, Tr.prune.go(r, Tr.Ent.k(e) <> gone, Tr.gone.at(r, Tr.Ent.k(e) <> gone))), Tr.Ent.p(e))))) == True{} : Bool}:
  match c:
    case True{}:
      +k = Tr.Ent.k(e)
      +p = Tr.Ent.p(e)
      +g2 = {k <> gone : List<&2, Nat>}
      +R = List.append(&2, Tr.Ent, B, Tr.prune.go(r, g2, Tr.gone.at(r, g2)))
      +d = Bool.and(Bool.not(Nat.is_eq(p, 0n)), Bool.not(Tr.has(R, p)))
      +h = pt.all_hit(gone, z => Bool.or(Nat.is_eq(z, x), Tr.above(z, e <> r)), k, i1)(ec)
      LABool.pt.or_tl(Nat.is_eq(k, x), d, LABool.pt.or_l_true(Nat.is_eq(k, x), Nat.is_lt(k, k), h, LNatIsLt.pt.lt_irrefl(k)))
    case False{}:
      +k = Tr.Ent.k(e)
      +p = Tr.Ent.p(e)
      +g2 = {k <> gone : List<&2, Nat>}
      +P = Tr.prune.go(r, g2, Tr.gone.at(r, g2))
      +R = List.append(&2, Tr.Ent, B, P)
      +d = Bool.and(Bool.not(Nat.is_eq(p, 0n)), Bool.not(Tr.has(R, p)))
      +nz = pt.all_hit(gone, z => Bool.not(Nat.is_eq(z, 0n)), p, i2)(eh)
      +nb = pt.all_hit(gone, z => Bool.not(Tr.has(B, z)), p, i3)(eh)
      +sr = LBoolAnd.tree.pt.and_r(Tr.above(k, r), Tr.sorted(r), st)
      +ap = LATreeAbove.pt.above_prune_go(r, g2, Tr.gone.at(r, g2), p, LATreeAbove.pt.above_lt(p, k, r, lt, LBoolAnd.tree.pt.and_l(Tr.above(k, r), Tr.sorted(r), st)), sr)
      +np = LATreeHas.pt.has_below(P, p, ap, LATreeSorted.pt.sorted_prune_go(r, g2, Tr.gone.at(r, g2), sr))
      LABool.pt.or_tr(Nat.is_eq(k, x), d, LBoolAnd.tree.pt.and_t(Bool.not(Nat.is_eq(p, 0n)), Bool.not(Tr.has(R, p)), nz, pt.not_has_app(B, P, p, LBoolMisc.pt.not_f(Tr.has(B, p), nb), np)))

def pt.ob_go(s: List<&2, Tr.Ent>, +gone: List<&2, Nat>, hit: Bool, eh: {Tr.gone.at(s, gone) == hit : Bool}, +x: Nat, +t: List<&2, Tr.Ent>, +B: List<&2, Tr.Ent>, +i1: pt.All(gone, z => Bool.or(Nat.is_eq(z, x), Tr.above(z, s))), +i2: pt.All(gone, z => Bool.not(Nat.is_eq(z, 0n))), +i3: pt.All(gone, z => Bool.not(Tr.has(B, z))), +bw: {pt.blw(B, s) == True{} : Bool}, +st: {Tr.sorted(s) == True{} : Bool}, +rs: {Tr.rooted.go(s, t) == True{} : Bool}) -> {Tr.only_below(s, x, List.append(&2, Tr.Ent, B, Tr.prune.go(s, gone, hit))) == True{} : Bool}:
  match s:
    case Nil{}:
      {==}
    case +e <> +r:
      match hit:
        case True{}:
          +k = Tr.Ent.k(e)
          +p = Tr.Ent.p(e)
          +g2 = {k <> gone : List<&2, Nat>}
          +R = List.append(&2, Tr.Ent, B, Tr.prune.go(r, g2, Tr.gone.at(r, g2)))
          +lt = LBoolAnd.tree.pt.and_l(Nat.is_lt(p, k), Bool.or(Nat.is_eq(p, 0n), Tr.has(t, p)), LBoolAnd.tree.pt.and_l(Tr.ok(t, k, p), Tr.rooted.go(r, t), rs))
          +ak = LBoolAnd.tree.pt.and_l(Tr.above(k, r), Tr.sorted(r), st)
          +hd = LABool.pt.or_tr(Tr.has(R, k), Bool.or(Nat.is_eq(k, x), Bool.and(Bool.not(Nat.is_eq(p, 0n)), Bool.not(Tr.has(R, p)))), pt.ob_drop(gone, x, B, e, r, Tr.elem(gone, k), {==}, eh, i1, i2, i3, lt, st))
          +j1 = {(LABool.pt.or_tr(Nat.is_eq(k, x), Tr.above(k, r), ak), pt.gl_tail(gone, x, e, r, i1, st)) : pt.All(g2, z => Bool.or(Nat.is_eq(z, x), Tr.above(z, r)))}
          +j2 = {(pt.lt_nz(p, k, lt), i2) : pt.All(g2, z => Bool.not(Nat.is_eq(z, 0n)))}
          +j3 = {(LBoolMisc.pt.not_t(Tr.has(B, k), pt.blw_has(B, e, r, bw)), i3) : pt.All(g2, z => Bool.not(Tr.has(B, z)))}
          +tl = pt.ob_go(r, g2, Tr.gone.at(r, g2), {==}, x, t, B, j1, j2, j3, pt.blw_tail(B, e, r, bw, st), LBoolAnd.tree.pt.and_r(Tr.above(k, r), Tr.sorted(r), st), LBoolAnd.tree.pt.and_r(Tr.ok(t, k, p), Tr.rooted.go(r, t), rs))
          LBoolAnd.tree.pt.and_t(Bool.or(Tr.has(R, k), Bool.or(Nat.is_eq(k, x), Bool.and(Bool.not(Nat.is_eq(p, 0n)), Bool.not(Tr.has(R, p))))), Tr.only_below(r, x, R), hd, tl)
        case False{}:
          +k = Tr.Ent.k(e)
          +p = Tr.Ent.p(e)
          +P = Tr.prune.go(r, gone, Tr.gone.at(r, gone))
          +R = List.append(&2, Tr.Ent, B, e <> P)
          +B2 = List.append(&2, Tr.Ent, B, [e])
          +ak = LBoolAnd.tree.pt.and_l(Tr.above(k, r), Tr.sorted(r), st)
          +hd = LABool.pt.or_tl(Tr.has(R, k), Bool.or(Nat.is_eq(k, x), Bool.and(Bool.not(Nat.is_eq(p, 0n)), Bool.not(Tr.has(R, p)))), LATreeHas.pt.has_app_r(B, e <> P, k, LATreeHas.pt.has_head(e, P)))
          +j3 = pt.ng_snoc(gone, B, e, i3, LABool.pt.or_l(Tr.elem(gone, k), Tr.elem(gone, p), eh))
          +bw2 = pt.blw_snoc(B, e, r, pt.blw_tail(B, e, r, bw, st), ak)
          +ih = pt.ob_go(r, gone, Tr.gone.at(r, gone), {==}, x, t, B2, pt.gl_tail(gone, x, e, r, i1, st), i2, j3, bw2, LBoolAnd.tree.pt.and_r(Tr.above(k, r), Tr.sorted(r), st), LBoolAnd.tree.pt.and_r(Tr.ok(t, k, p), Tr.rooted.go(r, t), rs))
          +tl = Equal.trans(Bool, Tr.only_below(r, x, R), Tr.only_below(r, x, List.append(&2, Tr.Ent, B2, P)), True{}, Equal.cong(List<&2, Tr.Ent>, Bool, l => Tr.only_below(r, x, l), R, List.append(&2, Tr.Ent, B2, P), Equal.sym(List<&2, Tr.Ent>, List.append(&2, Tr.Ent, B2, P), R, LAList.pt.app_snoc(B, e, P))), ih)
          LBoolAnd.tree.pt.and_t(Bool.or(Tr.has(R, k), Bool.or(Nat.is_eq(k, x), Bool.and(Bool.not(Nat.is_eq(p, 0n)), Bool.not(Tr.has(R, p))))), Tr.only_below(r, x, R), hd, tl)

# a prune of a node (not the root) removes only its subtree
def pt.only_below_nz(+t: List<&2, Tr.Ent>, +good: {Tr.sound(t) == True{} : Bool}, +x: Nat, nz: {Nat.is_eq(x, 0n) == False{} : Bool}) -> {Tr.only_below(t, x, Tr.prune(t, x)) == True{} : Bool}:
  +i1 = {(LABool.pt.or_tl(Nat.is_eq(x, x), Tr.above(x, t), Equal.sym(Bool, True{}, Nat.is_eq(x, x), LANat.pt.eq_refl(x))), Unit{}) : pt.All([x], z => Bool.or(Nat.is_eq(z, x), Tr.above(z, t)))}
  +i2 = {(LBoolMisc.pt.not_t(Nat.is_eq(x, 0n), nz), Unit{}) : pt.All([x], z => Bool.not(Nat.is_eq(z, 0n)))}
  +i3 = {({==}, Unit{}) : pt.All([x], z => Bool.not(Tr.has(Nil{}, z)))}
  pt.ob_go(t, [x], Tr.gone.at(t, [x]), {==}, x, t, Nil{}, i1, i2, i3, {==}, LBoolAnd.tree.pt.and_l(Tr.sorted(t), Tr.rooted(t), good), LBoolAnd.tree.pt.and_r(Tr.sorted(t), Tr.rooted(t), good))

# a tree that keeps every node drops none
def pt.ob_all(s: List<&2, Tr.Ent>, +x: Nat, +r: List<&2, Tr.Ent>, +ah: {LABool.pt.allhas(s, r) == True{} : Bool}) -> {Tr.only_below(s, x, r) == True{} : Bool}:
  match s:
    case Nil{}:
      {==}
    case +e <> +rest:
      +i = Tr.has(r, Tr.Ent.k(e))
      +o = Bool.or(Nat.is_eq(Tr.Ent.k(e), x), Bool.and(Bool.not(Nat.is_eq(Tr.Ent.p(e), 0n)), Bool.not(Tr.has(r, Tr.Ent.p(e)))))
      LBoolAnd.tree.pt.and_t(Bool.or(i, o), Tr.only_below(rest, x, r), LABool.pt.or_tl(i, o, LBoolAnd.tree.pt.and_l(i, LABool.pt.allhas(rest, r), ah)), pt.ob_all(rest, x, r, LBoolAnd.tree.pt.and_r(i, LABool.pt.allhas(rest, r), ah)))

# a delete of the root changes nothing; of a node, removes its subtree
def delete_only_below(+t: List<&2, Tr.Ent>, +good: {Tr.sound(t) == True{} : Bool}, +x: Nat) -> {Tr.only_below(t, x, Tr.apply(t, Tr.Do{Tr.Del{x}})) == True{} : Bool}:
  match x:
    case 0n:
      pt.ob_all(t, 0n, t, LATreeHas.pt.allhas_self(t))
    case 1n+y:
      pt.only_below_nz(t, good, 1n+y, {==})

def Tree.tree_delete_only_below(t, LRetry.good, x):
  delete_only_below(t, LRetry.good, x)
