# eukhe: lemmas the proofs of area tree share: tree/unset

import Base
import ../../../../bend/tree.bend as Tr
import ../../../base/logic/bool.bend as LLogicBool
import ../../../base/nat.bend as LNat
import ../../../base/tree.bend as LTree
import ../list.bend as LAList
import ../logic.bend as LALogic
import ../nat.bend as LANat
import ./KMap.bend as LATreeKMap
import ./above.bend as LATreeAbove
import ./get.bend as LATreeGet
import ./has.bend as LATreeHas
import ./put.bend as LATreePut
import ./sorted.bend as LATreeSorted
import ./sound.bend as LATreeSound

# an unset of a key below every key of r keeps r
def tc.unset_above(r: List<&2, Tr.Ent>, +k: Nat, +ar: {Tr.above(k, r) == True{} : Bool}, +sr: {Tr.sorted(r) == True{} : Bool}) -> {Tr.unset(r, k) == r : List<&2, Tr.Ent>}:
  match r:
    case Nil{}:
      {==}
    case +f <> +r2:
      +ne = LNat.pt.lt_ne_r(k, Tr.Ent.k(f), ar)
      +af = LLogicBool.tree.pt.and_l(Tr.above(Tr.Ent.k(f), r2), Tr.sorted(r2), sr)
      +sr2 = LLogicBool.tree.pt.and_r(Tr.above(Tr.Ent.k(f), r2), Tr.sorted(r2), sr)
      %Equal.sym(Bool, Nat.is_eq(Tr.Ent.k(f), k), False{}, ne) : {Tr.unset.go(f <> r2, k, _) == f <> r2 : List<&2, Tr.Ent>}
      Equal.cong(List<&2, Tr.Ent>, List<&2, Tr.Ent>, ys => f <> ys, Tr.unset(r2, k), r2, tc.unset_above(r2, k, LATreeAbove.pt.above_lt(k, Tr.Ent.k(f), r2, ar, af), sr2))

# unsetting the keys a walk drops is the walk's prune
def tc.unsets_drops(t: List<&2, Tr.Ent>, +gone: List<&2, Nat>, hit: Bool, +st: {Tr.sorted(t) == True{} : Bool}) -> {LALogic.tc.unsets(LALogic.tc.dgo(t, gone, hit), t) == Tr.prune.go(t, gone, hit) : List<&2, Tr.Ent>}:
  match t:
    case Nil{}:
      {==}
    case +e <> +r:
      match hit:
        case True{}:
          +ar = LLogicBool.tree.pt.and_l(Tr.above(Tr.Ent.k(e), r), Tr.sorted(r), st)
          +sr = LLogicBool.tree.pt.and_r(Tr.above(Tr.Ent.k(e), r), Tr.sorted(r), st)
          +g2 = {Tr.Ent.k(e) <> gone : List<&2, Nat>}
          +D = LALogic.tc.dgo(r, g2, Tr.gone.at(r, g2))
          %Equal.sym(Bool, Nat.is_eq(Tr.Ent.k(e), Tr.Ent.k(e)), True{}, Equal.sym(Bool, True{}, Nat.is_eq(Tr.Ent.k(e), Tr.Ent.k(e)), LANat.pt.eq_refl(Tr.Ent.k(e)))) : {LALogic.tc.unsets(D, Tr.unset.go(e <> r, Tr.Ent.k(e), _)) == Tr.prune.go(r, g2, Tr.gone.at(r, g2)) : List<&2, Tr.Ent>}
          %Equal.sym(List<&2, Tr.Ent>, Tr.unset(r, Tr.Ent.k(e)), r, tc.unset_above(r, Tr.Ent.k(e), ar, sr)) : {LALogic.tc.unsets(D, _) == Tr.prune.go(r, g2, Tr.gone.at(r, g2)) : List<&2, Tr.Ent>}
          tc.unsets_drops(r, g2, Tr.gone.at(r, g2), sr)
        case False{}:
          +ar = LLogicBool.tree.pt.and_l(Tr.above(Tr.Ent.k(e), r), Tr.sorted(r), st)
          +sr = LLogicBool.tree.pt.and_r(Tr.above(Tr.Ent.k(e), r), Tr.sorted(r), st)
          +D = LALogic.tc.dgo(r, gone, Tr.gone.at(r, gone))
          +gt = LATreeAbove.tc.drops_gt(r, gone, Tr.gone.at(r, gone), Tr.Ent.k(e), ar, sr)
          Equal.trans(List<&2, Tr.Ent>, LALogic.tc.unsets(D, e <> r), e <> LALogic.tc.unsets(D, r), e <> Tr.prune.go(r, gone, Tr.gone.at(r, gone)), LALogic.tc.unsets_cons(D, e, r, gt), Equal.cong(List<&2, Tr.Ent>, List<&2, Tr.Ent>, ys => e <> ys, LALogic.tc.unsets(D, r), Tr.prune.go(r, gone, Tr.gone.at(r, gone)), tc.unsets_drops(r, gone, Tr.gone.at(r, gone), sr)))

def tc.rec_read(+m: Tr.KMap, +hs: List<&2, Nat>, r: Tr.Rec, +bt: {LLogicBool.tc.bst(m) == True{} : Bool}, +mk: {LALogic.tc.mpok(m) == True{} : Bool}, +sd: {Tr.sound(Tr.KMap.read(m)) == True{} : Bool}) -> {Tr.KMap.read(Pair.fst(Tr.KMap, Tr.Ans, Tr.KMap.rec(m, hs, r))) == Tr.apply(Tr.KMap.read(m), r) : List<&2, Tr.Ent>}:
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
              +K2 = LALogic.tc.dgo(F, [1n+y], Tr.gone.at(F, [1n+y]))
              +D = LALogic.tc.dgo(t, [1n+y], Tr.gone.at(t, [1n+y]))
              +s1 = LATreeKMap.tc.drop_read(KS, m, bt)
              +s2 = Equal.cong(List<&2, Nat>, List<&2, Tr.Ent>, z => LALogic.tc.unsets(z, t), KS, D, Equal.trans(List<&2, Nat>, KS, K2, D, LATreeHas.tc.drops(F, hs, 1n+y), LATreeSorted.tc.del_keys(m, 1n+y, bt, mk, sd)))
              +s3 = tc.unsets_drops(t, [1n+y], Tr.gone.at(t, [1n+y]), LATreeSorted.tc.sorted_read(m, bt))
              Equal.trans(List<&2, Tr.Ent>, Tr.KMap.read(Tr.KMap.drop(KS, m)), LALogic.tc.unsets(KS, t), Tr.prune(t, 1n+y), s1, Equal.trans(List<&2, Tr.Ent>, LALogic.tc.unsets(KS, t), LALogic.tc.unsets(D, t), Tr.prune(t, 1n+y), s2, s3))
    case Tr.Rewind{+ops}:
      +n = Tr.KMap.patch(ops, hs, m)
      +G = Tr.KMap.hangs(Tr.KMap.onto(n, Nil{}), n)
      +N = Tr.patch(ops, Tr.KMap.read(m))
      %Equal.sym(Bool, G, Tr.sound(N), LATreeSorted.tc.good_rewind(ops, hs, m, bt)) : {Tr.KMap.read(Pair.fst(Tr.KMap, Tr.Ans, Tr.keep.ans(_, m, n))) == Tr.keep.at(Tr.sound(N), Tr.KMap.read(m), N) : List<&2, Tr.Ent>}
      LATreeKMap.tc.keep_case(Tr.sound(N), m, n, N, LATreeKMap.tc.patch_read(ops, hs, m, bt))

def tc.go_read(rs: List<&2, Tr.Rec>, +hs: List<&2, Nat>, +m: Tr.KMap, +bt: {LLogicBool.tc.bst(m) == True{} : Bool}, +mk: {LALogic.tc.mpok(m) == True{} : Bool}, +sd: {Tr.sound(Tr.KMap.read(m)) == True{} : Bool}) -> {Tr.KMap.read(Tr.KMap.go(rs, hs, m)) == Tr.go(rs, Tr.KMap.read(m)) : List<&2, Tr.Ent>}:
  match rs:
    case Nil{}:
      {==}
    case +r <> rest:
      +m2 = Pair.fst(Tr.KMap, Tr.Ans, Tr.KMap.rec(m, hs, r))
      +rr = tc.rec_read(m, hs, r, bt, mk, sd)
      +s2 = Equal.trans(Bool, Tr.sound(Tr.KMap.read(m2)), Tr.sound(Tr.apply(Tr.KMap.read(m), r)), True{}, Equal.cong(List<&2, Tr.Ent>, Bool, z => Tr.sound(z), Tr.KMap.read(m2), Tr.apply(Tr.KMap.read(m), r), rr), LATreeSound.apply_sound(Tr.KMap.read(m), sd, r))
      %rr : {Tr.KMap.read(Tr.KMap.go(rest, hs, m2)) == Tr.go(rest, _) : List<&2, Tr.Ent>}
      tc.go_read(rest, hs, m2, LTree.tc.rec_bst(m, hs, r, bt), LATreePut.tc.rec_mpok(m, hs, r, mk), s2)

def tc.live_read(+hs: List<&2, Nat>, +rs: List<&2, Tr.Rec>) -> {Tr.KMap.read(Tr.KMap.go(rs, hs, Tr.KNil{})) == Tr.replay(rs) : List<&2, Tr.Ent>}:
  tc.go_read(rs, hs, Tr.KNil{}, {==}, {==}, {==})

# the map after the first n records of the journal log of rs
def tc.at_read(+hs: List<&2, Nat>, +rs: List<&2, Tr.Rec>, +n: Nat) -> {Tr.KMap.read(Tr.St.at(List.reverse.go(&2, Tr.Rec, rs, Nil{}), hs, n)) == Tr.replay(List.take(&2, Tr.Rec, rs, n)) : List<&2, Tr.Ent>}:
  %Equal.sym(List<&2, Tr.Rec>, List.reverse(&2, Tr.Rec, List.reverse.go(&2, Tr.Rec, rs, Nil{})), rs, LAList.tc.rev_rev(rs)) : {Tr.KMap.read(Tr.KMap.go(List.take(&2, Tr.Rec, _, n), hs, Tr.KNil{})) == Tr.replay(List.take(&2, Tr.Rec, rs, n)) : List<&2, Tr.Ent>}
  tc.live_read(hs, List.take(&2, Tr.Rec, rs, n))
