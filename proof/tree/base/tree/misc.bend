# eukhe: lemmas the proofs of area tree share: tree/misc

import Base
import ../../../../bend/tree.bend as Tr
import ../../../base/bool/and.bend as LBoolAnd
import ../../../base/bool/misc.bend as LBoolMisc
import ../../../base/nat/is_eq.bend as LNatIsEq
import ../../../base/nat/is_lt.bend as LNatIsLt
import ../bool.bend as LABool
import ../list.bend as LAList
import ../maybe.bend as LAMaybe
import ../nat.bend as LANat
import ../pair.bend as LAPair

def pt.keep_sound(+t: List<&2, Tr.Ent>, +n: List<&2, Tr.Ent>, b: Bool, eb: {Tr.sound(n) == b : Bool}, st: {Tr.sound(t) == True{} : Bool}) -> {Tr.sound(Tr.keep.at(b, t, n)) == True{} : Bool}:
  match b:
    case True{}:
      eb
    case False{}:
      st

def pt.dels_none(s: List<&2, Tr.Ent>, +b: List<&2, Tr.Ent>, hit: Bool, +x: Nat) -> {LAMaybe.pt.look(Tr.dels.go(s, b, hit), None{}, x) == None{} : Maybe<&2, Tr.Ent>}:
  match s:
    case Nil{}:
      {==}
    case +e <> +r:
      match hit:
        case True{}:
          pt.dels_none(r, b, Tr.held.at(r, b), x)
        case False{}:
          +c = Nat.is_eq(Tr.Ent.k(e), x)
          %Equal.sym(Maybe<&2, Tr.Ent>, LAMaybe.tree.pt.pick(c, None{}, None{}), None{}, LAMaybe.pt.pick_same(c, None{})) : {LAMaybe.pt.look(Tr.dels.go(r, b, Tr.held.at(r, b)), _, x) == None{} : Maybe<&2, Tr.Ent>}
          pt.dels_none(r, b, Tr.held.at(r, b), x)

# the dels leave a key the target holds
def pt.dels_keep(s: List<&2, Tr.Ent>, +b: List<&2, Tr.Ent>, hit: Bool, eh: {Tr.held.at(s, b) == hit : Bool}, +m: Maybe<&2, Tr.Ent>, +x: Nat, +hb: {Tr.has(b, x) == True{} : Bool}) -> {LAMaybe.pt.look(Tr.dels.go(s, b, hit), m, x) == m : Maybe<&2, Tr.Ent>}:
  match s:
    case Nil{}:
      {==}
    case +e <> +r:
      match hit:
        case True{}:
          pt.dels_keep(r, b, Tr.held.at(r, b), {==}, m, x, hb)
        case False{}:
          +ne = LANat.pt.ne_by(Tr.Ent.k(e), x, z => Tr.has(b, z), eh, hb)
          %Equal.sym(Bool, Nat.is_eq(Tr.Ent.k(e), x), False{}, ne) : {LAMaybe.pt.look(Tr.dels.go(r, b, Tr.held.at(r, b)), LAMaybe.tree.pt.pick(_, None{}, m), x) == m : Maybe<&2, Tr.Ent>}
          pt.dels_keep(r, b, Tr.held.at(r, b), {==}, m, x, hb)

def tc.elem_none(gone: List<&2, Nat>, +x: Nat, +y: Nat, +ng: {LABool.tc.nall(gone, x) == True{} : Bool}, +yx: {Nat.is_lt(y, x) == True{} : Bool}) -> {Tr.elem(gone, y) == False{} : Bool}:
  match gone:
    case Nil{}:
      {==}
    case +g <> +rest:
      +gx = LBoolMisc.pt.not_f(Nat.is_lt(g, x), LBoolAnd.tree.pt.and_l(Bool.not(Nat.is_lt(g, x)), LABool.tc.nall(rest, x), ng))
      +ne = LNatIsEq.pt.lt_ne_r(y, g, LNatIsLt.tc.lt_le(y, x, g, yx, gx))
      %Equal.sym(Bool, Nat.is_eq(g, y), False{}, ne) : {Bool.or(_, Tr.elem(rest, y)) == False{} : Bool}
      tc.elem_none(rest, x, y, LBoolAnd.tree.pt.and_r(Bool.not(Nat.is_lt(g, x)), LABool.tc.nall(rest, x), ng), yx)

def tc.dg_ge(hit: Bool, +e: Tr.Ent, +r: List<&2, Tr.Ent>, +X: List<&2, Tr.Ent>, +gone: List<&2, Nat>, +ih1: {LAList.tc.dgo(r, gone, Tr.gone.at(r, gone)) == LAList.tc.dgo(X, gone, Tr.gone.at(X, gone)) : List<&2, Nat>}, ih2: {LAList.tc.dgo(r, Tr.Ent.k(e) <> gone, Tr.gone.at(r, Tr.Ent.k(e) <> gone)) == LAList.tc.dgo(X, Tr.Ent.k(e) <> gone, Tr.gone.at(X, Tr.Ent.k(e) <> gone)) : List<&2, Nat>}) -> {LAList.tc.dgo(e <> r, gone, hit) == LAList.tc.dgo(e <> X, gone, hit) : List<&2, Nat>}:
  match hit:
    case True{}:
      Equal.cong(List<&2, Nat>, List<&2, Nat>, ys => Tr.Ent.k(e) <> ys, LAList.tc.dgo(r, Tr.Ent.k(e) <> gone, Tr.gone.at(r, Tr.Ent.k(e) <> gone)), LAList.tc.dgo(X, Tr.Ent.k(e) <> gone, Tr.gone.at(X, Tr.Ent.k(e) <> gone)), ih2)
    case False{}:
      ih1

def tc.mpok_l(+mid: Nat, +mp: Nat, +l: Tr.KMap, +r: Tr.KMap, +h: {LABool.tc.mpok(Tr.KFork{mid, mp, l, r}) == True{} : Bool}) -> {LABool.tc.mpok(l) == True{} : Bool}:
  LBoolAnd.tree.pt.and_l(LABool.tc.mpok(l), Bool.and(LABool.tc.mpok(r), Bool.and(Nat.is_ge(mp, Tr.KMap.mp(l)), Nat.is_ge(mp, Tr.KMap.mp(r)))), h)

def tc.mpok_r(+mid: Nat, +mp: Nat, +l: Tr.KMap, +r: Tr.KMap, +h: {LABool.tc.mpok(Tr.KFork{mid, mp, l, r}) == True{} : Bool}) -> {LABool.tc.mpok(r) == True{} : Bool}:
  LBoolAnd.tree.pt.and_l(LABool.tc.mpok(r), Bool.and(Nat.is_ge(mp, Tr.KMap.mp(l)), Nat.is_ge(mp, Tr.KMap.mp(r))), LABool.tc.mpok_rest(mid, mp, l, r, h))

# a key that is not x is not gone, while gone holds x and keys below it
def tc.gb_elem(gone: List<&2, Nat>, +x: Nat, +e: Tr.Ent, +r: List<&2, Tr.Ent>, +g: {LABool.tc.gb(gone, x, e <> r) == True{} : Bool}, +kx: {Nat.is_eq(Tr.Ent.k(e), x) == False{} : Bool}) -> {Tr.elem(gone, Tr.Ent.k(e)) == False{} : Bool}:
  match gone:
    case Nil{}:
      {==}
    case +z <> +rest:
      +hd = LBoolAnd.tree.pt.and_l(Bool.or(Nat.is_eq(z, x), Tr.above(z, e <> r)), LABool.tc.gb(rest, x, e <> r), g)
      +tl = LBoolAnd.tree.pt.and_r(Bool.or(Nat.is_eq(z, x), Tr.above(z, e <> r)), LABool.tc.gb(rest, x, e <> r), g)
      +ne = LANat.tc.gb_hd(Nat.is_eq(z, x), z, x, Tr.Ent.k(e), {==}, hd, kx)
      %Equal.sym(Bool, Nat.is_eq(z, Tr.Ent.k(e)), False{}, ne) : {Bool.or(_, Tr.elem(rest, Tr.Ent.k(e))) == False{} : Bool}
      tc.gb_elem(rest, x, e, r, tl, kx)

def tc.feed_go(rs: List<&2, Tr.Rec>, +m: Tr.KMap, +log: List<&2, Tr.Rec>, +hs: List<&2, Nat>) -> {Tr.core.feed.go(rs, Tr.St{m, log, hs}) == Tr.St{Tr.KMap.go(rs, hs, m), List.reverse.go(&2, Tr.Rec, rs, log), hs} : Tr.St}:
  match rs:
    case Nil{}:
      {==}
    case +r <> rest:
      +m2 = Pair.fst(Tr.KMap, Tr.Ans, Tr.KMap.rec(m, hs, r))
      %Equal.sym(Tr.St, Pair.fst(Tr.St, Tr.Ans, Tr.St.note(log, r, hs, Tr.KMap.rec(m, hs, r))), Tr.St{m2, r <> log, hs}, LAPair.tc.note_fst(log, r, hs, Tr.KMap.rec(m, hs, r))) : {Tr.core.feed.go(rest, _) == Tr.St{Tr.KMap.go(rest, hs, m2), List.reverse.go(&2, Tr.Rec, rest, r <> log), hs} : Tr.St}
      tc.feed_go(rest, m2, r <> log, hs)

# the stepper after a journal
def tc.feed(+hs: List<&2, Nat>, +rs: List<&2, Tr.Rec>) -> {Tr.core.feed(hs, rs) == Tr.St{Tr.KMap.go(rs, hs, Tr.KNil{}), List.reverse.go(&2, Tr.Rec, rs, Nil{}), hs} : Tr.St}:
  tc.feed_go(rs, Tr.KNil{}, Nil{}, hs)
