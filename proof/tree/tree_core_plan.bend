# eukhe: the proof of LAW tree_core_plan

import Base
import ../../bend/tree.bend as Tr
import ../../laws/tree.bend as Tree
import ../base/bool.bend as LBool
import ../base/logic/bool.bend as LLogicBool
import ../base/nat.bend as LNat
import ./base/tree/KMap.bend as LATreeKMap
import ./base/tree/above.bend as LATreeAbove
import ./base/tree/core.bend as LATreeCore
import ./base/tree/get.bend as LATreeGet
import ./base/tree/has.bend as LATreeHas
import ./base/tree/sound.bend as LATreeSound
import ./base/tree/unset.bend as LATreeUnset

# The plan: the merge is diff

def tc.from_sorted(s: List<&2, Tr.Ent>, +k: Nat, lo: Bool, +st: {Tr.sorted(s) == True{} : Bool}) -> {Tr.sorted(Tr.from.go(s, k, lo)) == True{} : Bool}:
  match s:
    case Nil{}:
      {==}
    case +e <> +rest:
      match lo:
        case True{}:
          tc.from_sorted(rest, k, Tr.below.at(rest, k), LLogicBool.tree.pt.and_r(Tr.above(Tr.Ent.k(e), rest), Tr.sorted(rest), st))
        case False{}:
          st

def tc.from_get(s: List<&2, Tr.Ent>, +k: Nat, lo: Bool, +elo: {Tr.below.at(s, k) == lo : Bool}, +y: Nat, +yk: {Nat.is_lt(y, k) == False{} : Bool}) -> {Tr.get(Tr.from.go(s, k, lo), y) == Tr.get(s, y) : Maybe<&2, Tr.Ent>}:
  match s:
    case Nil{}:
      {==}
    case +e <> +rest:
      match lo:
        case True{}:
          +ne = LNat.pt.lt_ne(Tr.Ent.k(e), y, LNat.tc.lt_le(Tr.Ent.k(e), k, y, elo, yk))
          Equal.trans(Maybe<&2, Tr.Ent>, Tr.get(Tr.from.go(rest, k, Tr.below.at(rest, k)), y), Tr.get(rest, y), Tr.get(e <> rest, y), tc.from_get(rest, k, Tr.below.at(rest, k), {==}, y, yk), Equal.sym(Maybe<&2, Tr.Ent>, Tr.get(e <> rest, y), Tr.get(rest, y), LATreeGet.pt.get_miss(e, rest, y, ne)))
        case False{}:
          {==}

def tc.from_has(+s: List<&2, Tr.Ent>, +k: Nat, +y: Nat, +yk: {Nat.is_lt(y, k) == False{} : Bool}) -> {Tr.has(Tr.from.k(s, k), y) == Tr.has(s, y) : Bool}:
  Equal.cong(Maybe<&2, Tr.Ent>, Bool, z => Maybe.is_some(&2, Tr.Ent, z), Tr.get(Tr.from.k(s, k), y), Tr.get(s, y), tc.from_get(s, k, Tr.below.at(s, k), {==}, y, yk))

# the first key of c is k or more
def tc.headge(c: List<&2, Tr.Ent>, +k: Nat) -> Bool:
  match c:
    case Nil{}:
      True{}
    case +f <> r:
      Bool.not(Nat.is_lt(Tr.Ent.k(f), k))

def tc.from_head(s: List<&2, Tr.Ent>, +k: Nat, lo: Bool, +elo: {Tr.below.at(s, k) == lo : Bool}) -> {tc.headge(Tr.from.go(s, k, lo), k) == True{} : Bool}:
  match s:
    case Nil{}:
      {==}
    case +e <> +rest:
      match lo:
        case True{}:
          tc.from_head(rest, k, Tr.below.at(rest, k), {==})
        case False{}:
          LBool.pt.not_t(Nat.is_lt(Tr.Ent.k(e), k), elo)

def tc.hh_at(+f: Tr.Ent, +r: List<&2, Tr.Ent>, +k: Nat, b: Bool, +eb: {Nat.is_eq(Tr.Ent.k(f), k) == b : Bool}, +hg: {Nat.is_lt(Tr.Ent.k(f), k) == False{} : Bool}, +sc: {Tr.sorted(f <> r) == True{} : Bool}) -> {Bool.or(b, Tr.has(r, k)) == b : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      +lt = LNat.tc.lt_total(Tr.Ent.k(f), k, hg, eb)
      +ar = LATreeAbove.pt.above_lt(k, Tr.Ent.k(f), r, lt, LLogicBool.tree.pt.and_l(Tr.above(Tr.Ent.k(f), r), Tr.sorted(r), sc))
      LATreeHas.pt.has_below(r, k, ar, LLogicBool.tree.pt.and_r(Tr.above(Tr.Ent.k(f), r), Tr.sorted(r), sc))

# in a sorted list whose first key is k or more, k is held only at the head
def tc.has_head(c: List<&2, Tr.Ent>, +k: Nat, +hg: {tc.headge(c, k) == True{} : Bool}, +sc: {Tr.sorted(c) == True{} : Bool}) -> {Tr.has(c, k) == Tr.key.at(c, k) : Bool}:
  match c:
    case Nil{}:
      {==}
    case +f <> +r:
      +b = Nat.is_eq(Tr.Ent.k(f), k)
      Equal.trans(Bool, Tr.has(f <> r, k), Bool.or(b, Tr.has(r, k)), b, LATreeHas.pt.has_cons(f, r, k), tc.hh_at(f, r, k, b, {==}, LLogicBool.pt.not_f(Nat.is_lt(Tr.Ent.k(f), k), hg), sc))

def tc.ent_eq_ne(f: Tr.Ent, e: Tr.Ent, +ne: {Nat.is_eq(Tr.Ent.k(f), Tr.Ent.k(e)) == False{} : Bool}) -> {Tr.Ent.eq(f, e) == False{} : Bool}:
  match f e:
    case Tr.Ent{fk, fp, fv} Tr.Ent{ek, ep, ev}:
      %Equal.sym(Bool, Nat.is_eq(fk, ek), False{}, ne) : {Bool.and(_, Bool.and(Nat.is_eq(fp, ep), Nat.is_eq(fv, ev))) == False{} : Bool}
      {==}

def tc.hs_at(+f: Tr.Ent, +r: List<&2, Tr.Ent>, +e: Tr.Ent, b: Bool, +eb: {Nat.is_eq(Tr.Ent.k(f), Tr.Ent.k(e)) == b : Bool}, +hg: {Nat.is_lt(Tr.Ent.k(f), Tr.Ent.k(e)) == False{} : Bool}, +sc: {Tr.sorted(f <> r) == True{} : Bool}) -> {Tr.Ent.eq(f, e) == Tr.same(Tr.get.go(f <> r, Tr.Ent.k(e), b), Some{e}) : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      +lt = LNat.tc.lt_total(Tr.Ent.k(f), Tr.Ent.k(e), hg, eb)
      +ar = LATreeAbove.pt.above_lt(Tr.Ent.k(e), Tr.Ent.k(f), r, lt, LLogicBool.tree.pt.and_l(Tr.above(Tr.Ent.k(f), r), Tr.sorted(r), sc))
      +gn = LATreeGet.pt.get_below(r, Tr.Ent.k(e), ar, LLogicBool.tree.pt.and_r(Tr.above(Tr.Ent.k(f), r), Tr.sorted(r), sc))
      %Equal.sym(Maybe<&2, Tr.Ent>, Tr.get(r, Tr.Ent.k(e)), None{}, gn) : {Tr.Ent.eq(f, e) == Tr.same(_, Some{e}) : Bool}
      tc.ent_eq_ne(f, e, eb)

# in a sorted list whose first key is e's or more, e is held only at the head
def tc.head_same(c: List<&2, Tr.Ent>, +e: Tr.Ent, +hg: {tc.headge(c, Tr.Ent.k(e)) == True{} : Bool}, +sc: {Tr.sorted(c) == True{} : Bool}) -> {Tr.head.same(c, e) == Tr.same(Tr.get(c, Tr.Ent.k(e)), Some{e}) : Bool}:
  match c:
    case Nil{}:
      {==}
    case +f <> +r:
      tc.hs_at(f, r, e, Nat.is_eq(Tr.Ent.k(f), Tr.Ent.k(e)), {==}, LLogicBool.pt.not_f(Nat.is_lt(Tr.Ent.k(f), Tr.Ent.k(e)), hg), sc)

def tc.ge_above(r: List<&2, Tr.Ent>, +k: Nat, +ar: {Tr.above(k, r) == True{} : Bool}, +sr: {Tr.sorted(r) == True{} : Bool}) -> {LLogicBool.tc.ge(r, k) == True{} : Bool}:
  match r:
    case Nil{}:
      {==}
    case +f <> +r2:
      +af = LLogicBool.tree.pt.and_l(Tr.above(Tr.Ent.k(f), r2), Tr.sorted(r2), sr)
      +sr2 = LLogicBool.tree.pt.and_r(Tr.above(Tr.Ent.k(f), r2), Tr.sorted(r2), sr)
      LBool.tc.ge_cons(f, r2, k, LNat.tc.lt_asym(k, Tr.Ent.k(f), ar), tc.ge_above(r2, k, LATreeAbove.pt.above_lt(k, Tr.Ent.k(f), r2, ar, af), sr2))

def tc.dc_at(hit: Bool, +f: Tr.Ent, +s2: List<&2, Tr.Ent>, +c: List<&2, Tr.Ent>, +b: List<&2, Tr.Ent>, +ih: {Tr.dels.go(s2, c, Tr.held.at(s2, c)) == Tr.dels.go(s2, b, Tr.held.at(s2, b)) : List<&2, Tr.Op>}) -> {Tr.dels.go(f <> s2, c, hit) == Tr.dels.go(f <> s2, b, hit) : List<&2, Tr.Op>}:
  match hit:
    case True{}:
      ih
    case False{}:
      Equal.cong(List<&2, Tr.Op>, List<&2, Tr.Op>, ys => Tr.Del{Tr.Ent.k(f)} <> ys, Tr.dels.go(s2, c, Tr.held.at(s2, c)), Tr.dels.go(s2, b, Tr.held.at(s2, b)), ih)

# dels reads b only at the keys of s, all k or more
def tc.dels_cong(s: List<&2, Tr.Ent>, +b: List<&2, Tr.Ent>, +k: Nat, +gs: {LLogicBool.tc.ge(s, k) == True{} : Bool}) -> {Tr.dels.go(s, Tr.from.k(b, k), Tr.held.at(s, Tr.from.k(b, k))) == Tr.dels.go(s, b, Tr.held.at(s, b)) : List<&2, Tr.Op>}:
  match s:
    case Nil{}:
      {==}
    case +f <> +s2:
      +c = Tr.from.k(b, k)
      +fh = tc.from_has(b, k, Tr.Ent.k(f), LNat.tc.ge_head(f, s2, k, gs))
      %Equal.sym(Bool, Tr.has(c, Tr.Ent.k(f)), Tr.has(b, Tr.Ent.k(f)), fh) : {Tr.dels.go(f <> s2, c, _) == Tr.dels.go(f <> s2, b, Tr.has(b, Tr.Ent.k(f))) : List<&2, Tr.Op>}
      tc.dc_at(Tr.has(b, Tr.Ent.k(f)), f, s2, c, b, tc.dels_cong(s2, b, k, LLogicBool.tc.ge_tail(f, s2, k, gs)))

def tc.dm_at(hit: Bool, +e: Tr.Ent, +rest: List<&2, Tr.Ent>, +b: List<&2, Tr.Ent>) -> {Tr.dels.m.at(hit, Tr.Ent.k(e), Tr.dels.go(rest, b, Tr.held.at(rest, b))) == Tr.dels.go(e <> rest, b, hit) : List<&2, Tr.Op>}:
  match hit:
    case True{}:
      {==}
    case False{}:
      {==}

def tc.dels_m(a: List<&2, Tr.Ent>, +b: List<&2, Tr.Ent>, +sa: {Tr.sorted(a) == True{} : Bool}, +sb: {Tr.sorted(b) == True{} : Bool}) -> {Tr.dels.m(a, b) == Tr.dels(a, b) : List<&2, Tr.Op>}:
  match a:
    case Nil{}:
      {==}
    case +e <> +rest:
      +k = Tr.Ent.k(e)
      +c = Tr.from.k(b, k)
      +sc = tc.from_sorted(b, k, Tr.below.at(b, k), sb)
      +ar = LLogicBool.tree.pt.and_l(Tr.above(k, rest), Tr.sorted(rest), sa)
      +sr = LLogicBool.tree.pt.and_r(Tr.above(k, rest), Tr.sorted(rest), sa)
      +D = Tr.dels.go(rest, b, Tr.held.at(rest, b))
      +e1 = Equal.trans(List<&2, Tr.Op>, Tr.dels.m(rest, c), Tr.dels(rest, c), D, tc.dels_m(rest, c, sr, sc), tc.dels_cong(rest, b, k, tc.ge_above(rest, k, ar, sr)))
      +e2 = Equal.trans(Bool, Tr.key.at(c, k), Tr.has(c, k), Tr.has(b, k), Equal.sym(Bool, Tr.has(c, k), Tr.key.at(c, k), tc.has_head(c, k, tc.from_head(b, k, Tr.below.at(b, k), {==}), sc)), tc.from_has(b, k, k, LNat.pt.lt_irrefl(k)))
      %Equal.sym(List<&2, Tr.Op>, Tr.dels.m(rest, c), D, e1) : {Tr.dels.m.at(Tr.key.at(c, k), k, _) == Tr.dels.go(e <> rest, b, Tr.has(b, k)) : List<&2, Tr.Op>}
      %Equal.sym(Bool, Tr.key.at(c, k), Tr.has(b, k), e2) : {Tr.dels.m.at(_, k, D) == Tr.dels.go(e <> rest, b, Tr.has(b, k)) : List<&2, Tr.Op>}
      tc.dm_at(Tr.has(b, k), e, rest, b)

def tc.pc_at(hit: Bool, +a: List<&2, Tr.Ent>, +c: List<&2, Tr.Ent>, +f: Tr.Ent, +s2: List<&2, Tr.Ent>, +ih: {Tr.puts.go(c, s2, Tr.kept.at(c, s2)) == Tr.puts.go(a, s2, Tr.kept.at(a, s2)) : List<&2, Tr.Op>}) -> {Tr.puts.go(c, f <> s2, hit) == Tr.puts.go(a, f <> s2, hit) : List<&2, Tr.Op>}:
  match hit:
    case True{}:
      ih
    case False{}:
      Equal.cong(List<&2, Tr.Op>, List<&2, Tr.Op>, ys => Tr.Put{Tr.Ent.k(f), Tr.Ent.p(f), Tr.Ent.v(f)} <> ys, Tr.puts.go(c, s2, Tr.kept.at(c, s2)), Tr.puts.go(a, s2, Tr.kept.at(a, s2)), ih)

# puts reads a only at the keys of s, all k or more
def tc.puts_cong(s: List<&2, Tr.Ent>, +a: List<&2, Tr.Ent>, +k: Nat, +gs: {LLogicBool.tc.ge(s, k) == True{} : Bool}) -> {Tr.puts.go(Tr.from.k(a, k), s, Tr.kept.at(Tr.from.k(a, k), s)) == Tr.puts.go(a, s, Tr.kept.at(a, s)) : List<&2, Tr.Op>}:
  match s:
    case Nil{}:
      {==}
    case +f <> +s2:
      +c = Tr.from.k(a, k)
      +fg = tc.from_get(a, k, Tr.below.at(a, k), {==}, Tr.Ent.k(f), LNat.tc.ge_head(f, s2, k, gs))
      %Equal.sym(Maybe<&2, Tr.Ent>, Tr.get(c, Tr.Ent.k(f)), Tr.get(a, Tr.Ent.k(f)), fg) : {Tr.puts.go(c, f <> s2, Tr.same(_, Some{f})) == Tr.puts.go(a, f <> s2, Tr.same(Tr.get(a, Tr.Ent.k(f)), Some{f})) : List<&2, Tr.Op>}
      tc.pc_at(Tr.same(Tr.get(a, Tr.Ent.k(f)), Some{f}), a, c, f, s2, tc.puts_cong(s2, a, k, LLogicBool.tc.ge_tail(f, s2, k, gs)))

def tc.pm_at(hit: Bool, +e: Tr.Ent, +rest: List<&2, Tr.Ent>, +a: List<&2, Tr.Ent>) -> {Tr.puts.m.at(hit, e, Tr.puts.go(a, rest, Tr.kept.at(a, rest))) == Tr.puts.go(a, e <> rest, hit) : List<&2, Tr.Op>}:
  match hit:
    case True{}:
      {==}
    case False{}:
      {==}

def tc.puts_m(b: List<&2, Tr.Ent>, +a: List<&2, Tr.Ent>, +sa: {Tr.sorted(a) == True{} : Bool}, +sb: {Tr.sorted(b) == True{} : Bool}) -> {Tr.puts.m(b, a) == Tr.puts(a, b) : List<&2, Tr.Op>}:
  match b:
    case Nil{}:
      {==}
    case +e <> +rest:
      +k = Tr.Ent.k(e)
      +c = Tr.from.k(a, k)
      +sc = tc.from_sorted(a, k, Tr.below.at(a, k), sa)
      +ar = LLogicBool.tree.pt.and_l(Tr.above(k, rest), Tr.sorted(rest), sb)
      +sr = LLogicBool.tree.pt.and_r(Tr.above(k, rest), Tr.sorted(rest), sb)
      +U = Tr.puts.go(a, rest, Tr.kept.at(a, rest))
      +H = Tr.same(Tr.get(a, k), Some{e})
      +e1 = Equal.trans(List<&2, Tr.Op>, Tr.puts.m(rest, c), Tr.puts(c, rest), U, tc.puts_m(rest, c, sc, sr), tc.puts_cong(rest, a, k, tc.ge_above(rest, k, ar, sr)))
      +fg = tc.from_get(a, k, Tr.below.at(a, k), {==}, k, LNat.pt.lt_irrefl(k))
      +e2 = Equal.trans(Bool, Tr.head.same(c, e), Tr.same(Tr.get(c, k), Some{e}), H, tc.head_same(c, e, tc.from_head(a, k, Tr.below.at(a, k), {==}), sc), Equal.cong(Maybe<&2, Tr.Ent>, Bool, z => Tr.same(z, Some{e}), Tr.get(c, k), Tr.get(a, k), fg))
      %Equal.sym(List<&2, Tr.Op>, Tr.puts.m(rest, c), U, e1) : {Tr.puts.m.at(Tr.head.same(c, e), e, _) == Tr.puts.go(a, e <> rest, H) : List<&2, Tr.Op>}
      %Equal.sym(Bool, Tr.head.same(c, e), H, e2) : {Tr.puts.m.at(_, e, U) == Tr.puts.go(a, e <> rest, H) : List<&2, Tr.Op>}
      tc.pm_at(H, e, rest, a)

def tc.diff_m(+a: List<&2, Tr.Ent>, +b: List<&2, Tr.Ent>, +sa: {Tr.sorted(a) == True{} : Bool}, +sb: {Tr.sorted(b) == True{} : Bool}) -> {Tr.diff.m(a, b) == Tr.diff(a, b) : List<&2, Tr.Op>}:
  %Equal.sym(List<&2, Tr.Op>, Tr.dels.m(a, b), Tr.dels(a, b), tc.dels_m(a, b, sa, sb)) : {List.append(&2, Tr.Op, _, Tr.puts.m(b, a)) == Tr.diff(a, b) : List<&2, Tr.Op>}
  %Equal.sym(List<&2, Tr.Op>, Tr.puts.m(b, a), Tr.puts(a, b), tc.puts_m(b, a, sa, sb)) : {List.append(&2, Tr.Op, Tr.dels(a, b), _) == Tr.diff(a, b) : List<&2, Tr.Op>}
  {==}

def tc.eff_cons(h: Bool, +k: Nat, +X: List<&2, Tr.Eff>, +Y: List<&2, Tr.Eff>, +e: {X == Y : List<&2, Tr.Eff>}) -> {Tr.eff.put(h, k) <> X == Tree.tree.effect(h, k) <> Y : List<&2, Tr.Eff>}:
  match h:
    case True{}:
      Equal.cong(List<&2, Tr.Eff>, List<&2, Tr.Eff>, ys => Tr.Restore{k} <> ys, X, Y, e)
    case False{}:
      Equal.cong(List<&2, Tr.Eff>, List<&2, Tr.Eff>, ys => Tr.Start{k} <> ys, X, Y, e)

def tc.effects(ops: List<&2, Tr.Op>, +m: Tr.KMap, +bt: {LLogicBool.tc.bst(m) == True{} : Bool}) -> {Tr.effects(ops, m) == Tree.tree.effects(ops, Tr.KMap.read(m)) : List<&2, Tr.Eff>}:
  match ops:
    case Nil{}:
      {==}
    case o <> +rest:
      match o:
        case Tr.Del{+k}:
          Equal.cong(List<&2, Tr.Eff>, List<&2, Tr.Eff>, ys => Tr.Stop{k} <> ys, Tr.effects(rest, m), Tree.tree.effects(rest, Tr.KMap.read(m)), tc.effects(rest, m, bt))
        case Tr.Put{+k, p, v}:
          %Equal.sym(Bool, Tr.KMap.has(m, k), Tr.has(Tr.KMap.read(m), k), LATreeGet.tc.has(m, k, bt)) : {Tr.eff.put(_, k) <> Tr.effects(rest, m) == Tree.tree.effect(Tr.has(Tr.KMap.read(m), k), k) <> Tree.tree.effects(rest, Tr.KMap.read(m)) : List<&2, Tr.Eff>}
          tc.eff_cons(Tr.has(Tr.KMap.read(m), k), k, Tr.effects(rest, m), Tree.tree.effects(rest, Tr.KMap.read(m)), tc.effects(rest, m, bt))

def Tree.tree_core_plan(hs, rs, n):
  +M = Tr.KMap.go(rs, hs, Tr.KNil{})
  +L = List.reverse.go(&2, Tr.Rec, rs, Nil{})
  +T = Tr.St.at(L, hs, n)
  +R = Tr.replay(rs)
  +R2 = Tr.replay(List.take(&2, Tr.Rec, rs, n))
  +bm = LATreeKMap.tc.live_bst(hs, rs)
  +e1 = Equal.trans(List<&2, Tr.Ent>, Tr.KMap.onto(M, Nil{}), Tr.KMap.read(M), R, LATreeKMap.tc.onto_nil(M), LATreeUnset.tc.live_read(hs, rs))
  +e2 = Equal.trans(List<&2, Tr.Ent>, Tr.KMap.onto(T, Nil{}), Tr.KMap.read(T), R2, LATreeKMap.tc.onto_nil(T), LATreeUnset.tc.at_read(hs, rs, n))
  +sR = LLogicBool.tree.pt.and_l(Tr.sorted(R), Tr.rooted(R), LATreeSound.replay_sound(rs))
  +sR2 = LLogicBool.tree.pt.and_l(Tr.sorted(R2), Tr.rooted(R2), LATreeSound.replay_sound(List.take(&2, Tr.Rec, rs, n)))
  +D = Tr.diff(R, R2)
  %Equal.sym(Tr.St, Tr.core.feed(hs, rs), Tr.St{M, L, hs}, LATreeCore.tc.feed(hs, rs)) : {Pair.snd(Tr.St, Tr.Ans, Tr.core.step(_, Tr.Plan{n})) == Tr.Effects{Tree.tree.effects(D, R)} : Tr.Ans}
  %Equal.sym(List<&2, Tr.Ent>, Tr.KMap.onto(M, Nil{}), R, e1) : {Tr.Effects{Tr.effects(Tr.diff.m(_, Tr.KMap.onto(T, Nil{})), M)} == Tr.Effects{Tree.tree.effects(D, R)} : Tr.Ans}
  %Equal.sym(List<&2, Tr.Ent>, Tr.KMap.onto(T, Nil{}), R2, e2) : {Tr.Effects{Tr.effects(Tr.diff.m(R, _), M)} == Tr.Effects{Tree.tree.effects(D, R)} : Tr.Ans}
  %Equal.sym(List<&2, Tr.Op>, Tr.diff.m(R, R2), D, tc.diff_m(R, R2, sR, sR2)) : {Tr.Effects{Tr.effects(_, M)} == Tr.Effects{Tree.tree.effects(D, R)} : Tr.Ans}
  +s1 = tc.effects(D, M, bm)
  +s2 = Equal.cong(List<&2, Tr.Ent>, List<&2, Tr.Eff>, z => Tree.tree.effects(D, z), Tr.KMap.read(M), R, LATreeUnset.tc.live_read(hs, rs))
  Equal.cong(List<&2, Tr.Eff>, Tr.Ans, z => Tr.Effects{z}, Tr.effects(D, M), Tree.tree.effects(D, R), Equal.trans(List<&2, Tr.Eff>, Tr.effects(D, M), Tree.tree.effects(D, Tr.KMap.read(M)), Tree.tree.effects(D, R), s1, s2))
