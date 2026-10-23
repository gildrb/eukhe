# eukhe: lemmas the proofs of area tree share: tree/puts

import Base
import ../../../../bend/tree.bend as Tr
import ../../../base/logic/bool.bend as LLogicBool
import ../list.bend as LAList
import ../logic.bend as LALogic
import ./Ent.bend as LATreeEnt
import ./dels.bend as LATreeDels
import ./get.bend as LATreeGet

# the puts leave a key the target lacks
def pt.puts_miss(+a: List<&2, Tr.Ent>, s: List<&2, Tr.Ent>, hit: Bool, +m: Maybe<&2, Tr.Ent>, +x: Nat, +gn: {Tr.get(s, x) == None{} : Maybe<&2, Tr.Ent>}) -> {LALogic.pt.look(Tr.puts.go(a, s, hit), m, x) == m : Maybe<&2, Tr.Ent>}:
  match s:
    case Nil{}:
      {==}
    case +e <> +r:
      match hit:
        case True{}:
          +ne = LATreeGet.pt.get_none_head(e, r, x, gn)
          pt.puts_miss(a, r, Tr.kept.at(a, r), m, x, Equal.trans(Maybe<&2, Tr.Ent>, Tr.get(r, x), Tr.get(e <> r, x), None{}, Equal.sym(Maybe<&2, Tr.Ent>, Tr.get(e <> r, x), Tr.get(r, x), LATreeGet.pt.get_miss(e, r, x, ne)), gn))
        case False{}:
          +ne = LATreeGet.pt.get_none_head(e, r, x, gn)
          %Equal.sym(Bool, Nat.is_eq(Tr.Ent.k(e), x), False{}, ne) : {LALogic.pt.look(Tr.puts.go(a, r, Tr.kept.at(a, r)), LALogic.tree.pt.pick(_, Some{Tr.Ent{Tr.Ent.k(e), Tr.Ent.p(e), Tr.Ent.v(e)}}, m), x) == m : Maybe<&2, Tr.Ent>}
          pt.puts_miss(a, r, Tr.kept.at(a, r), m, x, Equal.trans(Maybe<&2, Tr.Ent>, Tr.get(r, x), Tr.get(e <> r, x), None{}, Equal.sym(Maybe<&2, Tr.Ent>, Tr.get(e <> r, x), Tr.get(r, x), LATreeGet.pt.get_miss(e, r, x, ne)), gn))

def pt.ph_go(+a: List<&2, Tr.Ent>, +e: Tr.Ent, +r: List<&2, Tr.Ent>, +m: Maybe<&2, Tr.Ent>, +x: Nat, +z: Tr.Ent, c: Bool, +ec: {Nat.is_eq(Tr.Ent.k(e), x) == c : Bool}, hit: Bool, eh: {Tr.same(Tr.get(a, Tr.Ent.k(e)), Some{e}) == hit : Bool}, +al: {Tr.above(Tr.Ent.k(e), r) == True{} : Bool}, +sr: {Tr.sorted(r) == True{} : Bool}, ih: {Tr.get(r, x) == Some{z} : Maybe<&2, Tr.Ent>} -> {LALogic.pt.look(Tr.puts.go(a, r, Tr.kept.at(a, r)), m, x) == LALogic.tree.pt.pick(Tr.same(Tr.get(a, x), Some{z}), m, Some{z}) : Maybe<&2, Tr.Ent>}, +gs: {Tr.get(e <> r, x) == Some{z} : Maybe<&2, Tr.Ent>}) -> {LALogic.pt.look(Tr.puts.go(a, e <> r, hit), m, x) == LALogic.tree.pt.pick(Tr.same(Tr.get(a, x), Some{z}), m, Some{z}) : Maybe<&2, Tr.Ent>}:
  match c hit:
    case True{} True{}:
      +P = Tr.puts.go(a, r, Tr.kept.at(a, r))
      +ez = LALogic.tree.pt.some_inj(e, z, Equal.trans(Maybe<&2, Tr.Ent>, Some{e}, Tr.get(e <> r, x), Some{z}, Equal.sym(Maybe<&2, Tr.Ent>, Tr.get(e <> r, x), Some{e}, LATreeGet.pt.get_hit(e, r, x, ec)), gs))
      %ez : {LALogic.pt.look(P, m, x) == LALogic.tree.pt.pick(Tr.same(Tr.get(a, x), Some{_}), m, Some{_}) : Maybe<&2, Tr.Ent>}
      %LALogic.pt.eq_true(Tr.Ent.k(e), x, ec) : {LALogic.pt.look(P, m, _) == LALogic.tree.pt.pick(Tr.same(Tr.get(a, _), Some{e}), m, Some{e}) : Maybe<&2, Tr.Ent>}
      %Equal.sym(Bool, Tr.same(Tr.get(a, Tr.Ent.k(e)), Some{e}), True{}, eh) : {LALogic.pt.look(P, m, Tr.Ent.k(e)) == LALogic.tree.pt.pick(_, m, Some{e}) : Maybe<&2, Tr.Ent>}
      pt.puts_miss(a, r, Tr.kept.at(a, r), m, Tr.Ent.k(e), LATreeGet.pt.get_below(r, Tr.Ent.k(e), al, sr))
    case True{} False{}:
      +P = Tr.puts.go(a, r, Tr.kept.at(a, r))
      +E = {Tr.Ent{Tr.Ent.k(e), Tr.Ent.p(e), Tr.Ent.v(e)} : Tr.Ent}
      +ez = LALogic.tree.pt.some_inj(e, z, Equal.trans(Maybe<&2, Tr.Ent>, Some{e}, Tr.get(e <> r, x), Some{z}, Equal.sym(Maybe<&2, Tr.Ent>, Tr.get(e <> r, x), Some{e}, LATreeGet.pt.get_hit(e, r, x, ec)), gs))
      %Equal.sym(Bool, Nat.is_eq(Tr.Ent.k(e), x), True{}, ec) : {LALogic.pt.look(P, LALogic.tree.pt.pick(_, Some{E}, m), x) == LALogic.tree.pt.pick(Tr.same(Tr.get(a, x), Some{z}), m, Some{z}) : Maybe<&2, Tr.Ent>}
      %ez : {LALogic.pt.look(P, Some{E}, x) == LALogic.tree.pt.pick(Tr.same(Tr.get(a, x), Some{_}), m, Some{_}) : Maybe<&2, Tr.Ent>}
      %LALogic.pt.eq_true(Tr.Ent.k(e), x, ec) : {LALogic.pt.look(P, Some{E}, _) == LALogic.tree.pt.pick(Tr.same(Tr.get(a, _), Some{e}), m, Some{e}) : Maybe<&2, Tr.Ent>}
      %Equal.sym(Bool, Tr.same(Tr.get(a, Tr.Ent.k(e)), Some{e}), False{}, eh) : {LALogic.pt.look(P, Some{E}, Tr.Ent.k(e)) == LALogic.tree.pt.pick(_, m, Some{e}) : Maybe<&2, Tr.Ent>}
      Equal.trans(Maybe<&2, Tr.Ent>, LALogic.pt.look(P, Some{E}, Tr.Ent.k(e)), Some{E}, Some{e}, pt.puts_miss(a, r, Tr.kept.at(a, r), Some{E}, Tr.Ent.k(e), LATreeGet.pt.get_below(r, Tr.Ent.k(e), al, sr)), Equal.cong(Tr.Ent, Maybe<&2, Tr.Ent>, y => Some{y}, E, e, LATreeEnt.pt.ent_eta(e)))
    case False{} True{}:
      ih(Equal.trans(Maybe<&2, Tr.Ent>, Tr.get(r, x), Tr.get(e <> r, x), Some{z}, Equal.sym(Maybe<&2, Tr.Ent>, Tr.get(e <> r, x), Tr.get(r, x), LATreeGet.pt.get_miss(e, r, x, ec)), gs))
    case False{} False{}:
      +P = Tr.puts.go(a, r, Tr.kept.at(a, r))
      +E = {Tr.Ent{Tr.Ent.k(e), Tr.Ent.p(e), Tr.Ent.v(e)} : Tr.Ent}
      %Equal.sym(Bool, Nat.is_eq(Tr.Ent.k(e), x), False{}, ec) : {LALogic.pt.look(P, LALogic.tree.pt.pick(_, Some{E}, m), x) == LALogic.tree.pt.pick(Tr.same(Tr.get(a, x), Some{z}), m, Some{z}) : Maybe<&2, Tr.Ent>}
      ih(Equal.trans(Maybe<&2, Tr.Ent>, Tr.get(r, x), Tr.get(e <> r, x), Some{z}, Equal.sym(Maybe<&2, Tr.Ent>, Tr.get(e <> r, x), Tr.get(r, x), LATreeGet.pt.get_miss(e, r, x, ec)), gs))

# the puts set a key the target holds, unless a holds it the same
def pt.puts_hit(+a: List<&2, Tr.Ent>, s: List<&2, Tr.Ent>, hit: Bool, eh: {Tr.kept.at(a, s) == hit : Bool}, +m: Maybe<&2, Tr.Ent>, +x: Nat, +z: Tr.Ent, +st: {Tr.sorted(s) == True{} : Bool}) -> {Tr.get(s, x) == Some{z} : Maybe<&2, Tr.Ent>} -> {LALogic.pt.look(Tr.puts.go(a, s, hit), m, x) == LALogic.tree.pt.pick(Tr.same(Tr.get(a, x), Some{z}), m, Some{z}) : Maybe<&2, Tr.Ent>}:
  match s:
    case Nil{}:
      gs => LALogic.tree.pt.none_some({LALogic.pt.look(Tr.puts.go(a, Nil{}, hit), m, x) == LALogic.tree.pt.pick(Tr.same(Tr.get(a, x), Some{z}), m, Some{z}) : Maybe<&2, Tr.Ent>}, z, gs)
    case +e <> +r:
      ih = pt.puts_hit(a, r, Tr.kept.at(a, r), {==}, m, x, z, LLogicBool.tree.pt.and_r(Tr.above(Tr.Ent.k(e), r), Tr.sorted(r), st))
      gs => pt.ph_go(a, e, r, m, x, z, Nat.is_eq(Tr.Ent.k(e), x), {==}, hit, eh, LLogicBool.tree.pt.and_l(Tr.above(Tr.Ent.k(e), r), Tr.sorted(r), st), LLogicBool.tree.pt.and_r(Tr.above(Tr.Ent.k(e), r), Tr.sorted(r), st), ih, gs)

def pt.reach_go(+a: List<&2, Tr.Ent>, +b: List<&2, Tr.Ent>, +x: Nat, +sb: {Tr.sorted(b) == True{} : Bool}, mb: Maybe<&2, Tr.Ent>, +eb: {Tr.get(b, x) == mb : Maybe<&2, Tr.Ent>}) -> {LALogic.pt.look(Tr.puts.go(a, b, Tr.kept.at(a, b)), LALogic.pt.look(Tr.dels.go(a, b, Tr.held.at(a, b)), Tr.get(a, x), x), x) == Tr.get(b, x) : Maybe<&2, Tr.Ent>}:
  match mb:
    case None{}:
      +P = Tr.puts.go(a, b, Tr.kept.at(a, b))
      +D = Tr.dels.go(a, b, Tr.held.at(a, b))
      +hb = Equal.cong(Maybe<&2, Tr.Ent>, Bool, mm => Maybe.is_some(&2, Tr.Ent, mm), Tr.get(b, x), None{}, eb)
      %Equal.sym(Maybe<&2, Tr.Ent>, LALogic.pt.look(D, Tr.get(a, x), x), None{}, LATreeGet.pt.dels_drop(a, b, Tr.held.at(a, b), {==}, x, hb)) : {LALogic.pt.look(P, _, x) == Tr.get(b, x) : Maybe<&2, Tr.Ent>}
      Equal.trans(Maybe<&2, Tr.Ent>, LALogic.pt.look(P, None{}, x), None{}, Tr.get(b, x), pt.puts_miss(a, b, Tr.kept.at(a, b), None{}, x, eb), Equal.sym(Maybe<&2, Tr.Ent>, Tr.get(b, x), None{}, eb))
    case Some{+z}:
      +P = Tr.puts.go(a, b, Tr.kept.at(a, b))
      +D = Tr.dels.go(a, b, Tr.held.at(a, b))
      +ga = Tr.get(a, x)
      +hb = Equal.cong(Maybe<&2, Tr.Ent>, Bool, mm => Maybe.is_some(&2, Tr.Ent, mm), Tr.get(b, x), Some{z}, eb)
      %Equal.sym(Maybe<&2, Tr.Ent>, LALogic.pt.look(D, ga, x), ga, LATreeDels.pt.dels_keep(a, b, Tr.held.at(a, b), {==}, ga, x, hb)) : {LALogic.pt.look(P, _, x) == Tr.get(b, x) : Maybe<&2, Tr.Ent>}
      +c = Tr.same(ga, Some{z})
      Equal.trans(Maybe<&2, Tr.Ent>, LALogic.pt.look(P, ga, x), LALogic.tree.pt.pick(c, ga, Some{z}), Tr.get(b, x), pt.puts_hit(a, b, Tr.kept.at(a, b), {==}, ga, x, z, sb)(eb), Equal.trans(Maybe<&2, Tr.Ent>, LALogic.tree.pt.pick(c, ga, Some{z}), Some{z}, Tr.get(b, x), LATreeGet.pt.reach_tail(a, x, z, c, {==}), Equal.sym(Maybe<&2, Tr.Ent>, Tr.get(b, x), Some{z}, eb)))

# after the rewind ops, the tree holds at x what the target holds
def pt.reach_at(+a: List<&2, Tr.Ent>, +b: List<&2, Tr.Ent>, +x: Nat, +sb: {Tr.sorted(b) == True{} : Bool}) -> {Tr.get(Tr.patch(Tr.diff(a, b), a), x) == Tr.get(b, x) : Maybe<&2, Tr.Ent>}:
  +D = Tr.dels(a, b)
  +P = Tr.puts(a, b)
  +ga = Tr.get(a, x)
  Equal.trans(Maybe<&2, Tr.Ent>, Tr.get(Tr.patch(Tr.diff(a, b), a), x), LALogic.pt.look(List.append(&2, Tr.Op, D, P), ga, x), Tr.get(b, x), LATreeGet.pt.get_patch(Tr.diff(a, b), a, x), Equal.trans(Maybe<&2, Tr.Ent>, LALogic.pt.look(List.append(&2, Tr.Op, D, P), ga, x), LALogic.pt.look(P, LALogic.pt.look(D, ga, x), x), Tr.get(b, x), LAList.pt.look_app(D, P, ga, x), pt.reach_go(a, b, x, sb, Tr.get(b, x), {==})))

def pt.agree_reach(es: List<&2, Tr.Ent>, +a: List<&2, Tr.Ent>, +b: List<&2, Tr.Ent>, +sb: {Tr.sorted(b) == True{} : Bool}) -> LALogic.pt.Agree(es, Tr.patch(Tr.diff(a, b), a), b):
  match es:
    case Nil{}:
      Unit{}
    case +e <> rest:
      (pt.reach_at(a, b, Tr.Ent.k(e), sb), pt.agree_reach(rest, a, b, sb))
