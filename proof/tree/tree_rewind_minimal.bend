# eukhe: the proof of LAW tree_rewind_minimal

import Base
import ../../bend/tree.bend as Tr
import ../../LAWS.bend as Laws
import ../base.bend as L
import ./base.bend as LA

def pt.changed_app(xs: List<&2, Tr.Op>, +ys: List<&2, Tr.Op>, +a: List<&2, Tr.Ent>, +b: List<&2, Tr.Ent>, +cx: {Tr.changed(a, b, xs) == True{} : Bool}, cy: {Tr.changed(a, b, ys) == True{} : Bool}) -> {Tr.changed(a, b, List.append(&2, Tr.Op, xs, ys)) == True{} : Bool}:
  match xs:
    case Nil{}:
      cy
    case +o <> +r:
      +i = Bool.not(Tr.same(Tr.get(a, Tr.Op.k(o)), Tr.get(b, Tr.Op.k(o))))
      L.tree.pt.and_t(i, Tr.changed(a, b, List.append(&2, Tr.Op, r, ys)), L.tree.pt.and_l(i, Tr.changed(a, b, r), cx), pt.changed_app(r, ys, a, b, L.tree.pt.and_r(i, Tr.changed(a, b, r), cx), cy))

# a node one side holds and the other lacks differs
def pt.same_has(m1: Maybe<&2, Tr.Ent>, m2: Maybe<&2, Tr.Ent>, h1: {Maybe.is_some(&2, Tr.Ent, m1) == True{} : Bool}, h2: {Maybe.is_some(&2, Tr.Ent, m2) == False{} : Bool}) -> {Bool.not(Tr.same(m1, m2)) == True{} : Bool}:
  match m1 m2:
    case None{} _:
      L.tree.pt.absurdF({Bool.not(Tr.same(None{}, m2)) == True{} : Bool}, h1)
    case Some{x} None{}:
      {==}
    case Some{x} Some{y}:
      L.pt.absurd({Bool.not(Tr.same(Some{x}, Some{y})) == True{} : Bool}, h2)

def pt.dels_changed(s: List<&2, Tr.Ent>, +a: List<&2, Tr.Ent>, +b: List<&2, Tr.Ent>, hit: Bool, eh: {Tr.held.at(s, b) == hit : Bool}, +ah: {LA.pt.allhas(s, a) == True{} : Bool}) -> {Tr.changed(a, b, Tr.dels.go(s, b, hit)) == True{} : Bool}:
  match s:
    case Nil{}:
      {==}
    case +e <> +r:
      match hit:
        case True{}:
          +i = Tr.has(a, Tr.Ent.k(e))
          pt.dels_changed(r, a, b, Tr.held.at(r, b), {==}, L.tree.pt.and_r(i, LA.pt.allhas(r, a), ah))
        case False{}:
          +i = Tr.has(a, Tr.Ent.k(e))
          +k = Tr.Ent.k(e)
          +d = Bool.not(Tr.same(Tr.get(a, k), Tr.get(b, k)))
          L.tree.pt.and_t(d, Tr.changed(a, b, Tr.dels.go(r, b, Tr.held.at(r, b))), pt.same_has(Tr.get(a, k), Tr.get(b, k), L.tree.pt.and_l(i, LA.pt.allhas(r, a), ah), eh), pt.dels_changed(r, a, b, Tr.held.at(r, b), {==}, L.tree.pt.and_r(i, LA.pt.allhas(r, a), ah)))

def pt.put_differs(+a: List<&2, Tr.Ent>, +b: List<&2, Tr.Ent>, +e: Tr.Ent, eh: {Tr.same(Tr.get(a, Tr.Ent.k(e)), Some{e}) == False{} : Bool}, wb: {Tr.same(Tr.get(b, Tr.Ent.k(e)), Some{e}) == True{} : Bool}) -> {Bool.not(Tr.same(Tr.get(a, Tr.Ent.k(e)), Tr.get(b, Tr.Ent.k(e)))) == True{} : Bool}:
  %Equal.sym(Maybe<&2, Tr.Ent>, Tr.get(b, Tr.Ent.k(e)), Some{e}, LA.pt.same_some(Tr.get(b, Tr.Ent.k(e)), e, wb)) : {Bool.not(Tr.same(Tr.get(a, Tr.Ent.k(e)), _)) == True{} : Bool}
  %Equal.sym(Bool, Tr.same(Tr.get(a, Tr.Ent.k(e)), Some{e}), False{}, eh) : {Bool.not(_) == True{} : Bool}
  {==}

def pt.puts_changed(+a: List<&2, Tr.Ent>, s: List<&2, Tr.Ent>, +b: List<&2, Tr.Ent>, hit: Bool, eh: {Tr.kept.at(a, s) == hit : Bool}, +w: {Tr.within(s, b) == True{} : Bool}) -> {Tr.changed(a, b, Tr.puts.go(a, s, hit)) == True{} : Bool}:
  match s:
    case Nil{}:
      {==}
    case +e <> +r:
      match hit:
        case True{}:
          +i = Tr.same(Tr.get(b, Tr.Ent.k(e)), Some{e})
          pt.puts_changed(a, r, b, Tr.kept.at(a, r), {==}, L.tree.pt.and_r(i, Tr.within(r, b), w))
        case False{}:
          +i = Tr.same(Tr.get(b, Tr.Ent.k(e)), Some{e})
          +k = Tr.Ent.k(e)
          +d = Bool.not(Tr.same(Tr.get(a, k), Tr.get(b, k)))
          L.tree.pt.and_t(d, Tr.changed(a, b, Tr.puts.go(a, r, Tr.kept.at(a, r))), pt.put_differs(a, b, e, eh, L.tree.pt.and_l(i, Tr.within(r, b), w)), pt.puts_changed(a, r, b, Tr.kept.at(a, r), {==}, L.tree.pt.and_r(i, Tr.within(r, b), w)))

def rewind_minimal(+a: List<&2, Tr.Ent>, +b: List<&2, Tr.Ent>, ga: {Tr.sorted(a) == True{} : Bool}, gb: {Tr.sorted(b) == True{} : Bool}) -> {Tr.changed(a, b, Tr.diff(a, b)) == True{} : Bool}:
  pt.changed_app(Tr.dels(a, b), Tr.puts(a, b), a, b, pt.dels_changed(a, a, b, Tr.held.at(a, b), {==}, LA.pt.allhas_self(a)), pt.puts_changed(a, b, b, Tr.kept.at(a, b), {==}, LA.pt.within_self(b, gb)))

def Laws.tree_rewind_minimal(a, b, ga, gb):
  rewind_minimal(a, b, ga, gb)
