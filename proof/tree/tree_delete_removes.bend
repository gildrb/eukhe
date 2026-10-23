# eukhe: the proof of LAW tree_delete_removes

import Base
import ../../bend/tree.bend as Tr
import ../../LAWS.bend as Laws
import ../base.bend as L
import ./base.bend as LA

# Delete: removes, within
# -----------------------

def pt.removes_go(s: List<&2, Tr.Ent>, +gone: List<&2, Nat>, hit: Bool, eh: {Tr.gone.at(s, gone) == hit : Bool}, +x: Nat, +ex: {Tr.elem(gone, x) == True{} : Bool}) -> {Tr.has(Tr.prune.go(s, gone, hit), x) == False{} : Bool}:
  match s:
    case Nil{}:
      {==}
    case +e <> +r:
      match hit:
        case True{}:
          +g2 = {Tr.Ent.k(e) <> gone : List<&2, Nat>}
          pt.removes_go(r, g2, Tr.gone.at(r, g2), {==}, x, LA.pt.or_tr(Nat.is_eq(Tr.Ent.k(e), x), Tr.elem(gone, x), ex))
        case False{}:
          +P = Tr.prune.go(r, gone, Tr.gone.at(r, gone))
          +ng = LA.pt.or_l(Tr.elem(gone, Tr.Ent.k(e)), Tr.elem(gone, Tr.Ent.p(e)), eh)
          +ne = LA.pt.ne_by(Tr.Ent.k(e), x, z => Tr.elem(gone, z), ng, ex)
          Equal.trans(Bool, Tr.has(e <> P, x), Tr.has(P, x), False{}, LA.pt.has_miss(e, P, x, ne), pt.removes_go(r, gone, Tr.gone.at(r, gone), {==}, x, ex))

def pt.removes_nz(+t: List<&2, Tr.Ent>, +x: Nat) -> {Tr.has(Tr.prune(t, x), x) == False{} : Bool}:
  pt.removes_go(t, [x], Tr.gone.at(t, [x]), {==}, x, LA.pt.or_tl(Nat.is_eq(x, x), False{}, Equal.sym(Bool, True{}, Nat.is_eq(x, x), LA.pt.eq_refl(x))))

# a key above a parent is not the root
def pt.key_nz(p: Nat, k: Nat, lt: {Nat.is_lt(p, k) == True{} : Bool}) -> {Nat.is_eq(k, 0n) == False{} : Bool}:
  match p k:
    case 0n 0n:
      L.tree.pt.absurdF({Nat.is_eq(0n, 0n) == False{} : Bool}, lt)
    case 1n+q 0n:
      L.tree.pt.absurdF({Nat.is_eq(0n, 0n) == False{} : Bool}, lt)
    case _ 1n+q:
      {==}

# no node of a rooted list is the root
def pt.rooted_nz(s: List<&2, Tr.Ent>, +all: List<&2, Tr.Ent>, +rs: {Tr.rooted.go(s, all) == True{} : Bool}) -> {Tr.has(s, 0n) == False{} : Bool}:
  match s:
    case Nil{}:
      {==}
    case +e <> +r:
      +k = Tr.Ent.k(e)
      +p = Tr.Ent.p(e)
      +oe = L.tree.pt.and_l(Tr.ok(all, k, p), Tr.rooted.go(r, all), rs)
      +lt = L.tree.pt.and_l(Nat.is_lt(p, k), Bool.or(Nat.is_eq(p, 0n), Tr.has(all, p)), oe)
      Equal.trans(Bool, Tr.has(e <> r, 0n), Tr.has(r, 0n), False{}, LA.pt.has_miss(e, r, 0n, pt.key_nz(p, k, lt)), pt.rooted_nz(r, all, L.tree.pt.and_r(Tr.ok(all, k, p), Tr.rooted.go(r, all), rs)))

# a delete of the root changes nothing, and the root is no node
def delete_removes(+t: List<&2, Tr.Ent>, +good: {Tr.sound(t) == True{} : Bool}, +x: Nat) -> {Tr.has(Tr.apply(t, Tr.Do{Tr.Del{x}}), x) == False{} : Bool}:
  match x:
    case 0n:
      pt.rooted_nz(t, t, L.tree.pt.and_r(Tr.sorted(t), Tr.rooted(t), good))
    case 1n+y:
      pt.removes_nz(t, 1n+y)

def Laws.tree_delete_removes(t, L.good, x):
  delete_removes(t, L.good, x)
