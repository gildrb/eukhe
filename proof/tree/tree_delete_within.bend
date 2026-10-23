# eukhe: the proof of LAW tree_delete_within

import Base
import ../../bend/tree.bend as Tr
import ../../laws/tree.bend as Tree
import ../base/bool.bend as LBool
import ../base/logic/bool.bend as LLogicBool
import ../base/retry.bend as LRetry
import ./base/tree/within.bend as LATreeWithin

def pt.within_prune_go(s: List<&2, Tr.Ent>, +gone: List<&2, Nat>, hit: Bool, +t: List<&2, Tr.Ent>, +w: {Tr.within(s, t) == True{} : Bool}) -> {Tr.within(Tr.prune.go(s, gone, hit), t) == True{} : Bool}:
  match s:
    case Nil{}:
      {==}
    case +e <> +r:
      match hit:
        case True{}:
          +i = Tr.same(Tr.get(t, Tr.Ent.k(e)), Some{e})
          +g2 = {Tr.Ent.k(e) <> gone : List<&2, Nat>}
          pt.within_prune_go(r, g2, Tr.gone.at(r, g2), t, LLogicBool.tree.pt.and_r(i, Tr.within(r, t), w))
        case False{}:
          +i = Tr.same(Tr.get(t, Tr.Ent.k(e)), Some{e})
          +P = Tr.prune.go(r, gone, Tr.gone.at(r, gone))
          LBool.tree.pt.and_t(i, Tr.within(P, t), LLogicBool.tree.pt.and_l(i, Tr.within(r, t), w), pt.within_prune_go(r, gone, Tr.gone.at(r, gone), t, LLogicBool.tree.pt.and_r(i, Tr.within(r, t), w)))

def delete_within(+t: List<&2, Tr.Ent>, +good: {Tr.sound(t) == True{} : Bool}, +x: Nat) -> {Tr.within(Tr.apply(t, Tr.Do{Tr.Del{x}}), t) == True{} : Bool}:
  match x:
    case 0n:
      LATreeWithin.pt.within_self(t, LLogicBool.tree.pt.and_l(Tr.sorted(t), Tr.rooted(t), good))
    case 1n+y:
      pt.within_prune_go(t, [1n+y], Tr.gone.at(t, [1n+y]), t, LATreeWithin.pt.within_self(t, LLogicBool.tree.pt.and_l(Tr.sorted(t), Tr.rooted(t), good)))

def Tree.tree_delete_within(t, LRetry.good, x):
  delete_within(t, LRetry.good, x)
