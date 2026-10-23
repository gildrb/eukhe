# eukhe: lemmas the proofs of area tree share: tree/sound

import Base
import ../../../../bend/tree.bend as Tr
import ../../../base/bool.bend as LBool
import ../../../base/logic/bool.bend as LLogicBool
import ./rooted.bend as LATreeRooted
import ./sorted.bend as LATreeSorted

def pt.keep_sound(+t: List<&2, Tr.Ent>, +n: List<&2, Tr.Ent>, b: Bool, eb: {Tr.sound(n) == b : Bool}, st: {Tr.sound(t) == True{} : Bool}) -> {Tr.sound(Tr.keep.at(b, t, n)) == True{} : Bool}:
  match b:
    case True{}:
      eb
    case False{}:
      st

def pt.put_sound(+t: List<&2, Tr.Ent>, +k: Nat, +p: Nat, +v: Nat, b: Bool, eb: {Tr.ok(t, k, p) == b : Bool}, +st: {Tr.sound(t) == True{} : Bool}) -> {Tr.sound(Tr.put.at(b, t, Tr.Ent{k, p, v})) == True{} : Bool}:
  match b:
    case True{}:
      +e = {Tr.Ent{k, p, v} : Tr.Ent}
      +s = Tr.set(t, e)
      LBool.tree.pt.and_t(Tr.sorted(s), Tr.rooted(s), LATreeSorted.pt.sorted_set_go(t, e, Tr.first(k, t), {==}, LLogicBool.tree.pt.and_l(Tr.sorted(t), Tr.rooted(t), st)), LATreeRooted.pt.rooted_set_go(t, t, e, Tr.first(k, t), LLogicBool.tree.pt.and_r(Tr.sorted(t), Tr.rooted(t), st), eb))
    case False{}:
      st

def pt.del_sound(+t: List<&2, Tr.Ent>, +x: Nat, +st: {Tr.sound(t) == True{} : Bool}) -> {Tr.sound(Tr.prune(t, x)) == True{} : Bool}:
  +R = Tr.prune(t, x)
  +so = LLogicBool.tree.pt.and_l(Tr.sorted(t), Tr.rooted(t), st)
  +ro = LLogicBool.tree.pt.and_r(Tr.sorted(t), Tr.rooted(t), st)
  LBool.tree.pt.and_t(Tr.sorted(R), Tr.rooted(R), LATreeSorted.pt.sorted_prune_go(t, [x], Tr.gone.at(t, [x]), so), LATreeRooted.pt.rooted_prune_go(t, [x], Tr.gone.at(t, [x]), {==}, Nil{}, Nil{}, {==}, LATreeSorted.pt.upl_of(t, Nil{}, ro, so)))

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
      pt.keep_sound(t, Tr.patch(ops, t), Tr.sound(Tr.patch(ops, t)), {==}, good)

def pt.go_sound(rs: List<&2, Tr.Rec>, +t: List<&2, Tr.Ent>, +st: {Tr.sound(t) == True{} : Bool}) -> {Tr.sound(Tr.go(rs, t)) == True{} : Bool}:
  match rs:
    case Nil{}:
      st
    case +r <> rest:
      pt.go_sound(rest, Tr.apply(t, r), apply_sound(t, st, r))

def replay_sound(+rs: List<&2, Tr.Rec>) -> {Tr.sound(Tr.replay(rs)) == True{} : Bool}:
  pt.go_sound(rs, Nil{}, {==})
