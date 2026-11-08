# eukhe: the proof of LAW tree_replay_spec
#
# PROOF: on a valid tree each record of the model is the spec's: a put
# checks the spec's hang (LB.ts.ok) and sets as the spec puts (LS.ts.set);
# a delete of the root keeps the tree, any other is the spec's delete
# (LP.tp.prune); a rewind patches as the spec does (LS.ts.patch) and keeps
# the result by the spec's validity (LB.ts.sound). Every record keeps the
# model's tree valid (apply_sound), so the journal folds the same from the
# empty tree.

import Base
import ../../bend/tree.bend as Tr
import ../../laws/tree.bend as Tree
import ../../spec/durable/tree.bend as TS
import ./base/tree/sound.bend as LATreeSound
import ../base/logic/bool.bend as LLogicBool
import ./tree_replay_spec/basic.bend as LB
import ./tree_replay_spec/set.bend as LS
import ./tree_replay_spec/prune.bend as LP

def tr.put_at(b: Bool, +t: List<&2, Tr.Ent>, +k: Nat, +p: Nat, +v: Nat, +st: {Tr.sorted(t) == True{} : Bool}) -> {Tr.put.at(b, t, Tr.Ent{k, p, v}) == TS.apply.put(b, t, Tr.Ent{k, p, v}) : List<&2, Tr.Ent>}:
  match b:
    case True{}:
      LS.ts.set(t, k, p, v, st)
    case False{}:
      {==}

def tr.keep_at(b: Bool, t: List<&2, Tr.Ent>, n: List<&2, Tr.Ent>) -> {Tr.keep.at(b, t, n) == TS.apply.keep(b, t, n) : List<&2, Tr.Ent>}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

# on a valid tree a record of the model is the spec's
def tr.apply(+t: List<&2, Tr.Ent>, r: Tr.Rec, +good: {Tr.sound(t) == True{} : Bool}) -> {Tr.apply(t, r) == TS.apply(t, r) : List<&2, Tr.Ent>}:
  match r:
    case Tr.Do{o}:
      match o:
        case Tr.Put{+k, +p, +v}:
          %LB.ts.ok(t, k, p) : {Tr.put.at(Tr.ok(t, k, p), t, Tr.Ent{k, p, v}) == TS.apply.put(_, t, Tr.Ent{k, p, v}) : List<&2, Tr.Ent>}
          tr.put_at(Tr.ok(t, k, p), t, k, p, v, LLogicBool.tree.pt.and_l(Tr.sorted(t), Tr.rooted(t), good))
        case Tr.Del{x}:
          match x:
            case 0n:
              {==}
            case 1n+q:
              LP.tp.prune(t, q, good)
    case Tr.Rewind{+ops}:
      +st = LLogicBool.tree.pt.and_l(Tr.sorted(t), Tr.rooted(t), good)
      %LS.ts.patch(ops, t, st) : {Tr.keep.at(Tr.sound(Tr.patch(ops, t)), t, Tr.patch(ops, t)) == TS.apply.keep(TS.valid(_), t, _) : List<&2, Tr.Ent>}
      %LB.ts.sound(Tr.patch(ops, t)) : {Tr.keep.at(Tr.sound(Tr.patch(ops, t)), t, Tr.patch(ops, t)) == TS.apply.keep(_, t, Tr.patch(ops, t)) : List<&2, Tr.Ent>}
      tr.keep_at(Tr.sound(Tr.patch(ops, t)), t, Tr.patch(ops, t))

def tr.go(rs: List<&2, Tr.Rec>, +t: List<&2, Tr.Ent>, +good: {Tr.sound(t) == True{} : Bool}) -> {Tr.go(rs, t) == TS.go(rs, t) : List<&2, Tr.Ent>}:
  match rs:
    case Nil{}:
      {==}
    case +r <> rest:
      %tr.apply(t, r, good) : {Tr.go(rest, Tr.apply(t, r)) == TS.go(rest, _) : List<&2, Tr.Ent>}
      tr.go(rest, Tr.apply(t, r), LATreeSound.apply_sound(t, good, r))

def Tree.tree_replay_spec(rs):
  tr.go(rs, Nil{}, {==})
