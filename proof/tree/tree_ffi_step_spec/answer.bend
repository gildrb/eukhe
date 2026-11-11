# eukhe: lemmas of LAW tree_ffi_step_spec: on a valid tree the laws'
# answer to a record (tree.answer) is the spec's (TS.answer).

import Base
import ../../../bend/tree.bend as Tr
import ../../../laws/tree.bend as Tree
import ../../../spec/durable/tree.bend as TS
import ../../base/logic/bool.bend as LLogicBool
import ../tree_replay_spec/basic.bend as LB
import ../tree_replay_spec/set.bend as LS
import ../tree_replay_spec/prune.bend as LP

def ta.took(b: Bool) -> {Tree.tree.took(b) == TS.took(b) : Tr.Ans}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def ta.lost_at(c: Bool, +k: Nat, -r1: List<&2, Nat>, -r2: List<&2, Nat>, ih: {r1 == r2 : List<&2, Nat>}) -> {Tree.tree.lost.at(c, k, r1) == TS.key.if(Bool.not(c), k, r2) : List<&2, Nat>}:
  match c:
    case True{}:
      ih
    case False{}:
      %ih : {k <> r1 == k <> _ : List<&2, Nat>}
      {==}

def ta.lost(s: List<&2, Tr.Ent>, +b: List<&2, Tr.Ent>) -> {Tree.tree.lost(s, b) == TS.lost(s, b) : List<&2, Nat>}:
  match s:
    case Nil{}:
      {==}
    case +e <> +rest:
      match e:
        case Tr.Ent{+k, p, v}:
          %LB.ts.has(b, k) : {Tree.tree.lost.at(Tr.has(b, k), k, Tree.tree.lost(rest, b)) == TS.key.if(Bool.not(_), k, TS.lost(rest, b)) : List<&2, Nat>}
          ta.lost_at(Tr.has(b, k), k, Tree.tree.lost(rest, b), TS.lost(rest, b), ta.lost(rest, b))

# on a valid tree the laws' answer to a record is the spec's
def ta.answer(+t: List<&2, Tr.Ent>, r: Tr.Rec, +good: {Tr.sound(t) == True{} : Bool}) -> {Tree.tree.answer(t, r) == TS.answer(t, r) : Tr.Ans}:
  match r:
    case Tr.Do{o}:
      match o:
        case Tr.Put{+k, +p, v}:
          %LB.ts.ok(t, k, p) : {Tree.tree.took(Tr.ok(t, k, p)) == TS.took(_) : Tr.Ans}
          ta.took(Tr.ok(t, k, p))
        case Tr.Del{x}:
          match x:
            case 0n:
              {==}
            case 1n++q:
              %LP.tp.prune(t, q, good) : {Tr.Cut{Tree.tree.lost(t, Tr.prune(t, 1n+q))} == Tr.Cut{TS.lost(t, _)} : Tr.Ans}
              %ta.lost(t, Tr.prune(t, 1n+q)) : {Tr.Cut{Tree.tree.lost(t, Tr.prune(t, 1n+q))} == Tr.Cut{_} : Tr.Ans}
              {==}
    case Tr.Rewind{+ops}:
      +st = LLogicBool.tree.pt.and_l(Tr.sorted(t), Tr.rooted(t), good)
      %LS.ts.patch(ops, t, st) : {Tree.tree.took(Tr.sound(Tr.patch(ops, t))) == TS.took(TS.valid(_)) : Tr.Ans}
      %LB.ts.sound(Tr.patch(ops, t)) : {Tree.tree.took(Tr.sound(Tr.patch(ops, t))) == TS.took(_) : Tr.Ans}
      ta.took(Tr.sound(Tr.patch(ops, t)))
