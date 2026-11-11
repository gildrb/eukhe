# eukhe: lemma of LAW tree_core_plan: the model's rewind ops (Tr.diff) are
# the spec's (TS.diff, T6): its deletes keep the nodes of a whose key b
# lacks, its puts the nodes of b that a does not hold the same, as the
# spec's filters do; the lookups and the sameness are the spec's
# (LB.ts.has, LB.ts.get, LB.ts.same).

import Base
import ../../../bend/tree.bend as Tr
import ../../../spec/durable/tree.bend as TS
import ../tree_replay_spec/basic.bend as LB

def td.dels_at(c: Bool, +k: Nat, +p: Nat, +v: Nat, +rest: List<&2, Tr.Ent>, +b: List<&2, Tr.Ent>, ih: {Tr.dels(rest, b) == TS.diff.dels(rest, b) : List<&2, Tr.Op>}) -> {Tr.dels.go(Tr.Ent{k, p, v} <> rest, b, c) == TS.op.if(Bool.not(c), Tr.Del{k}, TS.diff.dels(rest, b)) : List<&2, Tr.Op>}:
  match c:
    case True{}:
      ih
    case False{}:
      %ih : {Tr.Del{k} <> Tr.dels(rest, b) == Tr.Del{k} <> _ : List<&2, Tr.Op>}
      {==}

def td.dels(s: List<&2, Tr.Ent>, +b: List<&2, Tr.Ent>) -> {Tr.dels(s, b) == TS.diff.dels(s, b) : List<&2, Tr.Op>}:
  match s:
    case Nil{}:
      {==}
    case +e <> +rest:
      match e:
        case Tr.Ent{+k, +p, +v}:
          %LB.ts.has(b, k) : {Tr.dels.go(Tr.Ent{k, p, v} <> rest, b, Tr.has(b, k)) == TS.op.if(Bool.not(_), Tr.Del{k}, TS.diff.dels(rest, b)) : List<&2, Tr.Op>}
          td.dels_at(Tr.has(b, k), k, p, v, rest, b, td.dels(rest, b))

def td.puts_at(c: Bool, +a: List<&2, Tr.Ent>, +k: Nat, +p: Nat, +v: Nat, +rest: List<&2, Tr.Ent>, ih: {Tr.puts(a, rest) == TS.diff.puts(a, rest) : List<&2, Tr.Op>}) -> {Tr.puts.go(a, Tr.Ent{k, p, v} <> rest, c) == TS.op.if(Bool.not(c), Tr.Put{k, p, v}, TS.diff.puts(a, rest)) : List<&2, Tr.Op>}:
  match c:
    case True{}:
      ih
    case False{}:
      %ih : {Tr.Put{k, p, v} <> Tr.puts(a, rest) == Tr.Put{k, p, v} <> _ : List<&2, Tr.Op>}
      {==}

def td.puts(+a: List<&2, Tr.Ent>, s: List<&2, Tr.Ent>) -> {Tr.puts(a, s) == TS.diff.puts(a, s) : List<&2, Tr.Op>}:
  match s:
    case Nil{}:
      {==}
    case +e <> +rest:
      match e:
        case Tr.Ent{+k, +p, +v}:
          +E = {Tr.Ent{k, p, v} : Tr.Ent}
          %LB.ts.get(a, k) : {Tr.puts.go(a, E <> rest, Tr.same(Tr.get(a, k), Some{E})) == TS.op.if(Bool.not(TS.same(_, E)), Tr.Put{k, p, v}, TS.diff.puts(a, rest)) : List<&2, Tr.Op>}
          %LB.ts.same(Tr.get(a, k), E) : {Tr.puts.go(a, E <> rest, Tr.same(Tr.get(a, k), Some{E})) == TS.op.if(Bool.not(_), Tr.Put{k, p, v}, TS.diff.puts(a, rest)) : List<&2, Tr.Op>}
          td.puts_at(Tr.same(Tr.get(a, k), Some{E}), a, k, p, v, rest, td.puts(a, rest))

# the model's rewind from a to b is the spec's
def td.diff(+a: List<&2, Tr.Ent>, +b: List<&2, Tr.Ent>) -> {Tr.diff(a, b) == TS.diff(a, b) : List<&2, Tr.Op>}:
  %td.dels(a, b) : {List.append(&2, Tr.Op, Tr.dels(a, b), Tr.puts(a, b)) == List.append(&2, Tr.Op, _, TS.diff.puts(a, b)) : List<&2, Tr.Op>}
  %td.puts(a, b) : {List.append(&2, Tr.Op, Tr.dels(a, b), Tr.puts(a, b)) == List.append(&2, Tr.Op, Tr.dels(a, b), _) : List<&2, Tr.Op>}
  {==}
