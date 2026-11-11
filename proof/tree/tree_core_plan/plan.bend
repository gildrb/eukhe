# eukhe: lemma of LAW tree_core_plan: the spec's work of the spec's rewind
# from a to b (TS.effects of TS.diff, T6/T7) is the plan R3 states
# (tree.plan): the work of the deletes is a stop for each node of a whose
# key b lacks (pl.dels), the work of the puts a start or a restore for each
# node of b that a does not hold the same (pl.puts), and the work of the
# ops one after another is the work of each (pl.eff_app).

import Base
import ../../../bend/tree.bend as Tr
import ../../../laws/tree.bend as Tree
import ../../../spec/durable/tree.bend as TS

# the work of two runs of ops, one after another
def pl.eff_app(xs: List<&2, Tr.Op>, +ys: List<&2, Tr.Op>, +t: List<&2, Tr.Ent>) -> {TS.effects(List.append(&2, Tr.Op, xs, ys), t) == List.append(&2, Tr.Eff, TS.effects(xs, t), TS.effects(ys, t)) : List<&2, Tr.Eff>}:
  match xs:
    case Nil{}:
      {==}
    case o <> rest:
      match o:
        case Tr.Del{k}:
          Equal.cong(List<&2, Tr.Eff>, List<&2, Tr.Eff>, l => Tr.Stop{k} <> l, TS.effects(List.append(&2, Tr.Op, rest, ys), t), List.append(&2, Tr.Eff, TS.effects(rest, t), TS.effects(ys, t)), pl.eff_app(rest, ys, t))
        case Tr.Put{+k, p, v}:
          Equal.cong(List<&2, Tr.Eff>, List<&2, Tr.Eff>, l => TS.effect(TS.has(t, k), k) <> l, TS.effects(List.append(&2, Tr.Op, rest, ys), t), List.append(&2, Tr.Eff, TS.effects(rest, t), TS.effects(ys, t)), pl.eff_app(rest, ys, t))

def pl.stop_at(c: Bool, +k: Nat, -D: List<&2, Tr.Op>, -S: List<&2, Tr.Eff>, -t: List<&2, Tr.Ent>, ih: {TS.effects(D, t) == S : List<&2, Tr.Eff>}) -> {TS.effects(TS.op.if(Bool.not(c), Tr.Del{k}, D), t) == Tree.tree.stop.at(c, k, S) : List<&2, Tr.Eff>}:
  match c:
    case True{}:
      ih
    case False{}:
      Equal.cong(List<&2, Tr.Eff>, List<&2, Tr.Eff>, l => Tr.Stop{k} <> l, TS.effects(D, t), S, ih)

# the work of the deletes of the nodes of s whose key b lacks
def pl.dels(s: List<&2, Tr.Ent>, +b: List<&2, Tr.Ent>, +t: List<&2, Tr.Ent>) -> {TS.effects(TS.diff.dels(s, b), t) == Tree.tree.stops(s, b) : List<&2, Tr.Eff>}:
  match s:
    case Nil{}:
      {==}
    case e <> +rest:
      match e:
        case Tr.Ent{+k, p, v}:
          pl.stop_at(TS.has(b, k), k, TS.diff.dels(rest, b), Tree.tree.stops(rest, b), t, pl.dels(rest, b, t))

# the work of a put: a restore when held, a start when not
def pl.eff_at(h: Bool, +k: Nat, -X: List<&2, Tr.Eff>, -Y: List<&2, Tr.Eff>, e: {X == Y : List<&2, Tr.Eff>}) -> {TS.effect(h, k) <> X == Tree.tree.start.at(False{}, h, k, Y) : List<&2, Tr.Eff>}:
  match h:
    case True{}:
      Equal.cong(List<&2, Tr.Eff>, List<&2, Tr.Eff>, l => Tr.Restore{k} <> l, X, Y, e)
    case False{}:
      Equal.cong(List<&2, Tr.Eff>, List<&2, Tr.Eff>, l => Tr.Start{k} <> l, X, Y, e)

def pl.start_at(c: Bool, +k: Nat, p: Nat, v: Nat, -D: List<&2, Tr.Op>, -S: List<&2, Tr.Eff>, +t: List<&2, Tr.Ent>, ih: {TS.effects(D, t) == S : List<&2, Tr.Eff>}) -> {TS.effects(TS.op.if(Bool.not(c), Tr.Put{k, p, v}, D), t) == Tree.tree.start.at(c, TS.has(t, k), k, S) : List<&2, Tr.Eff>}:
  match c:
    case True{}:
      ih
    case False{}:
      pl.eff_at(TS.has(t, k), k, TS.effects(D, t), S, ih)

# the work of the puts of the nodes of s that a does not hold the same
def pl.puts(+a: List<&2, Tr.Ent>, s: List<&2, Tr.Ent>) -> {TS.effects(TS.diff.puts(a, s), a) == Tree.tree.starts(a, s) : List<&2, Tr.Eff>}:
  match s:
    case Nil{}:
      {==}
    case e <> +rest:
      match e:
        case Tr.Ent{+k, +p, +v}:
          pl.start_at(TS.same(TS.get(a, k), Tr.Ent{k, p, v}), k, p, v, TS.diff.puts(a, rest), Tree.tree.starts(a, rest), a, pl.puts(a, rest))

# the spec's work of the spec's rewind from a to b is the plan R3 states
def pl.plan(+a: List<&2, Tr.Ent>, +b: List<&2, Tr.Ent>) -> {TS.effects(TS.diff(a, b), a) == Tree.tree.plan(a, b) : List<&2, Tr.Eff>}:
  %pl.dels(a, b, a) : {TS.effects(TS.diff(a, b), a) == List.append(&2, Tr.Eff, _, Tree.tree.starts(a, b)) : List<&2, Tr.Eff>}
  %pl.puts(a, b) : {TS.effects(TS.diff(a, b), a) == List.append(&2, Tr.Eff, TS.effects(TS.diff.dels(a, b), a), _) : List<&2, Tr.Eff>}
  pl.eff_app(TS.diff.dels(a, b), TS.diff.puts(a, b), a)
