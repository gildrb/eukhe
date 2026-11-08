# eukhe: lemmas the proofs of area tree share: the entry's encoders are
# the laws' spelling (tree.spell_*), item by item; an answer never opens
# with 'E'; a step's reply is its pair's parts, the answer spelled

import Base
import ../../../bend/ffi_tree.bend as Ft
import ../../../bend/tree.bend as Tr
import ../../../bend/wire.bend as Wr
import ../../../laws/base.bend as LawsBase
import ../../../laws/tree.bend as Tree
import ../../../laws/wire.bend as Wire
import ../../wire/wire_nat_not_err.bend as PWireNatNotErr
import ../../wire/wire_nats_spells.bend as PWireNatsSpells

# an op
def ts.op(o: Tr.Op, -rest: String) -> {Ft.put_op(o, rest) == Tree.tree.spell_op(o, rest) : String}:
  match o:
    case Tr.Put{k, p, v}:
      {==}
    case Tr.Del{k}:
      {==}

def ts.ops_go(ops: List<&2, Tr.Op>, +rest: String) -> {Wr.put_list.go(~Tr.Op, ~Ft.put_op, ops, rest) == (List.length(&2, Tr.Op, ops), Tree.tree.spell_ops(ops, rest)) : Nat & String}:
  match ops:
    case Nil{}:
      {==}
    case +o <> +r:
      %Equal.sym(Nat & String, Wr.put_list.go(~Tr.Op, ~Ft.put_op, r, rest), (List.length(&2, Tr.Op, r), Tree.tree.spell_ops(r, rest)), ts.ops_go(r, rest)) : {Wr.put_list.step(~Tr.Op, ~Ft.put_op, o, _) == (1n+List.length(&2, Tr.Op, r), Tree.tree.spell_op(o, Tree.tree.spell_ops(r, rest))) : Nat & String}
      %ts.op(o, Tree.tree.spell_ops(r, rest)) : {(1n+List.length(&2, Tr.Op, r), Ft.put_op(o, Tree.tree.spell_ops(r, rest))) == (1n+List.length(&2, Tr.Op, r), _) : Nat & String}
      {==}

# the ops of a rewind: their count, then each op spelled
def ts.ops(+ops: List<&2, Tr.Op>, +rest: String) -> {Wr.put_list(~Tr.Op, ~Ft.put_op, ops, rest) == Wr.put_nat(List.length(&2, Tr.Op, ops), Tree.tree.spell_ops(ops, rest)) : String}:
  Equal.cong(Nat & String, String, x => Wr.put_list.fin(x), Wr.put_list.go(~Tr.Op, ~Ft.put_op, ops, rest), (List.length(&2, Tr.Op, ops), Tree.tree.spell_ops(ops, rest)), ts.ops_go(ops, rest))

# an ask
def ts.ask(q: Tr.Ask, +rest: String) -> {Ft.put_ask(q, rest) == Tree.tree.spell_ask(q, rest) : String}:
  match q:
    case Tr.Note{r}:
      match r:
        case Tr.Do{+o}:
          Equal.cong(String, String, z => Wr.put_nat(0n, Wr.put_nat(0n, z)), Ft.put_op(o, rest), Tree.tree.spell_op(o, rest), ts.op(o, rest))
        case Tr.Rewind{+ops}:
          Equal.cong(String, String, z => Wr.put_nat(0n, Wr.put_nat(1n, z)), Wr.put_list(~Tr.Op, ~Ft.put_op, ops, rest), Wr.put_nat(List.length(&2, Tr.Op, ops), Tree.tree.spell_ops(ops, rest)), ts.ops(ops, rest))
    case Tr.Plan{n}:
      {==}
    case Tr.Snap{n}:
      {==}

# an effect
def ts.eff(e: Tr.Eff, -rest: String) -> {Ft.put_eff(e, rest) == Tree.tree.spell_eff(e, rest) : String}:
  match e:
    case Tr.Start{k}:
      {==}
    case Tr.Stop{k}:
      {==}
    case Tr.Restore{k}:
      {==}

def ts.effs_go(es: List<&2, Tr.Eff>, +rest: String) -> {Wr.put_list.go(~Tr.Eff, ~Ft.put_eff, es, rest) == (List.length(&2, Tr.Eff, es), Tree.tree.spell_effs(es, rest)) : Nat & String}:
  match es:
    case Nil{}:
      {==}
    case +e <> +r:
      %Equal.sym(Nat & String, Wr.put_list.go(~Tr.Eff, ~Ft.put_eff, r, rest), (List.length(&2, Tr.Eff, r), Tree.tree.spell_effs(r, rest)), ts.effs_go(r, rest)) : {Wr.put_list.step(~Tr.Eff, ~Ft.put_eff, e, _) == (1n+List.length(&2, Tr.Eff, r), Tree.tree.spell_eff(e, Tree.tree.spell_effs(r, rest))) : Nat & String}
      %ts.eff(e, Tree.tree.spell_effs(r, rest)) : {(1n+List.length(&2, Tr.Eff, r), Ft.put_eff(e, Tree.tree.spell_effs(r, rest))) == (1n+List.length(&2, Tr.Eff, r), _) : Nat & String}
      {==}

def ts.effs(+es: List<&2, Tr.Eff>, +rest: String) -> {Wr.put_list(~Tr.Eff, ~Ft.put_eff, es, rest) == Wr.put_nat(List.length(&2, Tr.Eff, es), Tree.tree.spell_effs(es, rest)) : String}:
  Equal.cong(Nat & String, String, x => Wr.put_list.fin(x), Wr.put_list.go(~Tr.Eff, ~Ft.put_eff, es, rest), (List.length(&2, Tr.Eff, es), Tree.tree.spell_effs(es, rest)), ts.effs_go(es, rest))

# a node
def ts.ent(e: Tr.Ent, -rest: String) -> {Ft.put_ent(e, rest) == Tree.tree.spell_ent(e, rest) : String}:
  match e:
    case Tr.Ent{k, p, v}:
      {==}

def ts.ents_go(es: List<&2, Tr.Ent>, +rest: String) -> {Wr.put_list.go(~Tr.Ent, ~Ft.put_ent, es, rest) == (List.length(&2, Tr.Ent, es), Tree.tree.spell_ents(es, rest)) : Nat & String}:
  match es:
    case Nil{}:
      {==}
    case +e <> +r:
      %Equal.sym(Nat & String, Wr.put_list.go(~Tr.Ent, ~Ft.put_ent, r, rest), (List.length(&2, Tr.Ent, r), Tree.tree.spell_ents(r, rest)), ts.ents_go(r, rest)) : {Wr.put_list.step(~Tr.Ent, ~Ft.put_ent, e, _) == (1n+List.length(&2, Tr.Ent, r), Tree.tree.spell_ent(e, Tree.tree.spell_ents(r, rest))) : Nat & String}
      %ts.ent(e, Tree.tree.spell_ents(r, rest)) : {(1n+List.length(&2, Tr.Ent, r), Ft.put_ent(e, Tree.tree.spell_ents(r, rest))) == (1n+List.length(&2, Tr.Ent, r), _) : Nat & String}
      {==}

def ts.ents(+es: List<&2, Tr.Ent>, +rest: String) -> {Wr.put_list(~Tr.Ent, ~Ft.put_ent, es, rest) == Wr.put_nat(List.length(&2, Tr.Ent, es), Tree.tree.spell_ents(es, rest)) : String}:
  Equal.cong(Nat & String, String, x => Wr.put_list.fin(x), Wr.put_list.go(~Tr.Ent, ~Ft.put_ent, es, rest), (List.length(&2, Tr.Ent, es), Tree.tree.spell_ents(es, rest)), ts.ents_go(es, rest))

# an answer
def ts.ans(a: Tr.Ans, +rest: String) -> {Ft.put_ans(a, rest) == Tree.tree.spell_ans(a, rest) : String}:
  match a:
    case Tr.Kept{}:
      {==}
    case Tr.Took{}:
      {==}
    case Tr.Cut{+ks}:
      Equal.cong(String, String, z => Wr.put_nat(2n, z), Wr.put_list(~Nat, ~Wr.put_nat, ks, rest), LawsBase.wire_spell_nats(ks, rest), Wire.wire_nats_spells(ks, rest))
    case Tr.Effects{+es}:
      Equal.cong(String, String, z => Wr.put_nat(3n, z), Wr.put_list(~Tr.Eff, ~Ft.put_eff, es, rest), Wr.put_nat(List.length(&2, Tr.Eff, es), Tree.tree.spell_effs(es, rest)), ts.effs(es, rest))
    case Tr.Nodes{+es}:
      Equal.cong(String, String, z => Wr.put_nat(4n, z), Wr.put_list(~Tr.Ent, ~Ft.put_ent, es, rest), Wr.put_nat(List.length(&2, Tr.Ent, es), Tree.tree.spell_ents(es, rest)), ts.ents(es, rest))

# an answer opens with its tag: never 'E'
def ts.ans_ok(a: Tr.Ans, rest: String) -> {LawsBase.wire_opens_err(Ft.put_ans(a, rest)) == False{} : Bool}:
  match a:
    case Tr.Kept{}:
      Wire.wire_nat_not_err(0n, rest)
    case Tr.Took{}:
      Wire.wire_nat_not_err(1n, rest)
    case Tr.Cut{ks}:
      Wire.wire_nat_not_err(2n, Wr.put_list(~Nat, ~Wr.put_nat, ks, rest))
    case Tr.Effects{es}:
      Wire.wire_nat_not_err(3n, Wr.put_list(~Tr.Eff, ~Ft.put_eff, es, rest))
    case Tr.Nodes{es}:
      Wire.wire_nat_not_err(4n, Wr.put_list(~Tr.Ent, ~Ft.put_ent, es, rest))

# a step's reply is the pair's parts
def ts.step_put(r: Tr.St & Tr.Ans) -> {Ft.step.ans(r) == (Ft.Live{Pair.fst(Tr.St, Tr.Ans, r)}, Ft.put_ans(Pair.snd(Tr.St, Tr.Ans, r), "")) : Ft.St & String}:
  (st, a) = r
  {==}

# a step's reply is the pair's parts, the answer spelled
def ts.step_ans(r: Tr.St & Tr.Ans) -> {Ft.step.ans(r) == (Ft.Live{Pair.fst(Tr.St, Tr.Ans, r)}, Tree.tree.spell_ans(Pair.snd(Tr.St, Tr.Ans, r), "")) : Ft.St & String}:
  (st, +a) = r
  Equal.cong(String, Ft.St & String, z => (Ft.Live{st}, z), Ft.put_ans(a, ""), Tree.tree.spell_ans(a, ""), ts.ans(a, ""))
