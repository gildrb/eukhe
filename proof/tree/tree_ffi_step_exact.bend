# eukhe: the proof of LAW tree_ffi_step_exact
#
# PROOF: the entry's ask decoder takes, stage by stage, the same branches
# on the same wire primitives as the spec's reader (ttx.op_* .. ttx.ask);
# a rewind's ops are read by the list reader, which wire_list_reads_items
# pins to the count and that many ops, each read by the entry's op reader
# as the spec's op reader reads it (ttx.op, ttx.then, ttx.list). The
# entry's answer writer is the spec's: a list of effects or nodes is its
# count then each item (wire_list_spells_items), each item spelled as the
# spec spells it (ttx.effs, ttx.ents). The two error texts are the spec's.

import Base
import ../../bend/ffi_tree.bend as Ft
import ../../bend/tree.bend as Tr
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/tree.bend as Tree
import ../../laws/wire.bend as Wire
import ../wire/wire_list_reads_items.bend as PWireListReadsItems
import ../wire/wire_list_spells_items.bend as PWireListSpellsItems

# Ops
# ---

def ttx.op_v(+k: Nat, +p: Nat, d: Wr.Dec<Nat>) -> {Ft.get_op.v(k, p, d) == Tree.tt_read_op.v(k, p, d) : Wr.Dec<Tr.Op>}:
  match d:
    case Wr.Got{v, s}:
      {==}
    case Wr.Bad{}:
      {==}

def ttx.op_p(+k: Nat, d: Wr.Dec<Nat>) -> {Ft.get_op.p(k, d) == Tree.tt_read_op.p(k, d) : Wr.Dec<Tr.Op>}:
  match d:
    case Wr.Got{+p, +s}:
      ttx.op_v(k, p, Wr.get_nat(s))
    case Wr.Bad{}:
      {==}

def ttx.op_put(d: Wr.Dec<Nat>) -> {Ft.get_op.put(d) == Tree.tt_read_op.put(d) : Wr.Dec<Tr.Op>}:
  match d:
    case Wr.Got{+k, +s}:
      ttx.op_p(k, Wr.get_nat(s))
    case Wr.Bad{}:
      {==}

def ttx.op_del(d: Wr.Dec<Nat>) -> {Ft.get_op.del(d) == Tree.tt_read_op.del(d) : Wr.Dec<Tr.Op>}:
  match d:
    case Wr.Got{k, s}:
      {==}
    case Wr.Bad{}:
      {==}

def ttx.op_go(d: Wr.Dec<Nat>) -> {Ft.get_op.go(d) == Tree.tt_read_op.tag(d) : Wr.Dec<Tr.Op>}:
  match d:
    case Wr.Got{t, +s}:
      match t:
        case 0n:
          ttx.op_put(Wr.get_nat(s))
        case 1n:
          ttx.op_del(Wr.get_nat(s))
        case 2n+x:
          {==}
    case Wr.Bad{}:
      {==}

# the entry's op reader is the spec's
def ttx.op(+s: String) -> {Ft.get_op(s) == Tree.tt_read_op(s) : Wr.Dec<Tr.Op>}:
  ttx.op_go(Wr.get_nat(s))

# m more ops after the op d answers, read by either op reader
def ttx.then(m: Nat, d: Wr.Dec<Tr.Op>) -> {LawsBase.wire_items.then(Tr.Op, d, x => LawsBase.wire_items(~Tr.Op, ~Ft.get_op, m, x)) == LawsBase.wire_items.then(Tr.Op, d, x => LawsBase.wire_items(~Tr.Op, ~Tree.tt_read_op, m, x)) : Wr.Dec<List<&2, Tr.Op>>}:
  match m:
    case 0n:
      match d:
        case Wr.Got{x, r}:
          {==}
        case Wr.Bad{}:
          {==}
    case 1n+j:
      match d:
        case Wr.Got{+x, +r}:
          +g = Tree.tt_read_op(r)
          %Equal.sym(Wr.Dec<Tr.Op>, Ft.get_op(r), g, ttx.op(r)) : {LawsBase.wire_items.cons(Tr.Op, x, LawsBase.wire_items.then(Tr.Op, _, y => LawsBase.wire_items(~Tr.Op, ~Ft.get_op, j, y))) == LawsBase.wire_items.cons(Tr.Op, x, LawsBase.wire_items.then(Tr.Op, g, y => LawsBase.wire_items(~Tr.Op, ~Tree.tt_read_op, j, y))) : Wr.Dec<List<&2, Tr.Op>>}
          %Equal.sym(Wr.Dec<List<&2, Tr.Op>>, LawsBase.wire_items.then(Tr.Op, g, y => LawsBase.wire_items(~Tr.Op, ~Ft.get_op, j, y)), LawsBase.wire_items.then(Tr.Op, g, y => LawsBase.wire_items(~Tr.Op, ~Tree.tt_read_op, j, y)), ttx.then(j, g)) : {LawsBase.wire_items.cons(Tr.Op, x, _) == LawsBase.wire_items.cons(Tr.Op, x, LawsBase.wire_items.then(Tr.Op, g, y => LawsBase.wire_items(~Tr.Op, ~Tree.tt_read_op, j, y))) : Wr.Dec<List<&2, Tr.Op>>}
          {==}
        case Wr.Bad{}:
          {==}

# a list of ops read by either op reader
def ttx.list(d: Wr.Dec<Nat>) -> {LawsBase.wire_read_list.count(~Tr.Op, ~Ft.get_op, d) == LawsBase.wire_read_list.count(~Tr.Op, ~Tree.tt_read_op, d) : Wr.Dec<List<&2, Tr.Op>>}:
  match d:
    case Wr.Got{n, +r}:
      match n:
        case 0n:
          {==}
        case 1n+j:
          +g = Tree.tt_read_op(r)
          %Equal.sym(Wr.Dec<Tr.Op>, Ft.get_op(r), g, ttx.op(r)) : {LawsBase.wire_items.then(Tr.Op, _, y => LawsBase.wire_items(~Tr.Op, ~Ft.get_op, j, y)) == LawsBase.wire_items.then(Tr.Op, g, y => LawsBase.wire_items(~Tr.Op, ~Tree.tt_read_op, j, y)) : Wr.Dec<List<&2, Tr.Op>>}
          ttx.then(j, g)
    case Wr.Bad{}:
      {==}

# Records and asks
# ----------------

def ttx.rec_do(d: Wr.Dec<Tr.Op>) -> {Ft.get_rec.do(d) == Tree.tt_read_rec.do(d) : Wr.Dec<Tr.Rec>}:
  match d:
    case Wr.Got{o, s}:
      {==}
    case Wr.Bad{}:
      {==}

def ttx.rec_rewind(d: Wr.Dec<List<&2, Tr.Op>>) -> {Ft.get_rec.rewind(d) == Tree.tt_read_rec.rewind(d) : Wr.Dec<Tr.Rec>}:
  match d:
    case Wr.Got{ops, s}:
      {==}
    case Wr.Bad{}:
      {==}

def ttx.rec(d: Wr.Dec<Nat>) -> {Ft.get_rec.go(d) == Tree.tt_read_rec.tag(d) : Wr.Dec<Tr.Rec>}:
  match d:
    case Wr.Got{t, +s}:
      match t:
        case 0n:
          %Equal.sym(Wr.Dec<Tr.Op>, Ft.get_op(s), Tree.tt_read_op(s), ttx.op(s)) : {Ft.get_rec.do(_) == Tree.tt_read_rec.do(Tree.tt_read_op(s)) : Wr.Dec<Tr.Rec>}
          ttx.rec_do(Tree.tt_read_op(s))
        case 1n:
          +sp = LawsBase.wire_read_list(~Tr.Op, ~Tree.tt_read_op, s)
          %Equal.sym(Wr.Dec<List<&2, Tr.Op>>, Wr.get_list(~Tr.Op, ~Ft.get_op, s), LawsBase.wire_read_list(~Tr.Op, ~Ft.get_op, s), Wire.wire_list_reads_items(~Tr.Op, ~Ft.get_op, s)) : {Ft.get_rec.rewind(_) == Tree.tt_read_rec.rewind(sp) : Wr.Dec<Tr.Rec>}
          %Equal.sym(Wr.Dec<List<&2, Tr.Op>>, LawsBase.wire_read_list(~Tr.Op, ~Ft.get_op, s), sp, ttx.list(Wr.get_nat(s))) : {Ft.get_rec.rewind(_) == Tree.tt_read_rec.rewind(sp) : Wr.Dec<Tr.Rec>}
          ttx.rec_rewind(sp)
        case 2n+x:
          {==}
    case Wr.Bad{}:
      {==}

def ttx.note(d: Wr.Dec<Tr.Rec>) -> {Ft.get_ask.note(d) == Tree.tt_read_ask.note(d) : Wr.Dec<Tr.Ask>}:
  match d:
    case Wr.Got{x, s}:
      {==}
    case Wr.Bad{}:
      {==}

def ttx.plan(d: Wr.Dec<Nat>) -> {Ft.get_ask.plan(d) == Tree.tt_read_ask.plan(d) : Wr.Dec<Tr.Ask>}:
  match d:
    case Wr.Got{n, s}:
      {==}
    case Wr.Bad{}:
      {==}

def ttx.snap(d: Wr.Dec<Nat>) -> {Ft.get_ask.snap(d) == Tree.tt_read_ask.snap(d) : Wr.Dec<Tr.Ask>}:
  match d:
    case Wr.Got{n, s}:
      {==}
    case Wr.Bad{}:
      {==}

# the entry's ask decoder reads as the spec's reader
def ttx.ask(d: Wr.Dec<Nat>) -> {Ft.get_ask.go(d) == Tree.tt_read_ask.tag(d) : Wr.Dec<Tr.Ask>}:
  match d:
    case Wr.Got{t, +s}:
      match t:
        case 0n:
          %Equal.sym(Wr.Dec<Tr.Rec>, Ft.get_rec.go(Wr.get_nat(s)), Tree.tt_read_rec.tag(Wr.get_nat(s)), ttx.rec(Wr.get_nat(s))) : {Ft.get_ask.note(_) == Tree.tt_read_ask.note(Tree.tt_read_rec.tag(Wr.get_nat(s))) : Wr.Dec<Tr.Ask>}
          ttx.note(Tree.tt_read_rec.tag(Wr.get_nat(s)))
        case 1n:
          ttx.plan(Wr.get_nat(s))
        case 2n:
          ttx.snap(Wr.get_nat(s))
        case 3n+x:
          {==}
    case Wr.Bad{}:
      {==}

# Answers
# -------

def ttx.eff(e: Tr.Eff, rest: String) -> {Ft.put_eff(e, rest) == Tree.tt_spell_eff(e, rest) : String}:
  match e:
    case Tr.Start{k}:
      {==}
    case Tr.Stop{k}:
      {==}
    case Tr.Restore{k}:
      {==}

def ttx.effs(es: List<&2, Tr.Eff>, +rest: String) -> {LawsBase.wire_put_items(~Tr.Eff, ~Ft.put_eff, es, rest) == LawsBase.wire_put_items(~Tr.Eff, ~Tree.tt_spell_eff, es, rest) : String}:
  match es:
    case Nil{}:
      {==}
    case +e <> +t:
      %ttx.effs(t, rest) : {Ft.put_eff(e, LawsBase.wire_put_items(~Tr.Eff, ~Ft.put_eff, t, rest)) == Tree.tt_spell_eff(e, _) : String}
      ttx.eff(e, LawsBase.wire_put_items(~Tr.Eff, ~Ft.put_eff, t, rest))

def ttx.ent(e: Tr.Ent, rest: String) -> {Ft.put_ent(e, rest) == Tree.tt_spell_ent(e, rest) : String}:
  match e:
    case Tr.Ent{k, p, v}:
      {==}

def ttx.ents(es: List<&2, Tr.Ent>, +rest: String) -> {LawsBase.wire_put_items(~Tr.Ent, ~Ft.put_ent, es, rest) == LawsBase.wire_put_items(~Tr.Ent, ~Tree.tt_spell_ent, es, rest) : String}:
  match es:
    case Nil{}:
      {==}
    case +e <> +t:
      %ttx.ents(t, rest) : {Ft.put_ent(e, LawsBase.wire_put_items(~Tr.Ent, ~Ft.put_ent, t, rest)) == Tree.tt_spell_ent(e, _) : String}
      ttx.ent(e, LawsBase.wire_put_items(~Tr.Ent, ~Ft.put_ent, t, rest))

# the entry spells every answer as the spec does
def ttx.ans(a: Tr.Ans) -> {Ft.put_ans(a, "") == Tree.tt_spell_ans(a) : String}:
  match a:
    case Tr.Kept{}:
      {==}
    case Tr.Took{}:
      {==}
    case Tr.Cut{ks}:
      {==}
    case Tr.Effects{+es}:
      +n = List.length(&2, Tr.Eff, es)
      %Equal.sym(String, Wr.put_list(~Tr.Eff, ~Ft.put_eff, es, ""), LawsBase.wire_dec(n, LawsBase.wire_put_items(~Tr.Eff, ~Ft.put_eff, es, "")), Wire.wire_list_spells_items(~Tr.Eff, ~Ft.put_eff, es, "")) : {Wr.put_nat(3n, _) == Tree.tt_spell_ans(Tr.Effects{es}) : String}
      %Equal.sym(String, Wr.put_list(~Tr.Eff, ~Tree.tt_spell_eff, es, ""), LawsBase.wire_dec(n, LawsBase.wire_put_items(~Tr.Eff, ~Tree.tt_spell_eff, es, "")), Wire.wire_list_spells_items(~Tr.Eff, ~Tree.tt_spell_eff, es, "")) : {Wr.put_nat(3n, LawsBase.wire_dec(n, LawsBase.wire_put_items(~Tr.Eff, ~Ft.put_eff, es, ""))) == Wr.put_nat(3n, _) : String}
      %ttx.effs(es, "") : {Wr.put_nat(3n, LawsBase.wire_dec(n, LawsBase.wire_put_items(~Tr.Eff, ~Ft.put_eff, es, ""))) == Wr.put_nat(3n, LawsBase.wire_dec(n, _)) : String}
      {==}
    case Tr.Nodes{+es}:
      +n = List.length(&2, Tr.Ent, es)
      %Equal.sym(String, Wr.put_list(~Tr.Ent, ~Ft.put_ent, es, ""), LawsBase.wire_dec(n, LawsBase.wire_put_items(~Tr.Ent, ~Ft.put_ent, es, "")), Wire.wire_list_spells_items(~Tr.Ent, ~Ft.put_ent, es, "")) : {Wr.put_nat(4n, _) == Tree.tt_spell_ans(Tr.Nodes{es}) : String}
      %Equal.sym(String, Wr.put_list(~Tr.Ent, ~Tree.tt_spell_ent, es, ""), LawsBase.wire_dec(n, LawsBase.wire_put_items(~Tr.Ent, ~Tree.tt_spell_ent, es, "")), Wire.wire_list_spells_items(~Tr.Ent, ~Tree.tt_spell_ent, es, "")) : {Wr.put_nat(4n, LawsBase.wire_dec(n, LawsBase.wire_put_items(~Tr.Ent, ~Ft.put_ent, es, ""))) == Wr.put_nat(4n, _) : String}
      %ttx.ents(es, "") : {Wr.put_nat(4n, LawsBase.wire_dec(n, LawsBase.wire_put_items(~Tr.Ent, ~Ft.put_ent, es, ""))) == Wr.put_nat(4n, LawsBase.wire_dec(n, _)) : String}
      {==}

# The step
# --------

def ttx.step_ans(r: Tr.St & Tr.Ans) -> {Ft.step.ans(r) == Tree.tt_step.ans(r) : Ft.St & String}:
  match r:
    case (s, +a):
      %ttx.ans(a) : {(Ft.Live{s}, Ft.put_ans(a, "")) == (Ft.Live{s}, _) : Ft.St & String}
      {==}

def ttx.end(+s: Tr.St, q: Tr.Ask, r: String) -> {Ft.step.end(Wr.end(r), s, q) == Tree.tt_step.ask(s, Wr.Got{q, r}) : Ft.St & String}:
  match r:
    case SNil{}:
      ttx.step_ans(Tr.core.step(s, q))
    case SCon{c, t}:
      {==}

def ttx.go(+s: Tr.St, d: Wr.Dec<Tr.Ask>) -> {Ft.step.ask(s, d) == Tree.tt_step.ask(s, d) : Ft.St & String}:
  match d:
    case Wr.Got{q, r}:
      ttx.end(s, q, r)
    case Wr.Bad{}:
      {==}

def Tree.tree_ffi_step_exact(s, input):
  %ttx.ask(Wr.get_nat(input)) : {Ft.step(Ft.Live{s}, input) == Tree.tt_step.ask(s, _) : Ft.St & String}
  ttx.go(s, Ft.get_ask(input))
