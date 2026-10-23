# eukhe: lemmas the proofs of area tree share: wire

import Base
import ../../../bend/ffi_tree.bend as Ft
import ../../../bend/tree.bend as Tr
import ../../../bend/wire.bend as Wr
import ../../../laws/base.bend as LawsBase
import ../../../laws/tree.bend as Tree
import ../../../laws/wire.bend as Wire
import ../../base/logic/bool.bend as LLogicBool
import ../../base/wire.bend as LWire
import ./logic.bend as LALogic

# ---- tree_ffi ----

# proof_tree_ffi: the laws of LAWS.bend section tree_ffi (the entry of
# bend/ffi_tree.bend). Round trip: each field reads back by the wire law
# wire_nat_round_trip, a tag picks its constructor, and the ops of a
# rewind read back item by item (tf.ops_rt, after the list lemmas of
# section wire). The entry laws rewrite the decoded ask into the entry;
# a step's reply splits its pair (tf.ans).

# the Nat round trip, turned for rewriting
def tf.rt(+n: Nat, +rest: String, h: {LawsBase.wire_fits(n) == True{} : Bool}) -> {Wr.Got{n, rest} == Wr.get_nat(Wr.put_nat(n, rest)) : Wr.Dec<Nat>}:
  Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(n, rest)), Wr.Got{n, rest}, Wire.wire_nat_round_trip(n, rest, h))

def tf.op_rt(o: Tr.Op, +rest: String, +h: {Tree.tree.op_fits(o) == True{} : Bool}) -> {Ft.get_op(Ft.put_op(o, rest)) == Wr.Got{o, rest} : Wr.Dec<Tr.Op>}:
  match o:
    case Tr.Put{+k, +p, +v}:
      +O = {Tr.Put{k, p, v} : Tr.Op}
      +hpv = LLogicBool.wr_and_r(LawsBase.wire_fits(k), Bool.and(LawsBase.wire_fits(p), LawsBase.wire_fits(v)), h)
      %tf.rt(0n, Wr.put_nat(k, Wr.put_nat(p, Wr.put_nat(v, rest))), {==}) : {Ft.get_op.go(_) == Wr.Got{O, rest} : Wr.Dec<Tr.Op>}
      %tf.rt(k, Wr.put_nat(p, Wr.put_nat(v, rest)), LLogicBool.wr_and_l(LawsBase.wire_fits(k), Bool.and(LawsBase.wire_fits(p), LawsBase.wire_fits(v)), h)) : {Ft.get_op.put(_) == Wr.Got{O, rest} : Wr.Dec<Tr.Op>}
      %tf.rt(p, Wr.put_nat(v, rest), LLogicBool.wr_and_l(LawsBase.wire_fits(p), LawsBase.wire_fits(v), hpv)) : {Ft.get_op.p(k, _) == Wr.Got{O, rest} : Wr.Dec<Tr.Op>}
      %tf.rt(v, rest, LLogicBool.wr_and_r(LawsBase.wire_fits(p), LawsBase.wire_fits(v), hpv)) : {Ft.get_op.v(k, p, _) == Wr.Got{O, rest} : Wr.Dec<Tr.Op>}
      {==}
    case Tr.Del{+k}:
      %tf.rt(1n, Wr.put_nat(k, rest), {==}) : {Ft.get_op.go(_) == Wr.Got{Tr.Del{k}, rest} : Wr.Dec<Tr.Op>}
      %tf.rt(k, rest, h) : {Ft.get_op.del(_) == Wr.Got{Tr.Del{k}, rest} : Wr.Dec<Tr.Op>}
      {==}

def tf.go(ops: List<&2, Tr.Op>, +rest: String) -> {Wr.put_list.go(~Tr.Op, ~Ft.put_op, ops, rest) == (List.length(&2, Tr.Op, ops), LALogic.tf.items(ops, rest)) : Nat & String}:
  match ops:
    case Nil{}:
      {==}
    case +o <> +r:
      %Equal.sym(Nat & String, Wr.put_list.go(~Tr.Op, ~Ft.put_op, r, rest), (List.length(&2, Tr.Op, r), LALogic.tf.items(r, rest)), tf.go(r, rest)) : {Wr.put_list.step(~Tr.Op, ~Ft.put_op, o, _) == (1n+List.length(&2, Tr.Op, r), Ft.put_op(o, LALogic.tf.items(r, rest))) : Nat & String}
      {==}

# a list of ops is its count, then its items
def tf.put_list(+ops: List<&2, Tr.Op>, +rest: String) -> {Wr.put_list(~Tr.Op, ~Ft.put_op, ops, rest) == Wr.put_nat(List.length(&2, Tr.Op, ops), LALogic.tf.items(ops, rest)) : String}:
  Equal.cong(Nat & String, String, x => Wr.put_list.fin(x), Wr.put_list.go(~Tr.Op, ~Ft.put_op, ops, rest), (List.length(&2, Tr.Op, ops), LALogic.tf.items(ops, rest)), tf.go(ops, rest))

def tf.list_go(ops: List<&2, Tr.Op>, +o: Tr.Op, +rest: String, +hf: {Tree.tree.ops_fit(o <> ops) == True{} : Bool}) -> {Wr.get_list.go(~Tr.Op, ~Ft.get_op, List.length(&2, Tr.Op, ops), Ft.get_op(Ft.put_op(o, LALogic.tf.items(ops, rest)))) == Wr.Got{o <> ops, rest} : Wr.Dec<List<&2, Tr.Op>>}:
  match ops:
    case Nil{}:
      %Equal.sym(Wr.Dec<Tr.Op>, Ft.get_op(Ft.put_op(o, rest)), Wr.Got{o, rest}, tf.op_rt(o, rest, LALogic.tf.fit_l(o, Nil{}, hf))) : {Wr.get_list.go(~Tr.Op, ~Ft.get_op, 0n, _) == Wr.Got{[o], rest} : Wr.Dec<List<&2, Tr.Op>>}
      {==}
    case +o2 <> +ops2:
      %Equal.sym(Wr.Dec<Tr.Op>, Ft.get_op(Ft.put_op(o, LALogic.tf.items(o2 <> ops2, rest))), Wr.Got{o, LALogic.tf.items(o2 <> ops2, rest)}, tf.op_rt(o, LALogic.tf.items(o2 <> ops2, rest), LALogic.tf.fit_l(o, o2 <> ops2, hf))) : {Wr.get_list.go(~Tr.Op, ~Ft.get_op, 1n+List.length(&2, Tr.Op, ops2), _) == Wr.Got{o <> o2 <> ops2, rest} : Wr.Dec<List<&2, Tr.Op>>}
      %Equal.sym(Wr.Dec<List<&2, Tr.Op>>, Wr.get_list.go(~Tr.Op, ~Ft.get_op, List.length(&2, Tr.Op, ops2), Ft.get_op(Ft.put_op(o2, LALogic.tf.items(ops2, rest)))), Wr.Got{o2 <> ops2, rest}, tf.list_go(ops2, o2, rest, LALogic.tf.fit_r(o, o2 <> ops2, hf))) : {Wr.get_list.cons(Tr.Op, o, _) == Wr.Got{o <> o2 <> ops2, rest} : Wr.Dec<List<&2, Tr.Op>>}
      {==}

def tf.list_start(ops: List<&2, Tr.Op>, +rest: String, +hf: {Tree.tree.ops_fit(ops) == True{} : Bool}) -> {Wr.get_list.start(~Tr.Op, ~Ft.get_op, Wr.Got{List.length(&2, Tr.Op, ops), LALogic.tf.items(ops, rest)}) == Wr.Got{ops, rest} : Wr.Dec<List<&2, Tr.Op>>}:
  match ops:
    case Nil{}:
      {==}
    case +o <> +r:
      tf.list_go(r, o, rest, hf)

# a list of ops that fits reads back
def tf.ops_rt(+ops: List<&2, Tr.Op>, +rest: String, hl: {LawsBase.wire_fits(List.length(&2, Tr.Op, ops)) == True{} : Bool}, +hf: {Tree.tree.ops_fit(ops) == True{} : Bool}) -> {Wr.get_list(~Tr.Op, ~Ft.get_op, Wr.put_list(~Tr.Op, ~Ft.put_op, ops, rest)) == Wr.Got{ops, rest} : Wr.Dec<List<&2, Tr.Op>>}:
  %Equal.sym(String, Wr.put_list(~Tr.Op, ~Ft.put_op, ops, rest), Wr.put_nat(List.length(&2, Tr.Op, ops), LALogic.tf.items(ops, rest)), tf.put_list(ops, rest)) : {Wr.get_list(~Tr.Op, ~Ft.get_op, _) == Wr.Got{ops, rest} : Wr.Dec<List<&2, Tr.Op>>}
  %tf.rt(List.length(&2, Tr.Op, ops), LALogic.tf.items(ops, rest), hl) : {Wr.get_list.start(~Tr.Op, ~Ft.get_op, _) == Wr.Got{ops, rest} : Wr.Dec<List<&2, Tr.Op>>}
  tf.list_start(ops, rest, hf)

# an ask
# ------

def tf.ask_rt(q: Tr.Ask, +rest: String, +h: {Tree.tree.ask_fits(q) == True{} : Bool}) -> {Ft.get_ask(Ft.put_ask(q, rest)) == Wr.Got{q, rest} : Wr.Dec<Tr.Ask>}:
  match q:
    case Tr.Note{r}:
      match r:
        case Tr.Do{+o}:
          +Q = {Tr.Note{Tr.Do{o}} : Tr.Ask}
          %tf.rt(0n, Wr.put_nat(0n, Ft.put_op(o, rest)), {==}) : {Ft.get_ask.go(_) == Wr.Got{Q, rest} : Wr.Dec<Tr.Ask>}
          %tf.rt(0n, Ft.put_op(o, rest), {==}) : {Ft.get_ask.note(Ft.get_rec.go(_)) == Wr.Got{Q, rest} : Wr.Dec<Tr.Ask>}
          %Equal.sym(Wr.Dec<Tr.Op>, Ft.get_op(Ft.put_op(o, rest)), Wr.Got{o, rest}, tf.op_rt(o, rest, h)) : {Ft.get_ask.note(Ft.get_rec.do(_)) == Wr.Got{Q, rest} : Wr.Dec<Tr.Ask>}
          {==}
        case Tr.Rewind{+ops}:
          +Q = {Tr.Note{Tr.Rewind{ops}} : Tr.Ask}
          +s2 = Wr.put_list(~Tr.Op, ~Ft.put_op, ops, rest)
          %tf.rt(0n, Wr.put_nat(1n, s2), {==}) : {Ft.get_ask.go(_) == Wr.Got{Q, rest} : Wr.Dec<Tr.Ask>}
          %tf.rt(1n, s2, {==}) : {Ft.get_ask.note(Ft.get_rec.go(_)) == Wr.Got{Q, rest} : Wr.Dec<Tr.Ask>}
          %Equal.sym(Wr.Dec<List<&2, Tr.Op>>, Wr.get_list(~Tr.Op, ~Ft.get_op, s2), Wr.Got{ops, rest}, tf.ops_rt(ops, rest, LLogicBool.wr_and_l(LawsBase.wire_fits(List.length(&2, Tr.Op, ops)), Tree.tree.ops_fit(ops), h), LLogicBool.wr_and_r(LawsBase.wire_fits(List.length(&2, Tr.Op, ops)), Tree.tree.ops_fit(ops), h))) : {Ft.get_ask.note(Ft.get_rec.rewind(_)) == Wr.Got{Q, rest} : Wr.Dec<Tr.Ask>}
          {==}
    case Tr.Plan{+n}:
      %tf.rt(1n, Wr.put_nat(n, rest), {==}) : {Ft.get_ask.go(_) == Wr.Got{Tr.Plan{n}, rest} : Wr.Dec<Tr.Ask>}
      %tf.rt(n, rest, h) : {Ft.get_ask.plan(_) == Wr.Got{Tr.Plan{n}, rest} : Wr.Dec<Tr.Ask>}
      {==}
    case Tr.Snap{+n}:
      %tf.rt(2n, Wr.put_nat(n, rest), {==}) : {Ft.get_ask.go(_) == Wr.Got{Tr.Snap{n}, rest} : Wr.Dec<Tr.Ask>}
      %tf.rt(n, rest, h) : {Ft.get_ask.snap(_) == Wr.Got{Tr.Snap{n}, rest} : Wr.Dec<Tr.Ask>}
      {==}
