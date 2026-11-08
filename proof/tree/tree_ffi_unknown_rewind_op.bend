# eukhe: the proof of LAW tree_ffi_unknown_rewind_op
#
# PROOF: the note tag 0 and the rewind tag 1 read back (tf.rt); the count
# reads as itself or Bad, and so does the first op's tag (ws_nat_read); an
# op tag of 2 or more is no op, so the list is Bad however many ops it
# counts: the malformed error, the core kept.

import Base
import ../../bend/ffi_tree.bend as Ft
import ../../bend/tree.bend as Tr
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/tree.bend as Tree
import ../wire/base/spell.bend as LAWireSpell
import ./base/wire.bend as LAWire

def tw.op(+s: Tr.St, b: Bool, m: Nat, n: Nat, rest: String) -> {Ft.step.ask(s, Ft.get_ask.note(Ft.get_rec.rewind(Wr.get_list.go(~Tr.Op, ~Ft.get_op, m, Ft.get_op.go(LAWireSpell.ws_nat_answer(b, 2n+n, rest)))))) == (Ft.Live{s}, Wr.err("tree: malformed ask")) : Ft.St & String}:
  match b:
    case True{}:
      match m:
        case 0n:
          {==}
        case 1n+k:
          {==}
    case False{}:
      match m:
        case 0n:
          {==}
        case 1n+k:
          {==}

def tw.count(+s: Tr.St, b: Bool, +m: Nat, +n: Nat, +rest: String) -> {Ft.step.ask(s, Ft.get_ask.note(Ft.get_rec.rewind(Wr.get_list.start(~Tr.Op, ~Ft.get_op, LAWireSpell.ws_nat_answer(b, 1n+m, Wr.put_nat(2n+n, rest)))))) == (Ft.Live{s}, Wr.err("tree: malformed ask")) : Ft.St & String}:
  match b:
    case True{}:
      %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(2n+n, rest)), LAWireSpell.ws_nat_answer(LawsBase.wire_fits(2n+n), 2n+n, rest), LAWireSpell.ws_nat_read(2n+n, rest)) : {Ft.step.ask(s, Ft.get_ask.note(Ft.get_rec.rewind(Wr.get_list.go(~Tr.Op, ~Ft.get_op, m, Ft.get_op.go(_))))) == (Ft.Live{s}, Wr.err("tree: malformed ask")) : Ft.St & String}
      tw.op(s, LawsBase.wire_fits(2n+n), m, n, rest)
    case False{}:
      {==}

def Tree.tree_ffi_unknown_rewind_op(s, m, n, rest):
  +x = Wr.put_nat(1n+m, Wr.put_nat(2n+n, rest))
  %LAWire.tf.rt(0n, Wr.put_nat(1n, x), {==}) : {Ft.step.ask(s, Ft.get_ask.go(_)) == (Ft.Live{s}, Wr.err("tree: malformed ask")) : Ft.St & String}
  %LAWire.tf.rt(1n, x, {==}) : {Ft.step.ask(s, Ft.get_ask.note(Ft.get_rec.go(_))) == (Ft.Live{s}, Wr.err("tree: malformed ask")) : Ft.St & String}
  %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(x), LAWireSpell.ws_nat_answer(LawsBase.wire_fits(1n+m), 1n+m, Wr.put_nat(2n+n, rest)), LAWireSpell.ws_nat_read(1n+m, Wr.put_nat(2n+n, rest))) : {Ft.step.ask(s, Ft.get_ask.note(Ft.get_rec.rewind(Wr.get_list.start(~Tr.Op, ~Ft.get_op, _)))) == (Ft.Live{s}, Wr.err("tree: malformed ask")) : Ft.St & String}
  tw.count(s, LawsBase.wire_fits(1n+m), m, n, rest)
