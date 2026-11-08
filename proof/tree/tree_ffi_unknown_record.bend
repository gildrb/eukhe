# eukhe: the proof of LAW tree_ffi_unknown_record
#
# PROOF: the note tag 0 reads back (tf.rt); the record tag reads as itself
# or Bad (ws_nat_read); a tag of 2 or more is no record: Bad, the malformed
# error, the core kept.

import Base
import ../../bend/ffi_tree.bend as Ft
import ../../bend/tree.bend as Tr
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/tree.bend as Tree
import ../wire/base/spell.bend as LAWireSpell
import ./base/wire.bend as LAWire

def tu.rec(+s: Tr.St, b: Bool, n: Nat, rest: String) -> {Ft.step.ask(s, Ft.get_ask.note(Ft.get_rec.go(LAWireSpell.ws_nat_answer(b, 2n+n, rest)))) == (Ft.Live{s}, Wr.err("tree: malformed ask")) : Ft.St & String}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def Tree.tree_ffi_unknown_record(s, n, rest):
  %LAWire.tf.rt(0n, Wr.put_nat(2n+n, rest), {==}) : {Ft.step.ask(s, Ft.get_ask.go(_)) == (Ft.Live{s}, Wr.err("tree: malformed ask")) : Ft.St & String}
  %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(2n+n, rest)), LAWireSpell.ws_nat_answer(LawsBase.wire_fits(2n+n), 2n+n, rest), LAWireSpell.ws_nat_read(2n+n, rest)) : {Ft.step.ask(s, Ft.get_ask.note(Ft.get_rec.go(_))) == (Ft.Live{s}, Wr.err("tree: malformed ask")) : Ft.St & String}
  tu.rec(s, LawsBase.wire_fits(2n+n), n, rest)
