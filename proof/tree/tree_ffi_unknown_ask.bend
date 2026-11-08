# eukhe: the proof of LAW tree_ffi_unknown_ask
#
# PROOF: the ask tag reads as itself or Bad (ws_nat_read); a tag of 3 or
# more is no ask: Bad, the malformed error, the core kept.

import Base
import ../../bend/ffi_tree.bend as Ft
import ../../bend/tree.bend as Tr
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/tree.bend as Tree
import ../wire/base/spell.bend as LAWireSpell

def tu.ask(+s: Tr.St, b: Bool, n: Nat, rest: String) -> {Ft.step.ask(s, Ft.get_ask.go(LAWireSpell.ws_nat_answer(b, 3n+n, rest))) == (Ft.Live{s}, Wr.err("tree: malformed ask")) : Ft.St & String}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def Tree.tree_ffi_unknown_ask(s, n, rest):
  %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(3n+n, rest)), LAWireSpell.ws_nat_answer(LawsBase.wire_fits(3n+n), 3n+n, rest), LAWireSpell.ws_nat_read(3n+n, rest)) : {Ft.step.ask(s, Ft.get_ask.go(_)) == (Ft.Live{s}, Wr.err("tree: malformed ask")) : Ft.St & String}
  tu.ask(s, LawsBase.wire_fits(3n+n), n, rest)
