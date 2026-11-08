# eukhe: the proof of LAW run_ffi_unknown_ask
#
# PROOF: the tag reads back as itself when it fits the wire, else Bad
# (ws_nat_read); a tag of 7 or more is past every request, so both are
# malformed.

import Base
import ../../bend/ffi_run.bend as FRn
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/run/entry.bend as Run
import ../wire/base/spell.bend as LAWireSpell

def ua.at(b: Bool, +n: Nat, +rest: String) -> {FRn.ffi.go(FRn.get_ask.tag(LAWireSpell.ws_nat_answer(b, 7n+n, rest))) == Wr.err("run: malformed request") : String}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def Run.run_ffi_unknown_ask(n, rest):
  %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(7n+n, rest)), LAWireSpell.ws_nat_answer(LawsBase.wire_fits(7n+n), 7n+n, rest), LAWireSpell.ws_nat_read(7n+n, rest)) : {FRn.ffi.go(FRn.get_ask.tag(_)) == Wr.err("run: malformed request") : String}
  ua.at(LawsBase.wire_fits(7n+n), n, rest)
