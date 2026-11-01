# eukhe: the proof of LAW stop_entry_unknown
#
# PROOF: the tag 3 + n reads as itself when it fits and as Bad when too long (ws_nat_read); both ways the request is Bad.

import Base
import ../../bend/ffi_stop.bend as FS
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../wire/base/spell.bend as LAWireSpell
import ../../laws/stop.bend as Stop

def stu.bad(b: Bool, -n: Nat, -rest: String) -> {FS.get_ask.tag(LAWireSpell.ws_nat_answer(b, 3n+n, rest)) == Wr.Bad{} : Wr.Dec<FS.Ask>}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def Stop.stop_entry_unknown(n, rest):
  +x = Wr.put_nat(3n+n, rest)
  %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(x), LAWireSpell.ws_nat_answer(LawsBase.wire_fits(3n+n), 3n+n, rest), LAWireSpell.ws_nat_read(3n+n, rest)) : {FS.ffi.got(FS.get_ask.tag(_)) == Wr.err("stop: malformed request") : String}
  %Equal.sym(Wr.Dec<FS.Ask>, FS.get_ask.tag(LAWireSpell.ws_nat_answer(LawsBase.wire_fits(3n+n), 3n+n, rest)), Wr.Bad{}, stu.bad(LawsBase.wire_fits(3n+n), n, rest)) : {FS.ffi.got(_) == Wr.err("stop: malformed request") : String}
  {==}
