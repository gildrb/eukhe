# eukhe: the proof of LAW command_ffi_unknown_res
#
# PROOF of LAW command_ffi_unknown_res: the tag 4n + n reads as itself when
# it fits and as Bad when too long (ws_nat_read); both ways the resolve reply
# decoder answers Bad.

import Base
import ../../bend/ffi_command.bend as FCmd
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/command/entry.bend as Command
import ../wire/base/spell.bend as LAWireSpell

def cus_bad(b: Bool, -n: Nat, -rest: String) -> {FCmd.get_res.go(LAWireSpell.ws_nat_answer(b, 4n+n, rest)) == Wr.Bad{} : Wr.Dec<FCmd.ResW>}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def Command.command_ffi_unknown_res(n, rest):
  %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(4n+n, rest)), LAWireSpell.ws_nat_answer(LawsBase.wire_fits(4n+n), 4n+n, rest), LAWireSpell.ws_nat_read(4n+n, rest)) : {FCmd.get_res.go(_) == Wr.Bad{} : Wr.Dec<FCmd.ResW>}
  cus_bad(LawsBase.wire_fits(4n+n), n, rest)
