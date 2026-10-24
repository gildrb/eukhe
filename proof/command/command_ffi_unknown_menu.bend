# eukhe: the proof of LAW command_ffi_unknown_menu
#
# PROOF of LAW command_ffi_unknown_menu: the tag 3n + n reads as itself when
# it fits and as Bad when too long (ws_nat_read); both ways the menu reply
# decoder answers Bad.

import Base
import ../../bend/ffi_command.bend as FCmd
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/command/entry.bend as Command
import ../wire/base/spell.bend as LAWireSpell

def cum_bad(b: Bool, -n: Nat, -rest: String) -> {FCmd.get_menu.go(LAWireSpell.ws_nat_answer(b, 3n+n, rest)) == Wr.Bad{} : Wr.Dec<FCmd.MenuW>}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def Command.command_ffi_unknown_menu(n, rest):
  %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(3n+n, rest)), LAWireSpell.ws_nat_answer(LawsBase.wire_fits(3n+n), 3n+n, rest), LAWireSpell.ws_nat_read(3n+n, rest)) : {FCmd.get_menu.go(_) == Wr.Bad{} : Wr.Dec<FCmd.MenuW>}
  cum_bad(LawsBase.wire_fits(3n+n), n, rest)
