# eukhe: the proof of LAW slash_args_entry_unknown_tag
#
# PROOF: the tag 4 + n reads as itself when it fits and as Bad when too long (ws_nat_read); both ways no request is read.

import Base
import ../../bend/slash_args.bend as Sa
import ../../bend/ffi_slash_args.bend as FSa
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire
import ../../laws/slash_args/model.bend as SlashArgs
import ../../laws/slash_args/entry.bend as SlashArgsEntry
import ../wire/base/spell.bend as LAWireSpell

def sau.bad(b: Bool, -n: Nat, -rest: String) -> {FSa.ffi.got(FSa.get_req.start(LAWireSpell.ws_nat_answer(b, 4n+n, rest))) == Wr.err("slash_args: malformed request") : String}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def SlashArgsEntry.slash_args_entry_unknown_tag(n, rest):
  %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(4n+n, rest)), LAWireSpell.ws_nat_answer(LawsBase.wire_fits(4n+n), 4n+n, rest), LAWireSpell.ws_nat_read(4n+n, rest)) : {FSa.ffi.got(FSa.get_req.start(_)) == Wr.err("slash_args: malformed request") : String}
  sau.bad(LawsBase.wire_fits(4n+n), n, rest)
