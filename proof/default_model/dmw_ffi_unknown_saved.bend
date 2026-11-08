# eukhe: the proof of LAW dmw_ffi_unknown_saved
#
# PROOF: the tag reads as itself or Bad (ws_nat_read); a tag of 2 or more
# is no saved default: Bad, the malformed error form.

import Base
import ../../bend/ffi_default_model.bend as FDm
import ../../bend/wire.bend as Wr
import ../../laws/default_model.bend as DefaultModel
import ../../laws/base.bend as LawsBase
import ../wire/base/spell.bend as LAWireSpell

def dus.bad(b: Bool, +n: Nat, rest: String) -> {FDm.ffi.go(FDm.get_in.go(FDm.get_saved.go(LAWireSpell.ws_nat_answer(b, 2n+n, rest)))) == Wr.err("default_model: malformed request") : String}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def DefaultModel.dmw_ffi_unknown_saved(n, rest):
  %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(2n+n, rest)), LAWireSpell.ws_nat_answer(LawsBase.wire_fits(2n+n), 2n+n, rest), LAWireSpell.ws_nat_read(2n+n, rest)) : {FDm.ffi.go(FDm.get_in.go(FDm.get_saved.go(_))) == Wr.err("default_model: malformed request") : String}
  dus.bad(LawsBase.wire_fits(2n+n), n, rest)
