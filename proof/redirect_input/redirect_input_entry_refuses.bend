# eukhe: the proof of LAW redirect_input_entry_refuses
#
# PROOF: every answer opens with a Nat, never 'E' (rie.reply_ok); so an answer that opens with 'E' is the one error form.

import Base
import ../../bend/redirect_input.bend as Ri
import ../../bend/ffi_redirect_input.bend as FRi
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire
import ../../laws/redirect_input.bend as RedirectInput
import ./base/entry.bend as LE
import ../base/staging.bend as LStg

def rif.refuse(d: Wr.Dec<FRi.Req>, bad: {LawsBase.wire_opens_err(FRi.ffi.got(d)) == True{} : Bool}) -> {FRi.ffi.got(d) == Wr.err("redirect_input: malformed request") : String}:
  match d:
    case Wr.Got{+q, rest}:
      match rest:
        case SNil{}:
          LStg.stg.absurd({FRi.answer(q) == Wr.err("redirect_input: malformed request") : String}, Equal.trans(Bool, True{}, LawsBase.wire_opens_err(FRi.answer(q)), False{}, Equal.sym(Bool, LawsBase.wire_opens_err(FRi.answer(q)), True{}, bad), LE.rie.reply_ok(q)))
        case SCon{x, y}:
          {==}
    case Wr.Bad{}:
      {==}

def RedirectInput.redirect_input_entry_refuses(s, bad):
  rif.refuse(FRi.get_req(s), bad)
