# eukhe: the proof of LAW slash_args_entry_refuses
#
# PROOF: every answer opens with a Nat, never 'E' (sae.answer_ok); so an answer that opens with 'E' is the one error form.

import Base
import ../../bend/slash_args.bend as Sa
import ../../bend/ffi_slash_args.bend as FSa
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire
import ../../laws/slash_args/model.bend as SlashArgs
import ../../laws/slash_args/entry.bend as SlashArgsEntry
import ./base/entry.bend as LE
import ../base/staging.bend as LStg

def sar.refuse(d: Wr.Dec<FSa.Req>, bad: {LawsBase.wire_opens_err(FSa.ffi.got(d)) == True{} : Bool}) -> {FSa.ffi.got(d) == Wr.err("slash_args: malformed request") : String}:
  match d:
    case Wr.Got{+q, rest}:
      match rest:
        case SNil{}:
          LStg.stg.absurd({FSa.answer(q) == Wr.err("slash_args: malformed request") : String}, Equal.trans(Bool, True{}, LawsBase.wire_opens_err(FSa.answer(q)), False{}, Equal.sym(Bool, LawsBase.wire_opens_err(FSa.answer(q)), True{}, bad), LE.sae.answer_ok(q)))
        case SCon{x, y}:
          {==}
    case Wr.Bad{}:
      {==}

def SlashArgsEntry.slash_args_entry_refuses(s, bad):
  sar.refuse(FSa.get_req(s), bad)
