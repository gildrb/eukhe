# eukhe: the proof of LAW shell_ffi_refuses
#
# PROOF: every reply opens with a list of Nats, never 'E' (shr.reply_ok);
# so an answer that opens with 'E' is the one error form.

import Base
import ../../bend/ffi_shell.bend as FSh
import ../../bend/wire.bend as Wr
import ../../laws/shell.bend as Shell
import ../../bend/tools.bend as Tl
import ../../laws/base.bend as LawsBase
import ../base/wire_dec.bend as LD
import ../base/staging.bend as LStg

def shr.reply_ok(q: FSh.Req) -> {LawsBase.wire_opens_err(FSh.answer(q)) == False{} : Bool}:
  match q:
    case FSh.QVerdict{+ps}:
      LD.dcw.fin_ok(Wr.put_list.go(~Nat, ~Wr.put_nat, Tl.pieces.effs(ps), FSh.put_verdict(Tl.verdict(ps), "")))

def shr.refuse(d: Wr.Dec<FSh.Req>, bad: {LawsBase.wire_opens_err(FSh.run(d)) == True{} : Bool}) -> {FSh.run(d) == Shell.malformed() : String}:
  match d:
    case Wr.Got{+q, rest}:
      match rest:
        case SNil{}:
          LStg.stg.absurd({FSh.answer(q) == Shell.malformed() : String}, Equal.trans(Bool, True{}, LawsBase.wire_opens_err(FSh.answer(q)), False{}, Equal.sym(Bool, LawsBase.wire_opens_err(FSh.answer(q)), True{}, bad), shr.reply_ok(q)))
        case SCon{x, y}:
          {==}
    case Wr.Bad{}:
      {==}

def Shell.shell_ffi_refuses(s, bad):
  shr.refuse(FSh.get_req(s), bad)
