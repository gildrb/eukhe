# eukhe: the proof of LAW shell_ffi_refuses
#
# PROOF: every reply opens with a Nat or a Bool, never 'E' (shr.reply_ok);
# so an answer that opens with 'E' is the one error form.

import Base
import ../../bend/ffi_shell.bend as FSh
import ../../bend/wire.bend as Wr
import ../../laws/shell.bend as Shell
import ../../bend/tools.bend as Tl
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire
import ../base/wire_dec.bend as LD
import ../base/staging.bend as LStg
import ../wire/wire_nat_not_err.bend as PWireNatNotErr
import ../wire/wire_bool_not_err.bend as PWireBoolNotErr

def shr.step_ok(+a: List<&2, Nat>, +es: List<&2, Nat>) -> {LawsBase.wire_opens_err(FSh.answer.step(a, es)) == False{} : Bool}:
  LD.dcw.fin_ok(Wr.put_list.go(~Nat, ~Wr.put_nat, es, Wr.put_bool(Tl.within(es, a), "")))

def shr.reply_ok(q: FSh.Req) -> {LawsBase.wire_opens_err(FSh.answer(q)) == False{} : Bool}:
  match q:
    case FSh.QStep{+a, ps}:
      shr.step_ok(a, Tl.join(Tl.parts.effs(ps)))
    case FSh.QAllows{+a, es}:
      Wire.wire_bool_not_err(Tl.within(es, a), "")
    case FSh.QAnswer{i, y}:
      match y:
        case True{}:
          Wire.wire_nat_not_err(0n, "")
        case False{}:
          Wire.wire_nat_not_err(1n, Wr.put_nat(i, ""))

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
