# eukhe: the proof of LAW error_body_entry_refuses
#
# PROOF: every answer opens with a tag or a string length (never 'E':
# wire_nat_not_err), or is the one error form; so an answer that opens
# with 'E' is that error form.

import Base
import ../../bend/error_body.bend as Eb
import ../../bend/ffi_error_body.bend as FEb
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire
import ../../laws/error_body.bend as ErrorBody
import ../wire/wire_nat_not_err.bend as PWireNatNotErr
import ../base/staging.bend as LStg
import ../base/wire_dec.bend as LE

def ebf.str(x: String, rest: String) -> {LawsBase.wire_opens_err(Wr.put_str(x, rest)) == False{} : Bool}:
  LE.dcw.sfin_ok(Wr.put_str.go(x, "", 0n), rest)

def ebf.mstr(m: Maybe<&2, String>, rest: String) -> {LawsBase.wire_opens_err(FEb.put_mstr(m, rest)) == False{} : Bool}:
  match m:
    case None{}:
      Wire.wire_nat_not_err(0n, rest)
    case Some{x}:
      Wire.wire_nat_not_err(1n, Wr.put_str(x, rest))

def ebf.answer_ok(q: FEb.Req) -> {LawsBase.wire_opens_err(FEb.answer(q)) == False{} : Bool}:
  match q:
    case FEb.QBody{b, e, r}:
      ebf.mstr(Eb.body(b, e, r), "")
    case FEb.QShow{c, st, b, p, m}:
      ebf.str(Eb.show(c, st, b, p, m), "")
    case FEb.QTruncate{t, cap}:
      ebf.str(Eb.truncate(t, cap), "")

def ebf.refuse(d: Wr.Dec<FEb.Req>, bad: {LawsBase.wire_opens_err(FEb.ffi.got(d)) == True{} : Bool}) -> {FEb.ffi.got(d) == Wr.err("error_body: malformed request") : String}:
  match d:
    case Wr.Got{+q, rest}:
      match rest:
        case SNil{}:
          LStg.stg.absurd({FEb.answer(q) == Wr.err("error_body: malformed request") : String}, Equal.trans(Bool, True{}, LawsBase.wire_opens_err(FEb.answer(q)), False{}, Equal.sym(Bool, LawsBase.wire_opens_err(FEb.answer(q)), True{}, bad), ebf.answer_ok(q)))
        case SCon{x, y}:
          {==}
    case Wr.Bad{}:
      {==}

def ErrorBody.error_body_entry_refuses(s, bad):
  ebf.refuse(FEb.get_req(s), bad)
