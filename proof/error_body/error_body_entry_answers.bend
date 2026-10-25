# eukhe: the proof of LAW error_body_entry_answers
#
# PROOF: the spelled request reads back whole with nothing left
# (error_body_entry_reads), so the entry answers the code's decision, which
# is the spec's (LA.ebb.body, LA.ebs.show, LA.ebt.truncate), encoded as the spec spells it (eba.*).

import Base
import ../../bend/error_body.bend as Eb
import ../../bend/ffi_error_body.bend as FEb
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire
import ../../laws/error_body.bend as ErrorBody
import ./base.bend as LA
import ./error_body_entry_reads.bend as PErrorBodyEntryReads

def eba.mstr(m: Maybe<&2, String>, rest: String) -> {FEb.put_mstr(m, rest) == ErrorBody.sp_w_mstr(m, rest) : String}:
  match m:
    case None{}:
      {==}
    case Some{x}:
      {==}

def eba.reply(q: FEb.Req) -> {FEb.answer(q) == ErrorBody.sp_w_reply(q) : String}:
  match q:
    case FEb.QBody{+b, +e, +r}:
      %Equal.sym(Maybe<&2, String>, Eb.body(b, e, r), ErrorBody.sp_body(b, e, r), LA.ebb.body(b, e, r)) : {FEb.put_mstr(_, "") == ErrorBody.sp_w_mstr(ErrorBody.sp_body(b, e, r), "") : String}
      eba.mstr(ErrorBody.sp_body(b, e, r), "")
    case FEb.QShow{+c, +st, +b, +p, +m}:
      %Equal.sym(String, Eb.show(c, st, b, p, m), ErrorBody.sp_show(c, st, b, p, m), LA.ebs.show(c, st, b, p, m)) : {Wr.put_str(_, "") == Wr.put_str(ErrorBody.sp_show(c, st, b, p, m), "") : String}
      {==}
    case FEb.QTruncate{+t, +cap}:
      %Equal.sym(String, Eb.truncate(t, cap), ErrorBody.sp_truncate(t, cap), LA.ebt.truncate(t, cap)) : {Wr.put_str(_, "") == Wr.put_str(ErrorBody.sp_truncate(t, cap), "") : String}
      {==}

def ErrorBody.error_body_entry_answers(q, h):
  %Equal.sym(Wr.Dec<FEb.Req>, FEb.get_req(ErrorBody.sp_w_req(q, "")), Wr.Got{q, ""}, ErrorBody.error_body_entry_reads(q, "", h)) : {FEb.ffi.got(_) == ErrorBody.sp_w_reply(q) : String}
  eba.reply(q)
