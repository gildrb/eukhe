# eukhe: the proof of LAW codemode_describe_ffi_refuses

import Base
import ../../bend/codemode_describe.bend as Dsc
import ../../bend/ffi_codemode_describe.bend as FDsc
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/codemode_describe.bend as CodemodeDescribe
import ../context_order/base.bend as LACo
import ./base/reply.bend as LACdReply

# PROOF of LAW codemode_describe_ffi_refuses: the entry answers either the error form or an answer, and an answer opens with a Nat, never 'E' (cdy.not_err).

def cdf.done(q: FDsc.Req, b: Bool, bad: {LawsBase.wire_opens_err(FDsc.ffi.done(q, b)) == True{} : Bool}) -> {FDsc.ffi.done(q, b) == Wr.err("codemode_describe: malformed request") : String}:
  match b:
    case True{}:
      LACo.co.tf({FDsc.answer(q) == Wr.err("codemode_describe: malformed request") : String}, Equal.trans(Bool, True{}, LawsBase.wire_opens_err(FDsc.answer(q)), False{}, Equal.sym(Bool, LawsBase.wire_opens_err(FDsc.answer(q)), True{}, bad), LACdReply.cdy.not_err(q)))
    case False{}:
      {==}

def cdf.got(d: Wr.Dec<FDsc.Req>, bad: {LawsBase.wire_opens_err(FDsc.ffi.got(d)) == True{} : Bool}) -> {FDsc.ffi.got(d) == Wr.err("codemode_describe: malformed request") : String}:
  match d:
    case Wr.Got{+q, +r}:
      cdf.done(q, Wr.end(r), bad)
    case Wr.Bad{}:
      {==}

def CodemodeDescribe.codemode_describe_ffi_refuses(s, bad):
  cdf.got(FDsc.get_req(s), bad)
