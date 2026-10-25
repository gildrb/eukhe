# eukhe: the proof of LAW codemode_source_ffi_refuses

import Base
import ../../bend/codemode_source.bend as Src
import ../../bend/ffi_codemode_source.bend as FSrc
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire
import ../../laws/codemode_source.bend as CodemodeSource
import ../context_order/base.bend as LACo
import ./base/reply.bend as LACsReply

# PROOF of LAW codemode_source_ffi_refuses: the entry answers either the error form or an answer, and an answer opens with a Nat, never 'E' (csy.not_err).

def csf.done(f: Src.Facts, b: Bool, bad: {LawsBase.wire_opens_err(FSrc.ffi.done(f, b)) == True{} : Bool}) -> {FSrc.ffi.done(f, b) == Wr.err("codemode_source: malformed request") : String}:
  match b:
    case True{}:
      LACo.co.tf({FSrc.put_answer(Src.parse(f)) == Wr.err("codemode_source: malformed request") : String}, Equal.trans(Bool, True{}, LawsBase.wire_opens_err(FSrc.put_answer(Src.parse(f))), False{}, Equal.sym(Bool, LawsBase.wire_opens_err(FSrc.put_answer(Src.parse(f))), True{}, bad), LACsReply.csy.not_err(Src.parse(f))))
    case False{}:
      {==}

def csf.got(d: Wr.Dec<Src.Facts>, bad: {LawsBase.wire_opens_err(FSrc.ffi.got(d)) == True{} : Bool}) -> {FSrc.ffi.got(d) == Wr.err("codemode_source: malformed request") : String}:
  match d:
    case Wr.Got{+f, +r}:
      csf.done(f, Wr.end(r), bad)
    case Wr.Bad{}:
      {==}

def CodemodeSource.codemode_source_ffi_refuses(s, bad):
  csf.got(FSrc.get_req(s), bad)
