# eukhe: the proof of LAW codemode_models_ffi_refuses

import Base
import ../../bend/codemode_models.bend as Mod
import ../../bend/ffi_codemode_models.bend as FMod
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/codemode_models/entry.bend as CodemodeModelsEntry
import ../context_order/base.bend as LACo
import ./base/reply.bend as LACmReply

# PROOF of LAW codemode_models_ffi_refuses: the entry answers either the error form or an answer, and an answer never opens with 'E' (cmy.not_err).

def cmf.done(q: FMod.Req, b: Bool, bad: {LawsBase.wire_opens_err(FMod.ffi.done(q, b)) == True{} : Bool}) -> {FMod.ffi.done(q, b) == Wr.err("codemode_models: malformed request") : String}:
  match b:
    case True{}:
      LACo.co.tf({FMod.answer(q) == Wr.err("codemode_models: malformed request") : String}, Equal.trans(Bool, True{}, LawsBase.wire_opens_err(FMod.answer(q)), False{}, Equal.sym(Bool, LawsBase.wire_opens_err(FMod.answer(q)), True{}, bad), LACmReply.cmy.not_err(q)))
    case False{}:
      {==}

def cmf.got(d: Wr.Dec<FMod.Req>, bad: {LawsBase.wire_opens_err(FMod.ffi.got(d)) == True{} : Bool}) -> {FMod.ffi.got(d) == Wr.err("codemode_models: malformed request") : String}:
  match d:
    case Wr.Got{+q, +r}:
      cmf.done(q, Wr.end(r), bad)
    case Wr.Bad{}:
      {==}

def CodemodeModelsEntry.codemode_models_ffi_refuses(s, bad):
  cmf.got(FMod.get_req(s), bad)
