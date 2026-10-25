# eukhe: the proof of LAW codemode_models_ffi_exact

import Base
import ../../bend/codemode_models.bend as Mod
import ../../bend/ffi_codemode_models.bend as FMod
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/codemode_models/entry.bend as CodemodeModelsEntry
import ../context_order/base.bend as LACo
import ./base/exact_req.bend as LACmExactReq

# PROOF of LAW codemode_models_ffi_exact: the request decoder answers Got only for a spelled request whose numbers fit (cme.req); the entry answers a value only when nothing is left after it.

def cmx.top(-s: String, d: Wr.Dec<FMod.Req>, p: LACmExactReq.cme.RQ(s, d), ok: {LawsBase.wire_opens_err(FMod.ffi.got(d)) == False{} : Bool}) -> Sigma<&1, &1, FMod.Req, q2 => {s == CodemodeModelsEntry.spell_req(q2, "") : String} & {CodemodeModelsEntry.req_fits(q2) == True{} : Bool}>:
  match d:
    case Wr.Got{+q, rest}:
      match rest:
        case SNil{}:
          (q, p)
        case SCon{x, y}:
          LACo.co.tf(Sigma<&1, &1, FMod.Req, q2 => {s == CodemodeModelsEntry.spell_req(q2, "") : String} & {CodemodeModelsEntry.req_fits(q2) == True{} : Bool}>, ok)
    case Wr.Bad{}:
      LACo.co.tf(Sigma<&1, &1, FMod.Req, q2 => {s == CodemodeModelsEntry.spell_req(q2, "") : String} & {CodemodeModelsEntry.req_fits(q2) == True{} : Bool}>, ok)

def CodemodeModelsEntry.codemode_models_ffi_exact(s, ok):
  cmx.top(s, FMod.get_req(s), LACmExactReq.cme.req(s), ok)
