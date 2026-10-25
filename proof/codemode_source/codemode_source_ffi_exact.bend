# eukhe: the proof of LAW codemode_source_ffi_exact

import Base
import ../../bend/codemode_source.bend as Src
import ../../bend/ffi_codemode_source.bend as FSrc
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire
import ../../laws/codemode_source.bend as CodemodeSource
import ../context_order/base.bend as LACo
import ./base/exact.bend as LACsExact

# PROOF of LAW codemode_source_ffi_exact: the request decoder answers Got only for a spelled request whose numbers fit (cse.req); the entry answers a value only when nothing is left after it.

def csx.top(-s: String, d: Wr.Dec<Src.Facts>, p: LACsExact.cse.RQ(s, d), ok: {LawsBase.wire_opens_err(FSrc.ffi.got(d)) == False{} : Bool}) -> Sigma<&1, &1, Src.Facts, f2 => {s == CodemodeSource.spell_req(f2, "") : String} & {CodemodeSource.req_fits(f2) == True{} : Bool}>:
  match d:
    case Wr.Got{+f, rest}:
      match rest:
        case SNil{}:
          (f, p)
        case SCon{x, y}:
          LACo.co.tf(Sigma<&1, &1, Src.Facts, f2 => {s == CodemodeSource.spell_req(f2, "") : String} & {CodemodeSource.req_fits(f2) == True{} : Bool}>, ok)
    case Wr.Bad{}:
      LACo.co.tf(Sigma<&1, &1, Src.Facts, f2 => {s == CodemodeSource.spell_req(f2, "") : String} & {CodemodeSource.req_fits(f2) == True{} : Bool}>, ok)

def CodemodeSource.codemode_source_ffi_exact(s, ok):
  csx.top(s, FSrc.get_req(s), LACsExact.cse.req(s), ok)
