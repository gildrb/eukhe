# eukhe: the proof of LAW tags_entry_exact
#
# PROOF: the request decoder answers Got only for a spelled request whose
# count fits (ptg.req: wire_nat_exact, wire_nat_decoded_fits and
# wire_bool_exact, item by item); the entry answers a value only when
# nothing is left after it.

import Base
import ../../bend/doc_tags.bend as Dt
import ../../bend/ffi_doc_tags.bend as FDt
import ../../bend/wire.bend as Wr
import ../../laws/doc_tags.bend as DocTags
import ../../laws/base.bend as LawsBase
import ./base.bend as LADocTags

def pte.top(-s: String, d: Wr.Dec<List<&2, Dt.Scan>>, p: LADocTags.ptg.LS(s, d), ok: {LawsBase.wire_opens_err(FDt.ffi.got(d)) == False{} : Bool}) -> Sigma<&1, &1, List<&2, Dt.Scan>, r => {s == DocTags.sp_w_req(r, "") : String} & {DocTags.sp_fit_req(r) == True{} : Bool}>:
  match d:
    case Wr.Got{+r, rest}:
      match rest:
        case SNil{}:
          (r, p)
        case SCon{x, y}:
          LADocTags.ptg.tf(Sigma<&1, &1, List<&2, Dt.Scan>, r2 => {s == DocTags.sp_w_req(r2, "") : String} & {DocTags.sp_fit_req(r2) == True{} : Bool}>, ok)
    case Wr.Bad{}:
      LADocTags.ptg.tf(Sigma<&1, &1, List<&2, Dt.Scan>, r2 => {s == DocTags.sp_w_req(r2, "") : String} & {DocTags.sp_fit_req(r2) == True{} : Bool}>, ok)

def DocTags.tags_entry_exact(s, ok):
  pte.top(s, FDt.get_req(s), LADocTags.ptg.req(s), ok)
