# eukhe: the proof of LAW mcp_url_entry_exact
#
# PROOF: the host decoder answers Got{h, rest} only for the spelling of h before rest, h within the wire (dcw.str); the entry answers a value only when nothing is left: the input is the spelled host.

import Base
import ../../bend/mcp_url.bend as Mu
import ../../bend/ffi_mcp_url.bend as FMu
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire
import ../../laws/mcp_url.bend as McpUrl
import ../base/wire_dec.bend as LE
import ../base/staging.bend as LStg

def mux.top(-s: String, d: Wr.Dec<String>, sp: LE.dcw.SP(s, d), ok: {LawsBase.wire_opens_err(FMu.ffi.got(d)) == False{} : Bool}) -> Sigma<&1, &1, String, h => {s == McpUrl.mu_w_req(h, "") : String} & {LawsBase.wire_fits(String.length(h)) == True{} : Bool}>:
  match d:
    case Wr.Got{+h, rest}:
      match rest:
        case SNil{}:
          (h, sp)
        case SCon{x, y}:
          LStg.stg.absurd(Sigma<&1, &1, String, h2 => {s == McpUrl.mu_w_req(h2, "") : String} & {LawsBase.wire_fits(String.length(h2)) == True{} : Bool}>, ok)
    case Wr.Bad{}:
      LStg.stg.absurd(Sigma<&1, &1, String, h2 => {s == McpUrl.mu_w_req(h2, "") : String} & {LawsBase.wire_fits(String.length(h2)) == True{} : Bool}>, ok)

def McpUrl.mcp_url_entry_exact(s, ok):
  mux.top(s, Wr.get_str(s), LE.dcw.str(s), ok)
