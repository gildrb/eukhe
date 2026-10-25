# eukhe: the proof of LAW mcp_url_entry_refuses
#
# PROOF: the entry answers either a Bool (never 'E': wire_bool_not_err) or the one error form; so an answer that opens with 'E' is that error form.

import Base
import ../../bend/mcp_url.bend as Mu
import ../../bend/ffi_mcp_url.bend as FMu
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire
import ../../laws/mcp_url.bend as McpUrl
import ../wire/wire_bool_not_err.bend as PWireBoolNotErr
import ../base/staging.bend as LStg

def muf.refuse(d: Wr.Dec<String>, bad: {LawsBase.wire_opens_err(FMu.ffi.got(d)) == True{} : Bool}) -> {FMu.ffi.got(d) == Wr.err("mcp_url: malformed request") : String}:
  match d:
    case Wr.Got{+h, rest}:
      match rest:
        case SNil{}:
          LStg.stg.absurd({Wr.put_bool(Mu.refused(h), "") == Wr.err("mcp_url: malformed request") : String}, Equal.trans(Bool, True{}, LawsBase.wire_opens_err(Wr.put_bool(Mu.refused(h), "")), False{}, Equal.sym(Bool, LawsBase.wire_opens_err(Wr.put_bool(Mu.refused(h), "")), True{}, bad), Wire.wire_bool_not_err(Mu.refused(h), "")))
        case SCon{x, y}:
          {==}
    case Wr.Bad{}:
      {==}

def McpUrl.mcp_url_entry_refuses(s, bad):
  muf.refuse(Wr.get_str(s), bad)
