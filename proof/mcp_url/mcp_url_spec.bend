# eukhe: the proof of LAW mcp_url_spec
#
# PROOF: the bare host is the spec's (mub.bare), so is the localhost test (the same Base calls), and the rest of the check is the spec's stage by stage (mub.refused.at).

import Base
import ../../bend/mcp_url.bend as Mu
import ../../bend/ffi_mcp_url.bend as FMu
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire
import ../../laws/mcp_url.bend as McpUrl
import ./base.bend as LA

def McpUrl.mcp_url_spec(h):
  %Equal.sym(String, Mu.bare(h), McpUrl.mu_bare(h), LA.mub.bare(h)) : {Mu.refused.at(Bool.or(String.eq(_, "localhost"), String.ends_with(_, ".localhost")), _) == McpUrl.mu_refused(h) : Bool}
  LA.mub.refused.at(Bool.or(String.eq(McpUrl.mu_bare(h), "localhost"), String.ends_with(McpUrl.mu_bare(h), ".localhost")), McpUrl.mu_bare(h))
