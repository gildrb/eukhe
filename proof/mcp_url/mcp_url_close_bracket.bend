# eukhe: the proof of LAW mcp_url_close_bracket
#
# PROOF: `]` is no `[` (LT.mt.do_app), so the host reads as before with one more trailing `]`, which is dropped (LT.mt.dc_snoc).

import Base
import ../../bend/mcp_url.bend as Mu
import ../../laws/mcp_url.bend as McpUrl
import ./base/text.bend as LT

def McpUrl.mcp_url_close_bracket(h):
  +H = String.append(h, SCon{']', SNil{}})
  %Equal.sym(String, Mu.drop_open(H), String.append(Mu.drop_open(h), SCon{']', SNil{}}), LT.mt.do_app(h, ']', SNil{}, {==})) : {Mu.refused.at(Bool.or(String.eq(String.to_lower(Mu.drop_close(_)), "localhost"), String.ends_with(String.to_lower(Mu.drop_close(_)), ".localhost")), String.to_lower(Mu.drop_close(_))) == Mu.refused(h) : Bool}
  %Equal.sym(String, Mu.drop_close(String.append(Mu.drop_open(h), SCon{']', SNil{}})), Mu.drop_close(Mu.drop_open(h)), LT.mt.dc_snoc(Mu.drop_open(h))) : {Mu.refused.at(Bool.or(String.eq(String.to_lower(_), "localhost"), String.ends_with(String.to_lower(_), ".localhost")), String.to_lower(_)) == Mu.refused(h) : Bool}
  {==}
