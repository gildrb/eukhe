# eukhe: the proof of LAW mcp_url_localhost
#
# PROOF: `.` is no `[` or `]`, so the host reads as x read then `.localhost` (LT.mt.do_app, LT.mt.dca, LT.mt.tl_app), which ends with `.localhost` whatever x is (LT.mt.rev_app).

import Base
import ../../bend/mcp_url.bend as Mu
import ../../laws/mcp_url.bend as McpUrl
import ./base/text.bend as LT

def ml.at(g: Bool, +s: String) -> {Mu.refused.at(Bool.or(g, True{}), s) == True{} : Bool}:
  match g:
    case True{}:
      {==}
    case False{}:
      {==}

def McpUrl.mcp_url_localhost(x):
  +L = {".localhost" : String}
  +D = Mu.drop_open(x)
  +Z = String.to_lower(D)
  +S = String.append(Z, L)
  +EB = Equal.trans(String, Mu.bare(String.append(x, L)), String.to_lower(Mu.drop_close(String.append(D, L))), S, Equal.cong(String, String, z => String.to_lower(Mu.drop_close(z)), Mu.drop_open(String.append(x, L)), String.append(D, L), LT.mt.do_app(x, '.', "localhost", {==})), Equal.trans(String, String.to_lower(Mu.drop_close(String.append(D, L))), String.to_lower(String.append(D, L)), S, Equal.cong(String, String, z => String.to_lower(z), Mu.drop_close(String.append(D, L)), String.append(D, L), LT.mt.dca(D, L, {==})), LT.mt.tl_app(D, L)))
  %Equal.sym(String, Mu.bare(String.append(x, L)), S, EB) : {Mu.refused.at(Bool.or(String.eq(_, "localhost"), String.ends_with(_, ".localhost")), _) == True{} : Bool}
  %Equal.sym(String, String.reverse.go(S, SNil{}), String.reverse.go(L, String.reverse.go(Z, SNil{})), LT.mt.rev_app(Z, L, SNil{})) : {Mu.refused.at(Bool.or(String.eq(S, "localhost"), String.starts_with(_, String.reverse(".localhost"))), S) == True{} : Bool}
  ml.at(String.eq(S, "localhost"), S)
