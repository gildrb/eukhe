# eukhe: the proof of LAW mcp_url_v6_unique_local
#
# PROOF: each first word of fc00::/7, one arm per word (computed: LFC.mu6.fc, LFD.mu6.fd), is refused by the model whatever the other seven words are, so the host is refused whatever follows its first `:` (LV.m6.go).

import Base
import ../../bend/mcp_url.bend as Mu
import ../../laws/mcp_url.bend as McpUrl
import ./base/text.bend as LT
import ./base/v6.bend as LV
import ./mcp_url_v6_unique_local/fc.bend as LFC
import ./mcp_url_v6_unique_local/fd.bend as LFD

def McpUrl.mcp_url_v6_unique_local(i, j, rest, blk):
  match i:
    case 0n:
      LFC.mu6.fc(j, rest, blk)
    case 1n:
      LFD.mu6.fd(j, rest, blk)
    case 2n+p:
      LT.mt.lt_zero({Mu.refused(String.append(McpUrl.mu_hex2(Nat.add(252n, 2n+p)), String.append(McpUrl.mu_hex2(j), SCon{':', rest}))) == True{} : Bool}, p, LT.mt.and_l(Nat.is_lt(2n+p, 2n), Nat.is_le(j, 255n), blk))
