# eukhe: the proof of LAW mcp_url_open_bracket
#
# PROOF: the leading `[`s are dropped one by one, so the first is dropped like the rest.

import Base
import ../../bend/mcp_url.bend as Mu
import ../../laws/mcp_url.bend as McpUrl
import ./base/text.bend as LT

def McpUrl.mcp_url_open_bracket(h):
  {==}
