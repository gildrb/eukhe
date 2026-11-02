# eukhe: the proof of LAW optchat_info_empty
#
# PROOF: the empty chat holds no level, and no level reads a size
# (oq.lg_nil).

import Base
import ../../bend/optchat/node.bend as ONode
import ../../bend/optchat/info.bend as OInfo
import ../../laws/optchat/queries.bend as OptchatQueries
import ./base/queries.bend as LQ

def OptchatQueries.optchat_info_empty(m):
  match m:
    case ONode.Node{k, j}:
      LQ.oq.lg_nil(k, j)
