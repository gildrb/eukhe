# eukhe: the proof of LAW optchat_info_set_get
#
# PROOF: the levels read after a set are the levels read before, but at
# the set level (oq.lv), whose trie read after a set is the trie read
# before, but at the set bits (oq.tr).

import Base
import ../../bend/optchat/node.bend as ONode
import ../../bend/optchat/info.bend as OInfo
import ../../spec/memory/optchat.bend as S
import ../../laws/optchat/queries.bend as OptchatQueries
import ./base/queries.bend as LQ

def OptchatQueries.optchat_info_set_get(ts, n, z, m):
  match n m:
    case ONode.Node{l, +i} ONode.Node{k, +j}:
      LQ.oq.lv(l, ts, k, i, j, z)
