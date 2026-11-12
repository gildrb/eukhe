# eukhe: the proof of LAW last_merges_8_9

import Base
import ../../bend/optchat/fit.bend as OFit
import ../../bend/optchat/info.bend as OInfo
import ../../bend/optchat/node.bend as ONode
import ../../spec/memory/optchat.bend as S
import ../../laws/optchat.bend as Optchat

# First is not last
# -----------------

def last_merges_8_9() -> {OFit.fit.view(OFit.Last{}, S.ten(), 3n, 0n, OInfo.All{1n}, S.view10()) == [ONode.Node{2n, []}, ONode.Node{2n, [True{}]}, ONode.Node{1n, [False{}, False{}, True{}]}] : List<&2, ONode.Node>}:
  {==}

def Optchat.last_merges_8_9():
  last_merges_8_9()
