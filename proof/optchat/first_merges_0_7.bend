# eukhe: the proof of LAW first_merges_0_7

import Base
import ../../bend/optchat/fit.bend as OFit
import ../../bend/optchat/info.bend as OInfo
import ../../bend/optchat/node.bend as ONode
import ../../spec/memory/optchat.bend as S
import ../../laws/optchat.bend as Optchat

def first_merges_0_7() -> {OFit.fit.view(OFit.First{}, S.ten(), 3n, 0n, OInfo.All{1n}, S.view10()) == [ONode.Node{3n, []}, ONode.Node{0n, [False{}, False{}, False{}, True{}]}, ONode.Node{0n, [True{}, False{}, False{}, True{}]}] : List<&2, ONode.Node>}:
  {==}

def Optchat.first_merges_0_7():
  first_merges_0_7()
