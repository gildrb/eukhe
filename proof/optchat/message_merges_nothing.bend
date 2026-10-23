# eukhe: the proof of LAW message_merges_nothing

import Base
import ../../bend/optchat/bits.bend as OBits
import ../../bend/optchat/node.bend as ONode
import ../../bend/optchat/state.bend as OState
import ../../bend/optchat/step.bend as OStep
import ../../laws/optchat.bend as Optchat

def message_merges_nothing(+cfg: OState.Cfg, +s: OState.St, quiet: {OStep.St.batch(cfg, s) == False{} : Bool}) -> {Pair.snd(OState.St, List<&2, ONode.Node>, OStep.msg(cfg, s)) == Nil{} : List<&2, ONode.Node>}:
  %Equal.sym(Bool, OStep.St.batch(cfg, s), False{}, quiet) : {Pair.snd(OState.St, List<&2, ONode.Node>, OStep.msg.go(_, cfg, OBits.Bits.inc(OState.St.t(s)), OState.St.info(s), OStep.St.grown(s), List.append(&2, ONode.Node, OState.St.cview(s), [ONode.Node.leaf(OState.St.t(s))]), OState.St.ready(s), OState.St.busy(s))) == Nil{} : List<&2, ONode.Node>}
  {==}

def Optchat.message_merges_nothing(cfg, s, quiet):
  message_merges_nothing(cfg, s, quiet)
