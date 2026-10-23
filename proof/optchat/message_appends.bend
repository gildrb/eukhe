# eukhe: the proof of LAW message_appends

import Base
import ../../bend/optchat/bits.bend as OBits
import ../../bend/optchat/node.bend as ONode
import ../../bend/optchat/state.bend as OState
import ../../bend/optchat/step.bend as OStep
import ../../laws/optchat.bend as Optchat

def message_appends(+cfg: OState.Cfg, +s: OState.St, quiet: {OStep.St.batch(cfg, s) == False{} : Bool}) -> {OState.St.view(Pair.fst(OState.St, List<&2, ONode.Node>, OStep.msg(cfg, s))) == List.append(&2, ONode.Node, OState.St.view(s), [ONode.Node.leaf(OState.St.t(s))]) : List<&2, ONode.Node>}:
  %Equal.sym(Bool, OStep.St.batch(cfg, s), False{}, quiet) : {OState.St.view(Pair.fst(OState.St, List<&2, ONode.Node>, OStep.msg.go(_, cfg, OBits.Bits.inc(OState.St.t(s)), OState.St.info(s), OStep.St.grown(s), List.append(&2, ONode.Node, OState.St.cview(s), [ONode.Node.leaf(OState.St.t(s))]), OState.St.ready(s), OState.St.busy(s)))) == List.append(&2, ONode.Node, OState.St.view(s), [ONode.Node.leaf(OState.St.t(s))]) : List<&2, ONode.Node>}
  {==}

# (b) A message

def Optchat.message_appends(cfg, s, quiet):
  message_appends(cfg, s, quiet)
