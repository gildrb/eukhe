# eukhe: the proof of LAW message_appends

import Base
import ../../bend/optchat.bend as O
import ../../laws/optchat.bend as Optchat

def message_appends(+cfg: O.Cfg, +s: O.St, quiet: {O.St.batch(cfg, s) == False{} : Bool}) -> {O.St.view(Pair.fst(O.St, List<&2, O.Node>, O.msg(cfg, s))) == List.append(&2, O.Node, O.St.view(s), [O.Node.leaf(O.St.t(s))]) : List<&2, O.Node>}:
  %Equal.sym(Bool, O.St.batch(cfg, s), False{}, quiet) : {O.St.view(Pair.fst(O.St, List<&2, O.Node>, O.msg.go(_, cfg, O.Bits.inc(O.St.t(s)), O.St.info(s), O.St.grown(s), List.append(&2, O.Node, O.St.cview(s), [O.Node.leaf(O.St.t(s))]), O.St.ready(s), O.St.busy(s)))) == List.append(&2, O.Node, O.St.view(s), [O.Node.leaf(O.St.t(s))]) : List<&2, O.Node>}
  {==}

# (b) A message

def Optchat.message_appends(cfg, s, quiet):
  message_appends(cfg, s, quiet)
