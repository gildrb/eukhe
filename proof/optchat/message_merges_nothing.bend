# eukhe: the proof of LAW message_merges_nothing

import Base
import ../../bend/optchat.bend as O
import ../../laws/optchat.bend as Optchat

def message_merges_nothing(+cfg: O.Cfg, +s: O.St, quiet: {O.St.batch(cfg, s) == False{} : Bool}) -> {Pair.snd(O.St, List<&2, O.Node>, O.msg(cfg, s)) == Nil{} : List<&2, O.Node>}:
  %Equal.sym(Bool, O.St.batch(cfg, s), False{}, quiet) : {Pair.snd(O.St, List<&2, O.Node>, O.msg.go(_, cfg, O.Bits.inc(O.St.t(s)), O.St.info(s), O.St.grown(s), List.append(&2, O.Node, O.St.cview(s), [O.Node.leaf(O.St.t(s))]), O.St.ready(s), O.St.busy(s))) == Nil{} : List<&2, O.Node>}
  {==}

def Optchat.message_merges_nothing(cfg, s, quiet):
  message_merges_nothing(cfg, s, quiet)
