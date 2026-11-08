# eukhe: the proof of LAW optchat_cands_spec
#
# PROOF: the view's lines that start are the spec's within the room (oq.view), the ready merges too (oq.ready), and the first n of both lists is the first n of the first, then of the second within what is left (oq.take_app).

import Base
import ../../bend/optchat/bits.bend as OBits
import ../../bend/optchat/node.bend as ONode
import ../../bend/optchat/info.bend as OInfo
import ../../bend/optchat/state.bend as OState
import ../../bend/optchat/step.bend as OStep
import ../../bend/optchat/queue.bend as OQueue
import ../../bend/optchat/ctx.bend as OCtx
import ../../spec/memory/optchat.bend as S
import ../../laws/optchat/queries.bend as OptchatQueries
import ./base/queries.bend as LQ

def OptchatQueries.optchat_cands_spec(cfg, s):
  %Equal.sym(List<&2, ONode.Node>, OQueue.cand.view(OState.St.view(s), OState.St.info(s), OState.St.busy(s), OState.Cfg.jobs(cfg), 0n, Nat.sub(OState.Cfg.jobs(cfg), List.length(&2, ONode.Node, OState.St.busy(s)))), S.take(Nat.sub(OState.Cfg.jobs(cfg), List.length(&2, ONode.Node, OState.St.busy(s))), S.queue.lines(OState.St.info(s), OState.St.busy(s), OState.Cfg.jobs(cfg), OState.St.view(s), 0n)), LQ.oq.view(OState.St.view(s), Nat.sub(OState.Cfg.jobs(cfg), List.length(&2, ONode.Node, OState.St.busy(s))), OState.St.info(s), OState.St.busy(s), OState.Cfg.jobs(cfg), 0n)) : {List.append(&2, ONode.Node, _, OQueue.cand.ready(OState.St.ready(s), OState.St.busy(s), Nat.sub(Nat.sub(OState.Cfg.jobs(cfg), List.length(&2, ONode.Node, OState.St.busy(s))), List.length(&2, ONode.Node, _)))) == S.cands(cfg, s) : List<&2, ONode.Node>}
  %Equal.sym(List<&2, ONode.Node>, OQueue.cand.ready(OState.St.ready(s), OState.St.busy(s), Nat.sub(Nat.sub(OState.Cfg.jobs(cfg), List.length(&2, ONode.Node, OState.St.busy(s))), List.length(&2, ONode.Node, S.take(Nat.sub(OState.Cfg.jobs(cfg), List.length(&2, ONode.Node, OState.St.busy(s))), S.queue.lines(OState.St.info(s), OState.St.busy(s), OState.Cfg.jobs(cfg), OState.St.view(s), 0n))))), S.take(Nat.sub(Nat.sub(OState.Cfg.jobs(cfg), List.length(&2, ONode.Node, OState.St.busy(s))), List.length(&2, ONode.Node, S.take(Nat.sub(OState.Cfg.jobs(cfg), List.length(&2, ONode.Node, OState.St.busy(s))), S.queue.lines(OState.St.info(s), OState.St.busy(s), OState.Cfg.jobs(cfg), OState.St.view(s), 0n)))), S.queue.ready(OState.St.busy(s), OState.St.ready(s))), LQ.oq.ready(OState.St.ready(s), Nat.sub(Nat.sub(OState.Cfg.jobs(cfg), List.length(&2, ONode.Node, OState.St.busy(s))), List.length(&2, ONode.Node, S.take(Nat.sub(OState.Cfg.jobs(cfg), List.length(&2, ONode.Node, OState.St.busy(s))), S.queue.lines(OState.St.info(s), OState.St.busy(s), OState.Cfg.jobs(cfg), OState.St.view(s), 0n)))), OState.St.busy(s))) : {List.append(&2, ONode.Node, S.take(Nat.sub(OState.Cfg.jobs(cfg), List.length(&2, ONode.Node, OState.St.busy(s))), S.queue.lines(OState.St.info(s), OState.St.busy(s), OState.Cfg.jobs(cfg), OState.St.view(s), 0n)), _) == S.cands(cfg, s) : List<&2, ONode.Node>}
  LQ.oq.take_app(Nat.sub(OState.Cfg.jobs(cfg), List.length(&2, ONode.Node, OState.St.busy(s))), S.queue.lines(OState.St.info(s), OState.St.busy(s), OState.Cfg.jobs(cfg), OState.St.view(s), 0n), S.queue.ready(OState.St.busy(s), OState.St.ready(s)))
