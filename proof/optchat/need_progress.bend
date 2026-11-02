# eukhe: the proof of LAW need_progress
# The scan of the whole view (LAP.pc.scan, proof/optchat/base/scan.bend)
# from message 0: the view tiles the chat (view_covers).

import Base
import ../../bend/compactor.bend as C
import ../../bend/optchat/bits.bend as OBits
import ../../bend/optchat/node.bend as ONode
import ../../bend/optchat/queue.bend as OQueue
import ../../bend/optchat/state.bend as OState
import ../../bend/optchat/step.bend as OStep
import ../../spec/memory/optchat.bend as S
import ../../laws/optchat.bend as Optchat
import ./base/scan.bend as LAP
import ./base/step.bend as LA

def pc.need_progress(+cfg: OState.Cfg, +evs: List<&2, OState.Ev>, +room: {Nat.is_lt(List.length(&2, ONode.Node, OState.St.busy(OStep.run(cfg, evs))), OState.Cfg.jobs(cfg)) == True{} : Bool}, idle: {C.idle(OState.St.info(OStep.run(cfg, evs)), OState.St.view(OStep.run(cfg, evs)), OState.St.busy(OStep.run(cfg, evs))) == True{} : Bool}) -> {OBits.Nat.is_pos(List.length(&2, ONode.Node, OQueue.cands.need(cfg, OStep.run(cfg, evs)))) == True{} : Bool}:
  +s = OStep.run(cfg, evs)
  +jobs = OState.Cfg.jobs(cfg)
  +busy = OState.St.busy(s)
  LAP.pc.scan(OState.St.view(s), Nat.sub(jobs, List.length(&2, ONode.Node, busy)), OState.St.info(s), busy, jobs, 0n, 0n, S.total.of(cfg, evs), LA.view_covers(cfg, evs), idle, LAP.pc.sub_pos(List.length(&2, ONode.Node, busy), jobs, room), LAP.pc.under0(jobs, busy, room))

def Optchat.need_progress(cfg, evs, room, idle):
  pc.need_progress(cfg, evs, room, idle)
