# eukhe: the proof of LAW need_progress_due
# The view tiles the chat (view_covers), so its leading lines before the
# due mark tile a prefix of it (npd.tiles); the scan of need_progress
# (LAP.pc.scan) runs on that prefix, the view the queue reads under the
# mark.

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

# one past the last message of the leading lines of v from s that start
# before due
def npd.end.at(go: Bool, +s: Nat, rec: Nat) -> Nat:
  match go:
    case True{}:
      rec
    case False{}:
      s

def npd.end(v: List<&2, ONode.Node>, +due: Nat, +s: Nat) -> Nat:
  match v:
    case Nil{}:
      s
    case +h <> rest:
      npd.end.at(Nat.is_lt(ONode.Node.start(h), due), s, npd.end(rest, due, Nat.add(s, ONode.Node.count(h))))

def npd.keep(go: Bool, +s: Nat, +h: ONode.Node, l: List<&2, ONode.Node>, -e: Nat, st: {ONode.Node.start(h) == s : Nat}, tl: S.Tiles(Nat.add(s, ONode.Node.count(h)), l, e)) -> S.Tiles(s, OQueue.lines.keep(go, h, l), npd.end.at(go, s, e)):
  match go:
    case True{}:
      (st, tl)
    case False{}:
      {==}

# the leading lines of a tiling that start before due tile its prefix
def npd.tiles(v: List<&2, ONode.Node>, +due: Nat, +s: Nat, -e: Nat, tiles: S.Tiles(s, v, e)) -> S.Tiles(s, OQueue.lines.before(due, v), npd.end(v, due, s)):
  match v:
    case Nil{}:
      {==}
    case +h <> +rest:
      (st, tl) = tiles
      +s2 = Nat.add(s, ONode.Node.count(h))
      npd.keep(Nat.is_lt(ONode.Node.start(h), due), s, h, OQueue.lines.before(due, rest), npd.end(rest, due, s2), st, npd.tiles(rest, due, s2, e, tl))

def npd.go(+cfg: OState.Cfg, +due: Nat, s: OState.St, -e: Nat, tiles: S.Tiles(0n, OState.St.view(s), e), +room: {Nat.is_lt(List.length(&2, ONode.Node, OState.St.busy(s)), OState.Cfg.jobs(cfg)) == True{} : Bool}, idle: {C.idle(OState.St.info(s), OQueue.lines.before(due, OState.St.view(s)), OState.St.busy(s)) == True{} : Bool}) -> {OBits.Nat.is_pos(List.length(&2, ONode.Node, OQueue.cands.need.due(cfg, s, due))) == True{} : Bool}:
  match s:
    case OState.St{t, +info, +view, shrink, cview, ready, +busy}:
      +jobs = OState.Cfg.jobs(cfg)
      LAP.pc.scan(OQueue.lines.before(due, view), Nat.sub(jobs, List.length(&2, ONode.Node, busy)), info, busy, jobs, 0n, 0n, npd.end(view, due, 0n), npd.tiles(view, due, 0n, e, tiles), idle, LAP.pc.sub_pos(List.length(&2, ONode.Node, busy), jobs, room), LAP.pc.under0(jobs, busy, room))

def Optchat.need_progress_due(cfg, evs, due, room, idle):
  npd.go(cfg, due, OStep.run(cfg, evs), S.total.of(cfg, evs), LA.view_covers(cfg, evs), room, idle)
