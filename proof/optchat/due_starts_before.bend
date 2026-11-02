# eukhe: the proof of LAW due_starts_before
# Under the mark the queue reads the view's leading lines and the ready
# merges that start before it (dsb.lines, dsb.nodes); the queue starts
# only some of the lines it reads (dsb.view) and of the merges
# (dsb.ready), in their order, and appends the two (dsb.append).

import Base
import ../../bend/optchat/info.bend as OInfo
import ../../bend/optchat/node.bend as ONode
import ../../bend/optchat/bits.bend as OBits
import ../../bend/optchat/queue.bend as OQueue
import ../../bend/optchat/state.bend as OState
import ../../spec/memory/optchat.bend as S
import ../../laws/optchat.bend as Optchat
import ../base/logic/bool.bend as LLogicBool

def dsb.and(a: Bool, -b: Bool, ea: {a == True{} : Bool}, eb: {b == True{} : Bool}) -> {Bool.and(a, b) == True{} : Bool}:
  match a:
    case True{}:
      eb
    case False{}:
      ea

def dsb.lines.keep(go: Bool, +due: Nat, +h: ONode.Node, l: List<&2, ONode.Node>, eg: {Nat.is_lt(ONode.Node.start(h), due) == go : Bool}, ih: {S.starts_before(due, l) == True{} : Bool}) -> {S.starts_before(due, OQueue.lines.keep(go, h, l)) == True{} : Bool}:
  match go:
    case False{}:
      {==}
    case True{}:
      dsb.and(Nat.is_lt(ONode.Node.start(h), due), S.starts_before(due, l), eg, ih)

# the leading lines before the mark start before it
def dsb.lines(v: List<&2, ONode.Node>, +due: Nat) -> {S.starts_before(due, OQueue.lines.before(due, v)) == True{} : Bool}:
  match v:
    case Nil{}:
      {==}
    case +h <> +rest:
      dsb.lines.keep(Nat.is_lt(ONode.Node.start(h), due), due, h, OQueue.lines.before(due, rest), {==}, dsb.lines(rest, due))

def dsb.nodes.keep(go: Bool, +due: Nat, +h: ONode.Node, l: List<&2, ONode.Node>, eg: {Nat.is_lt(ONode.Node.start(h), due) == go : Bool}, ih: {S.starts_before(due, l) == True{} : Bool}) -> {S.starts_before(due, ONode.Nodes.keep(go, h, l)) == True{} : Bool}:
  match go:
    case False{}:
      ih
    case True{}:
      dsb.and(Nat.is_lt(ONode.Node.start(h), due), S.starts_before(due, l), eg, ih)

# so do the merges before the mark
def dsb.nodes(rs: List<&2, ONode.Node>, +due: Nat) -> {S.starts_before(due, OQueue.nodes.before(due, rs)) == True{} : Bool}:
  match rs:
    case Nil{}:
      {==}
    case +h <> +rest:
      dsb.nodes.keep(Nat.is_lt(ONode.Node.start(h), due), due, h, OQueue.nodes.before(due, rest), {==}, dsb.nodes(rest, due))

def dsb.emit(stop: Bool, built: Bool, free: Bool, +due: Nat, +h: ONode.Node, rec: List<&2, ONode.Node>, eh: {Nat.is_lt(ONode.Node.start(h), due) == True{} : Bool}, ih: {S.starts_before(due, rec) == True{} : Bool}) -> {S.starts_before(due, OQueue.cand.emit(stop, built, free, h, rec)) == True{} : Bool}:
  match stop built free:
    case True{} y z:
      {==}
    case False{} True{} z:
      ih
    case False{} False{} True{}:
      dsb.and(Nat.is_lt(ONode.Node.start(h), due), S.starts_before(due, rec), eh, ih)
    case False{} False{} False{}:
      ih

# the lines the queue starts are lines it reads
def dsb.view(v: List<&2, ONode.Node>, +info: OInfo.Info, +busy: List<&2, ONode.Node>, +jobs: Nat, +unb: Nat, room: Nat, +due: Nat, ev: {S.starts_before(due, v) == True{} : Bool}) -> {S.starts_before(due, OQueue.cand.view(v, info, busy, jobs, unb, room)) == True{} : Bool}:
  match v room:
    case Nil{} r:
      {==}
    case h <> rest 0n:
      {==}
    case +h <> +rest 1n+r:
      +unb2 = Nat.add(unb, OBits.bit(Bool.not(OInfo.Info.built(info, h)), 0n))
      +room2 = Nat.sub(1n+r, OBits.bit(Bool.and(Bool.not(OInfo.Info.built(info, h)), Bool.not(ONode.Nodes.has(busy, h))), 0n))
      +ev2 = ev
      dsb.emit(Nat.is_ge(unb, jobs), OInfo.Info.built(info, h), Bool.not(ONode.Nodes.has(busy, h)), due, h, OQueue.cand.view(rest, info, busy, jobs, unb2, room2), LLogicBool.pf.and_l(Nat.is_lt(ONode.Node.start(h), due), S.starts_before(due, rest), ev2), dsb.view(rest, info, busy, jobs, unb2, room2, due, LLogicBool.pf.and_r(Nat.is_lt(ONode.Node.start(h), due), S.starts_before(due, rest), ev2)))

def dsb.keep(k: Bool, +due: Nat, +h: ONode.Node, l: List<&2, ONode.Node>, eh: {Nat.is_lt(ONode.Node.start(h), due) == True{} : Bool}, ih: {S.starts_before(due, l) == True{} : Bool}) -> {S.starts_before(due, ONode.Nodes.keep(k, h, l)) == True{} : Bool}:
  match k:
    case False{}:
      ih
    case True{}:
      dsb.and(Nat.is_lt(ONode.Node.start(h), due), S.starts_before(due, l), eh, ih)

# the merges the queue starts are merges it reads
def dsb.ready(rs: List<&2, ONode.Node>, +busy: List<&2, ONode.Node>, room: Nat, +due: Nat, er: {S.starts_before(due, rs) == True{} : Bool}) -> {S.starts_before(due, OQueue.cand.ready(rs, busy, room)) == True{} : Bool}:
  match rs room:
    case Nil{} r:
      {==}
    case h <> rest 0n:
      {==}
    case +h <> +rest 1n+r:
      +free = Bool.not(ONode.Nodes.has(busy, h))
      +room2 = Nat.sub(1n+r, OBits.bit(free, 0n))
      +er2 = er
      dsb.keep(free, due, h, OQueue.cand.ready(rest, busy, room2), LLogicBool.pf.and_l(Nat.is_lt(ONode.Node.start(h), due), S.starts_before(due, rest), er2), dsb.ready(rest, busy, room2, due, LLogicBool.pf.and_r(Nat.is_lt(ONode.Node.start(h), due), S.starts_before(due, rest), er2)))

def dsb.append(a: List<&2, ONode.Node>, +due: Nat, b: List<&2, ONode.Node>, ea: {S.starts_before(due, a) == True{} : Bool}, eb: {S.starts_before(due, b) == True{} : Bool}) -> {S.starts_before(due, List.append(&2, ONode.Node, a, b)) == True{} : Bool}:
  match a:
    case Nil{}:
      eb
    case +h <> +rest:
      +ea2 = ea
      dsb.and(Nat.is_lt(ONode.Node.start(h), due), S.starts_before(due, List.append(&2, ONode.Node, rest, b)), LLogicBool.pf.and_l(Nat.is_lt(ONode.Node.start(h), due), S.starts_before(due, rest), ea2), dsb.append(rest, due, b, LLogicBool.pf.and_r(Nat.is_lt(ONode.Node.start(h), due), S.starts_before(due, rest), ea2), eb))

def dsb.go(+cfg: OState.Cfg, +due: Nat, s: OState.St) -> {S.starts_before(due, OQueue.cands.due(cfg, s, due)) == True{} : Bool} & {S.starts_before(due, OQueue.cands.need.due(cfg, s, due)) == True{} : Bool}:
  match s:
    case OState.St{t, +info, +view, shrink, cview, +ready, +busy}:
      +jobs = OState.Cfg.jobs(cfg)
      +room = Nat.sub(jobs, List.length(&2, ONode.Node, busy))
      +lv = OQueue.lines.before(due, view)
      +c = OQueue.cand.view(lv, info, busy, jobs, 0n, room)
      +rs = OQueue.nodes.before(due, ready)
      +ec = dsb.view(lv, info, busy, jobs, 0n, room, due, dsb.lines(view, due))
      (dsb.append(c, due, OQueue.cand.ready(rs, busy, Nat.sub(room, List.length(&2, ONode.Node, c))), ec, dsb.ready(rs, busy, Nat.sub(room, List.length(&2, ONode.Node, c)), due, dsb.nodes(ready, due))), ec)

def Optchat.due_starts_before(cfg, s, due):
  dsb.go(cfg, due, s)
