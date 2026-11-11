# eukhe: the proof of LAW optchat_build_notes
# A build files the size in the map's levels (LQ.oq.lv: a set reads back
# at its key, every other key keeps its value), drops n from the busy
# calls (LCs.cs.del), keeps T, the view and shrink, and takes the
# compaction view's sawtooth step under the new sizes (LAC.ch.saw).

import Base
import ../../bend/optchat/node.bend as ONode
import ../../bend/optchat/info.bend as OInfo
import ../../bend/optchat/state.bend as OState
import ../../spec/memory/optchat.bend as S
import ../../laws/optchat/queries.bend as OptchatQueries
import ./base/step.bend as LA
import ./base/queries.bend as LQ
import ./base/counts.bend as LCs
import ./base/chain.bend as LAC

def bn.info(info: OInfo.Info, n: ONode.Node, +z: Nat, m: ONode.Node, map: {S.is_map(info) == True{} : Bool}) -> {OInfo.Info.get(OInfo.Info.set(info, n, z), m) == S.info_after(n, z, m, OInfo.Info.get(info, m)) : Maybe<&2, Nat>}:
  match info:
    case OInfo.All{a}:
      LA.cover.absurd({OInfo.Info.get(OInfo.Info.set(OInfo.All{a}, n, z), m) == S.info_after(n, z, m, OInfo.Info.get(OInfo.All{a}, m)) : Maybe<&2, Nat>}, map)
    case OInfo.Lvls{ts}:
      match n m:
        case ONode.Node{l, +i} ONode.Node{k, +j}:
          LQ.oq.lv(l, ts, k, i, j, z)

def OptchatQueries.optchat_build_notes(cfg, s, n, size, m, map):
  match s:
    case OState.St{+t, +info, view, shrink, +cview, ready, +busy}:
      ({==}, ({==}, ({==}, ({==}, (bn.info(info, n, size, m, map), (LCs.cs.del(busy, n, m), LAC.ch.saw(cfg, t, OInfo.Info.set(info, n, size), cview)))))))
