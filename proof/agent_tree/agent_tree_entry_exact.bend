# eukhe: the proof of LAW agent_tree_entry_exact
#
# PROOF: the decoder answers Got{q, rest} only for an input that is the
# spelling of q before rest, every number and count within the wire
# (atx.req, stage by stage; a node by induction on the fuel); the entry
# answers a decision only for a request read whole with nothing left
# (atx.top).

import Base
import ../../bend/agent_tree.bend as T
import ../../bend/ffi_agent_tree.bend as FAt
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/agent_tree.bend as AgentTree
import ./base/entry.bend as ATE
import ./base/exact.bend as ATX

def atx.top(-s: String, d: Wr.Dec<FAt.Req>, rp: ATX.atx.QP(s, d), ok: {LawsBase.wire_opens_err(FAt.ffi.got(d)) == False{} : Bool}) -> Sigma<&1, &1, FAt.Req, v => {s == AgentTree.w_req(v, "") : String} & {AgentTree.fit_req(v) == True{} : Bool}>:
  match d:
    case Wr.Got{+q, rest}:
      match rest:
        case SNil{}:
          (q, rp)
        case SCon{x, y}:
          ATE.ate.absurdT(Sigma<&1, &1, FAt.Req, v2 => {s == AgentTree.w_req(v2, "") : String} & {AgentTree.fit_req(v2) == True{} : Bool}>, ok)
    case Wr.Bad{}:
      ATE.ate.absurdT(Sigma<&1, &1, FAt.Req, v2 => {s == AgentTree.w_req(v2, "") : String} & {AgentTree.fit_req(v2) == True{} : Bool}>, ok)

def AgentTree.agent_tree_entry_exact(s, ok):
  atx.top(s, FAt.get_req(s), ATX.atx.req(s), ok)
