# eukhe: the proof of LAW agent_tree_entry_refuses
#
# PROOF: the entry answers either a decision, which opens with a Nat
# (never 'E': ate.answer_ok, on wire_nat_not_err), or the one error form;
# so an answer that opens with 'E' is that error form.

import Base
import ../../bend/agent_tree.bend as T
import ../../bend/ffi_agent_tree.bend as FAt
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/agent_tree.bend as AgentTree
import ./base/entry.bend as ATE

def atf.refuse(d: Wr.Dec<FAt.Req>, bad: {LawsBase.wire_opens_err(FAt.ffi.got(d)) == True{} : Bool}) -> {FAt.ffi.got(d) == Wr.err("agent_tree: malformed request") : String}:
  match d:
    case Wr.Got{+q, rest}:
      match rest:
        case SNil{}:
          ATE.ate.absurdT({FAt.answer(q) == Wr.err("agent_tree: malformed request") : String}, Equal.trans(Bool, True{}, LawsBase.wire_opens_err(FAt.answer(q)), False{}, Equal.sym(Bool, LawsBase.wire_opens_err(FAt.answer(q)), True{}, bad), ATE.ate.answer_ok(q)))
        case SCon{x, y}:
          {==}
    case Wr.Bad{}:
      {==}

def AgentTree.agent_tree_entry_refuses(s, bad):
  atf.refuse(FAt.get_req(s), bad)
