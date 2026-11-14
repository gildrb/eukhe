# eukhe: the proof of LAW agent_tree_entry_answers
#
# PROOF: the spelled request reads back whole with nothing left
# (ate.reads), so the entry answers the model's decision spelled
# (ate.reply).

import Base
import ../../bend/agent_tree.bend as T
import ../../bend/ffi_agent_tree.bend as FAt
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/agent_tree.bend as AgentTree
import ./base/entry.bend as ATE

def AgentTree.agent_tree_entry_answers(q, fit):
  %Equal.sym(Wr.Dec<FAt.Req>, FAt.get_req(AgentTree.w_req(q, "")), Wr.Got{q, ""}, ATE.ate.reads(q, "", fit)) : {FAt.ffi.got(_) == AgentTree.w_reply(q) : String}
  ATE.ate.reply(q)
