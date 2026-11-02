# eukhe: the proof of LAW optchat_fit_spec
#
# PROOF: the sizes, the pairs, the due order (in numbers, through the values of the bit sums), the most due pair, a merge and the choice of the next one are the spec's, so each step of the fit is (proof/optchat/base/batch.bend ob.fit).

import Base
import ../../bend/optchat/node.bend as ONode
import ../../bend/optchat/info.bend as OInfo
import ../../bend/optchat/fit.bend as OFit
import ../../bend/optchat/state.bend as OState
import ../../bend/optchat/step.bend as OStep
import ../../spec/memory/optchat.bend as S
import ../../laws/optchat/queries.bend as OptchatQueries
import ./base/batch.bend as LB

def OptchatQueries.optchat_fit_spec(m, t, budget, ph, info, v):
  LB.ob.fit(m, t, budget, ph, info, v)
