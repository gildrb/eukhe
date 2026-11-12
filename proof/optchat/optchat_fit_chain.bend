# eukhe: the proof of LAW optchat_fit_chain
# LAC.ch.fit (proof/optchat/base/chain.bend): the scan's answer is the
# oldest most due mergeable pair, merge replaces it, and the fit stops
# within budget or with no pair left.

import Base
import ../../laws/optchat/queries.bend as OptchatQueries
import ./base/chain.bend as LAC

def OptchatQueries.optchat_fit_chain(m, t, budget, ph, info, v):
  LAC.ch.fit(m, t, budget, ph, info, v)
