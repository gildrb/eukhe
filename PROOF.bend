# PROOF: one proof per law of LAWS.bend. The proofs and their lemmas live
# in bend/proof_cover.bend (coverage, messages, merges), bend/proof_fit.bend
# (batches, summarized lines, compaction views) and bend/proof_push.bend
# (Taelin's push and the T = 10 example, by computation).
#
#   bend PROOF.bend             checks every proof
#   bend PROOF.bend --verdict   checks them again with the proven kernel

import Base
import ./LAWS.bend as Laws
import ./bend/proof_cover.bend as Cover
import ./bend/proof_fit.bend as Fit
import ./bend/proof_push.bend as Push

# (a) The view

def Laws.view_covers(cfg, evs):
  Cover.view_covers(cfg, evs)

def Laws.cview_covers(cfg, evs):
  Cover.cview_covers(cfg, evs)

# (b) A message

def Laws.message_appends(cfg, s, quiet):
  Cover.message_appends(cfg, s, quiet)

def Laws.message_merges_nothing(cfg, s, quiet):
  Cover.message_merges_nothing(cfg, s, quiet)

# (c) A merge

def Laws.merge_is_one_pair(info, v, a):
  Cover.merge_is_one_pair(info, v, a)

def Laws.merge_covers(info, s, v, w, e, tiles, merged):
  Cover.merge_covers(info, s, v, w, e, tiles, merged)

# (d) Taelin's push

def Laws.push_agrees():
  Push.push_agrees()

# (e) A batch

def Laws.fit_reaches_budget(m, t, budget, ph, info, v):
  Fit.fit_reaches_budget(m, t, budget, ph, info, v)

def Laws.fit_merges_built(m, t, budget, ph, info, v):
  Fit.fit_merges_built(m, t, budget, ph, info, v)

def Laws.view_summarized(cfg, evs):
  Fit.view_summarized(cfg, evs)

def Laws.cview_summarized(cfg, evs):
  Fit.cview_summarized(cfg, evs)

# (f) First is not last

def Laws.last_merges_8_9():
  Push.last_merges_8_9()

def Laws.first_merges_0_7():
  Push.first_merges_0_7()

def Laws.first_is_not_last():
  Push.first_is_not_last()

def Laws.first_leaves_push():
  Push.first_leaves_push()

# (g) A compaction's view

def Laws.context_ends_at_node(s, n):
  Fit.context_ends_at_node(s, n)

def Laws.context_is_prefix(s, n):
  Fit.context_is_prefix(s, n)
