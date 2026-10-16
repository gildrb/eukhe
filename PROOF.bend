# PROOF: one proof per law of LAWS.bend. The proofs and their lemmas live
# in bend/proof_cover.bend (coverage, messages, merges), bend/proof_fit.bend
# (batches, summarized lines, compaction views), bend/proof_push.bend
# (Taelin's push up to 20,000 and the T = 10 example, by computation) and
# bend/proof_agree.bend (Taelin's push at every step, by induction).
#
#   bend PROOF.bend             checks every proof
#   bend PROOF.bend --verdict   checks them again with the proven kernel

import Base
import ./LAWS.bend as Laws
import ./bend/proof_cover.bend as Cover
import ./bend/proof_fit.bend as Fit
import ./bend/proof_push.bend as Push
import ./bend/proof_agree.bend as Agree
import ./bend/proof_compactor.bend as Compactor

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

def Laws.push_agrees_always(n):
  Agree.push_agrees_always(n)

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

# (H1) A compactor call always ends with a line that fits

def Laws.line_calls_at_most_tries(tries, node, input, rs):
  Compactor.pc.line_calls_at_most_tries(tries, node, input, rs)

def Laws.line_fits(tries, k, c, rest, rs):
  Compactor.pc.line_fits(tries, k, c, rest, rs)

def Laws.line_takes_first_fit(tries, node, input, rs):
  Compactor.pc.line_takes_first_fit(tries, node, input, rs)

def Laws.line_stops_when_not_shorter(t, node, input, a, b, rest, over, longer):
  Compactor.pc.line_stops_when_not_shorter(t, node, input, a, b, rest, over, longer)

def Laws.line_empty_is_a_try(t, node, input, rest):
  Compactor.pc.line_empty_is_a_try(t, node, input, rest)

def Laws.line_error_fails(t, node, input, rest):
  Compactor.pc.line_error_fails(t, node, input, rest)

def Laws.fail_cap_builds(n, os, many):
  Compactor.pc.fail_cap_builds(os, n, many)

# (H2) A turn never waits forever for the memory

def Laws.need_first(cfg, s):
  Compactor.pc.need_first(cfg, s)

def Laws.need_first_running(cfg, s):
  Compactor.pc.need_first_running(cfg, s)

def Laws.wait_keeps_needed(s):
  Compactor.pc.wait_keeps_needed(s)

def Laws.need_progress(cfg, evs, room, idle):
  Compactor.pc.need_progress(cfg, evs, room, idle)

def Laws.settle_falls(ps, k, o, due, lands):
  Compactor.pc.settle_falls(ps, k, o, due, lands)

def Laws.settle_bounded(es, ps):
  Compactor.pc.settle_bounded(es, ps)

def Laws.settle_reached(es, ps, enough):
  Compactor.pc.settle_reached(es, ps, enough)

def Laws.settle_start(p, info, v):
  Compactor.pc.settle_start(p, info, v)
