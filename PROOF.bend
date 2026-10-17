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
import ./bend/proof_wait.bend as Waits
import ./bend/proof_lease.bend as Leases
import ./bend/proof_child.bend as Children
import ./bend/proof_run.bend as Runs
import ./bend/proof_admission.bend as Admission
import ./bend/proof_admission_wait.bend as AdmissionWait
import ./bend/proof_tree.bend as Trees
import ./bend/proof_job.bend as Jobs
import ./bend/proof_infer.bend as Infer
import ./bend/proof_quirks.bend as Quirks

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

# (H6) Every other wait has an exit

def Laws.wait_ends_once(dl, xs):
  Waits.wait_ends_once(dl, xs)

def Laws.wait_end_is_final(dl, pre, post, stop):
  Waits.wait_end_is_final(dl, pre, post, stop)

def Laws.wait_arrival_wins(dl, pre, post, calm):
  Waits.wait_arrival_wins(dl, pre, post, calm)

def Laws.wait_cancel_wins(dl, pre, post, calm):
  Waits.wait_cancel_wins(dl, pre, post, calm)

def Laws.lease_fifo(evs):
  Leases.lease_fifo(evs)

def Laws.lease_never_idle(evs):
  Leases.lease_never_idle(evs)

def Laws.lease_keeps_waiters(s, e, k, o, waits, other):
  Leases.lease_keeps_waiters(s, e, k, o, waits, other)

def Laws.lease_stop_never_holds(evs, k, o, rest, waits):
  Leases.lease_stop_never_holds(evs, k, o, rest, waits)

def Laws.lease_crash_frees(s, p):
  Leases.lease_crash_frees(s, p)

# (H5) Every subagent reports back exactly once

def Laws.child_stalls_in_time(cfg, w, h, hs, long):
  Children.pc.stalls_in_time(cfg, w, h, hs, long)

def Laws.child_unreachable_in_time(cfg, w, d, ds, long):
  Children.pc.unreachable_in_time(cfg, w, d, ds, long)

def Laws.child_clock_bounded(cfg, w, e, o, full):
  Children.pc.clock_bounded(cfg, w, e, o, full)

def Laws.child_progress_is_not_a_stall(cfg, w, e, x, news):
  Children.pc.progress_is_not_a_stall(cfg, w, e, x, news)

def Laws.child_one_live(cfg, evs):
  Children.pc.one_live(cfg, evs)

def Laws.child_report_once(cfg, evs):
  Children.pc.report_once(cfg, evs)

def Laws.child_resubmits_per_abort(cfg, evs):
  Children.pc.resubmits_per_abort(cfg, evs)

def Laws.child_delivered_once(cfg, evs, d1, o1, d2, o2, d3, o3, owing, m, waits):
  Children.pc.delivered_once(cfg, evs, d1, o1, d2, o2, d3, o3, owing, m, waits)

# (H4) Every run ends

def Laws.run_ends(cfg, evs, long, more):
  Runs.run_ends(cfg, evs, long, more)

def Laws.run_end_stays(cfg, s, ended, e):
  Runs.end_stays(cfg, s, e, ended)

def Laws.run_abort_ends_now(cfg, s, live):
  Runs.abort_now(cfg, s, live)

def Laws.run_rounds_capped(cfg, evs):
  Runs.rounds_capped(cfg, evs)

def Laws.run_loop_needs_repeats(cfg, evs):
  Runs.loop_needs_repeats(cfg, evs)

def Laws.run_rounds_fail_at_cap(cfg, evs):
  Runs.rounds_fail_at_cap(cfg, evs)

def Laws.run_polls_need_defers(cfg, evs):
  Runs.polls_need_defers(cfg, evs)

# (H3) A user's request never waits behind background work

def Laws.admission_preempts(s):
  Admission.preempts(s)

def Laws.admission_capacity(s, o):
  Admission.capacity(s, o)

def Laws.admission_no_lost_wakeup(l, q, os):
  Admission.no_lost_wakeup(l, q, os)

def Laws.admission_background_yields(l, q, os):
  Admission.background_yields(l, q, os)

def Laws.admission_fifo(l, q, os):
  Admission.fifo_per_class(l, q, os)

def Laws.admission_interactive_step(s, o, w, ws, wf):
  AdmissionWait.interactive_step(s, o, w, ws, wf)

def Laws.admission_interactive_bound(l, q, pre, os, w, waits):
  AdmissionWait.interactive_bound(l, q, pre, os, w, waits)

def Laws.admission_ended_stays_ended(s, o, k, e):
  Admission.ended_stays_ended(s, o, k, e)

def Laws.admission_end_twice_changes_nothing(s, k, e):
  Admission.end_twice_changes_nothing(s, k, e)

def Laws.admission_every_ticket_ends(s, k, live):
  Admission.every_ticket_ends(s, k, live)

# (S1) The session tree

def Laws.tree_apply_sound(t, good, r):
  Trees.apply_sound(t, good, r)

def Laws.tree_replay_sound(rs):
  Trees.replay_sound(rs)

def Laws.tree_snapshot(pre, post):
  Trees.snapshot(pre, post)

def Laws.tree_rewind_reaches(a, b, ga, gb):
  Trees.rewind_reaches(a, b, ga, gb)

def Laws.tree_rewind_still(a, ga):
  Trees.rewind_still(a, ga)

def Laws.tree_rewind_minimal(a, b, ga, gb):
  Trees.rewind_minimal(a, b, ga, gb)

def Laws.tree_delete_removes(t, good, x):
  Trees.delete_removes(t, good, x)

def Laws.tree_delete_within(t, good, x):
  Trees.delete_within(t, good, x)

def Laws.tree_delete_only_below(t, good, x):
  Trees.delete_only_below(t, good, x)

def Laws.tree_put_sets(t, good, k, p, v, fits):
  Trees.put_sets(t, good, k, p, v, fits)

def Laws.tree_put_keeps_others(t, good, k, p, v, x, other):
  Trees.put_keeps_others(t, good, k, p, v, x, other)

# (S2) Jobs and limits

def Laws.job_output_bounded(c, es):
  Jobs.pj.job_output_bounded(c, es)

def Laws.job_no_silent_loss(cap, es):
  Jobs.pj.job_no_silent_loss(cap, es)

def Laws.job_optout_keeps_all(es):
  Jobs.pj.job_optout_keeps_all(es)

def Laws.job_cap_drops_only_excess(c, es, fits):
  Jobs.pj.job_cap_drops_only_excess(c, es, fits)

def Laws.job_ends_once(cap, es):
  Jobs.pj.job_ends_once(cap, es)

def Laws.job_end_is_final(cap, pre, post, ended):
  Jobs.pj.job_end_is_final(cap, pre, post, ended)

def Laws.job_kill_ends_now(cap, k, d):
  Jobs.pj.job_kill_ends_now(cap, k, d)

def Laws.call_blocks_at_most_budget(b, es, long):
  Jobs.pj.call_blocks_at_most_budget(b, es, long)

def Laws.call_settles_with_job(cap, b, es, x, settled):
  Jobs.pj.call_settles_with_job(cap, b, es, x, settled)

def Laws.stream_journals_two(es):
  Jobs.pj.stream_journals_two(es)

def Laws.stream_settles_once(es):
  Jobs.pj.stream_settles_once(es)

def Laws.stream_settle_carries_all(es, ended):
  Jobs.pj.stream_settle_carries_all(es, ended)

def Laws.rewind_stops_orphans(js, keep):
  Jobs.pj.rewind_stops_orphans(js, keep)

def Laws.rewind_keeps_target_jobs(js, keep):
  Jobs.pj.rewind_keeps_target_jobs(js, keep)

# (S6) The inference layer

def Laws.quirk_unknown_rejected(known, pre, r, post, bad):
  Quirks.pq.quirk_unknown_rejected(known, pre, r, post, bad)

def Laws.quirk_clash_rejected(known, pre, a, mid, b, post, both):
  Quirks.pq.quirk_clash_rejected(known, pre, a, mid, b, post, both)

def Laws.quirk_unknown_when_none(rs, q, d, none):
  Quirks.pq.quirk_unknown_when_none(rs, q, d, none)

def Laws.quirk_known_when_some(rs, q, d, some):
  Quirks.pq.quirk_known_when_some(rs, q, d, some)

def Laws.quirk_highest_wins(known, pre, r, post, q, ok, hit, top):
  Quirks.pq.quirk_highest_wins(known, pre, r, post, q, ok, hit, top)

def Laws.quirk_order_free(known, pre, a, b, post, q, d, ok):
  Quirks.pq.quirk_order_free(known, pre, a, b, post, q, d, ok)

def Laws.quirk_compile_order_free(known, pre, a, b, post):
  Quirks.pq.quirk_compile_order_free(known, pre, a, b, post)

def Laws.force_bounded(r, replies, sup, free):
  Infer.pi.force_bounded(r, replies, sup, free)

def Laws.force_first_flag(r, replies, sup, free):
  Infer.pi.force_first_flag(r, replies, sup, free)

def Laws.force_retry_flag(r, replies, sup, free):
  Infer.pi.force_retry_flag(r, replies, sup, free)

def Laws.force_reports(r, replies, sup, free):
  Infer.pi.force_reports(r, replies, sup, free)

def Laws.strict_within_cap(cap, ts):
  Infer.pi.strict_within_cap(cap, ts)

def Laws.strict_keeps_every_tool(cap, ts, i):
  Infer.pi.strict_keeps_every_tool(cap, ts, i)

def Laws.strict_by_priority(cap, ts):
  Infer.pi.strict_by_priority(cap, ts)

def Laws.guard_cuts_repeats(xs, k, rep):
  Infer.pi.guard_cuts_repeats(xs, k, rep)

def Laws.guard_keeps_others(xs, k, calm):
  Infer.pi.guard_keeps_others(xs, k, calm)

def Laws.compact_starts_early(xs, m, lim, small, steps):
  Infer.pi.compact_starts_early(xs, m, lim, small, steps)
