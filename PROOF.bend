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
import ./bend/proof_retry.bend as Retries
import ./bend/proof_admission.bend as Admission
import ./bend/proof_admission_wait.bend as AdmissionWait
import ./bend/proof_tree.bend as Trees
import ./bend/proof_job.bend as Jobs
import ./bend/proof_sandbox.bend as Sandbox
import ./bend/proof_cvar.bend as Cvars
import ./bend/proof_director.bend as Directors
import ./bend/proof_infer.bend as Infer
import ./bend/proof_quirks.bend as Quirks
import ./bend/proof_tools.bend as Tools
import ./bend/proof_screen.bend as Screen
import ./bend/proof_tiny.bend as Tiny
import ./bend/proof_effort.bend as Effort
import ./laws/release.bend as Release
import ./bend/proof_semver.bend as Semver
import ./laws/auth_flight.bend as AuthFlight
import ./bend/proof_auth_flight.bend as AuthFlights
import ./laws/themes.bend as Themes
import ./bend/proof_themes.bend as ThemeProofs
import ./laws/dashboard_tokens.bend as DashTokens
import ./bend/proof_tokens.bend as Tokens
import ./laws/progress.bend as Prg
import ./bend/proof_progress.bend as Progress
import ./bend/proof_progress_report.bend as Reports
import ./laws/ladder.bend as Ladder
import ./laws/kernel_local.bend as KernelLocal
import ./bend/proof_kernel_local.bend as KernelLocals
import ./laws/storage.bend as Storage
import ./bend/proof_log.bend as Logs
import ./bend/proof_staging.bend as Stagings
import ./laws/recover.bend as Rec
import ./bend/proof_recover.bend as Recover
import ./laws/catalog_union.bend as CatalogUnion
import ./bend/proof_catalog_union.bend as CatalogUnions
import ./laws/cron.bend as Cronl
import ./bend/proof_cron_step.bend as Crons
import ./laws/supervisor.bend as Sup
import ./bend/proof_supervisor.bend as Supervision
import ./bend/proof_replace.bend as Replacing
import ./bend/proof_notice.bend as Notices
import ./laws/gateway_width.bend as GatewayWidth
import ./bend/proof_gateway_width.bend as GatewayWidths
import ./laws/tui_color.bend as TuiColor
import ./bend/proof_tui_color.bend as TuiColors
import ./laws/fsmode.bend as Fm
import ./bend/proof_fsmode.bend as FileModes
import ./laws/path_policy.bend as Pg
import ./bend/proof_path_policy.bend as PathPolicy

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

# (S3) The host and the sandbox

def Laws.proto_one_reply_each(fs, max, allowed):
  Sandbox.px.proto_one_reply_each(fs, max, allowed)

def Laws.proto_runs_only_accepted(fs, max, allowed):
  Sandbox.px.proto_runs_only_accepted(fs, max, allowed)

def Laws.proto_runs_every_accepted(fs, max, allowed):
  Sandbox.px.proto_runs_every_accepted(fs, max, allowed)

def Laws.proto_rejects_oversize(i, l, k, max, allowed, over):
  Sandbox.px.proto_rejects_oversize(i, l, k, max, allowed, over)

def Laws.cow_keeps_parent(ks, par, base, child, k, listed, calm):
  Sandbox.px.cow_keeps_parent(ks, par, base, child, k, listed, calm)

def Laws.cow_takes_child(ks, par, base, child, k, listed, moved, still):
  Sandbox.px.cow_takes_child(ks, par, base, child, k, listed, moved, still)

def Laws.cow_conflict_reported(ks, par, base, child, k, listed, moved, also, apart):
  Sandbox.px.cow_conflict_reported(ks, par, base, child, k, listed, moved, also, apart)

def Laws.cow_conflict_is_real(ks, par, base, child, k, clash):
  Sandbox.px.cow_conflict_is_real(ks, par, base, child, k, clash)

# (S4) Settings as console variables

def Laws.cvar_registry_unique(xs):
  Cvars.pv.cvar_registry_unique(xs)

def Laws.cvar_registry_typed(xs):
  Cvars.pv.cvar_registry_typed(xs)

def Laws.cvar_value_typed(xs, cfg, fam, x):
  Cvars.pv.cvar_value_typed(xs, cfg, fam, x)

def Laws.cvar_inherits(ds, cfg, fam, x):
  Cvars.pv.cvar_inherits(ds, cfg, fam, x)

def Laws.cvar_set_wins(ds, cfg, fam, p, ss, x, v, ok):
  Cvars.pv.cvar_set_wins(ds, cfg, fam, p, ss, x, v, ok)

def Laws.cvar_global_uniform(ds, cfg, fam, x, d, found, global):
  Cvars.pv.cvar_global_uniform(ds, cfg, fam, x, d, found, global)

def Laws.cvar_written_flagged(ss, ds, f):
  Cvars.pv.cvar_written_flagged(ss, ds, f)

def Laws.cvar_persist_roundtrip(ds, cfg, ss, x, keeps):
  Cvars.pv.cvar_persist_roundtrip(ds, cfg, ss, x, keeps)

def Laws.cvar_toggle_twice(ds, cfg, fam, a, x):
  Cvars.pv.cvar_toggle_twice(ds, cfg, fam, a, x)

def Laws.alias_expands_fully(cs, as):
  Cvars.pv.alias_expands_fully(cs, as)

def Laws.alias_self_cycle(n, as):
  Cvars.pv.alias_self_cycle(n, as)

def Laws.alias_unknown_reported(n, as, gone):
  Cvars.pv.alias_unknown_reported(n, as, gone)

def Laws.alias_runs_body(n, b, as, flat):
  Cvars.pv.alias_runs_body(n, b, as, flat)

def Laws.bind_press_plain(bs, k, as):
  Cvars.pv.bind_press_plain(bs, k, as)

def Laws.bind_unbound_runs_nothing(bs, k, as, free):
  Cvars.pv.bind_unbound_runs_nothing(bs, k, as, free)

def Laws.bind_first_wins(k, c, rest, as):
  Cvars.pv.bind_first_wins(k, c, rest, as)

# (S5) The Director stack

def Laws.dir_stack_bounded(s, vs, cap, fits):
  Directors.pd.dir_stack_bounded(s, vs, cap, fits)

def Laws.dir_loop_stack_bounded(vss, cap, l, fits):
  Directors.pd.dir_loop_stack_bounded(vss, cap, l, fits)

def Laws.dir_loop_ends(n, s, vss, cap, long):
  Directors.pd.dir_loop_ends(n, s, vss, cap, long)

def Laws.dir_end_is_final(cap, l, done, vs):
  Directors.pd.dir_end_is_final(cap, l, done, vs)

def Laws.dir_encode_sound(s):
  Directors.pd.dir_encode_sound(s)

def Laws.dir_resume_restores(s):
  Directors.pd.dir_resume_restores(s)

def Laws.dir_rewind_restores(a, s, good):
  Directors.pd.dir_rewind_restores(a, s, good)

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

def Laws.guard_cuts_loops(xs, k, lp):
  Infer.pi.guard_cuts_loops(xs, k, lp)

def Laws.guard_keeps_others(xs, k, calm):
  Infer.pi.guard_keeps_others(xs, k, calm)

def Laws.compact_starts_early(xs, m, lim, small, steps):
  Infer.pi.compact_starts_early(xs, m, lim, small, steps)

# (S7) The tool surface

def Laws.roster_fixed(es, s):
  Tools.pl.roster_fixed(es, s)

def Laws.roster_sent_fixed(es, r, d):
  Tools.pl.roster_sent_fixed(es, r, d)

def Laws.dyn_reaches_joined(s, t):
  Tools.pl.dyn_reaches_joined(s, t)

def Laws.dyn_drops_quit(s, t):
  Tools.pl.dyn_drops_quit(s, t)

def Laws.schema_has_intent(s):
  Tools.pl.schema_has_intent(s)

def Laws.schema_versioned(s):
  Tools.pl.schema_versioned(s)

def Laws.schema_keeps_params(s, x, has):
  Tools.pl.schema_keeps_params(s, x, has)

def Laws.schema_build_idempotent(s):
  Tools.pl.schema_build_idempotent(s)

def Laws.path_rejects_escape(segs, out):
  Tools.pl.path_rejects_escape(segs, out)

def Laws.path_resolves_inside(segs, inside):
  Tools.pl.path_resolves_inside(segs, inside)

def Laws.gate_prefix(ss, auto, ans):
  Tools.pl.gate_prefix(ss, auto, ans)

def Laws.gate_needs_yes(ss, auto, ans):
  Tools.pl.gate_needs_yes(ss, auto, ans)

def Laws.gate_deny_stops(pre, s, post, auto, ans, free, held):
  Tools.pl.gate_deny_stops(pre, s, post, auto, ans, free, held)

def Laws.gate_finish_runs_all(ss, auto, ans, fin):
  Tools.pl.gate_finish_runs_all(ss, auto, ans, fin)

# (S8) The interface

def Laws.tx_gapless(es, w):
  Screen.ps.tx_gapless(es, w)

def Laws.tx_scrollback_append_only(pre, post, w):
  Screen.ps.tx_scrollback_append_only(pre, post, w)

def Laws.tx_resize_keeps(t, w):
  Screen.ps.tx_resize_keeps(t, w)

def Laws.tx_flush_settles(t):
  Screen.ps.tx_flush_settles(t)

def Laws.pace_never_ahead(es, min, k):
  Screen.ps.pace_never_ahead(es, min, k)

def Laws.pace_never_back(min, k, p, e):
  Screen.ps.pace_never_back(min, k, p, e)

def Laws.pace_drains(min, k, p, n, one, behind, enough):
  Screen.ps.pace_drains(min, k, p, n, one, behind, enough)

def Laws.verify_only_checked(f, g, ok1, ok2):
  Screen.ps.verify_only_checked(f, g, ok1, ok2)

def Laws.layout_inside(hs, y, rows):
  Screen.ps.layout_inside(hs, y, rows)

def Laws.layout_apart(hs, y, rows):
  Screen.ps.layout_apart(hs, y, rows)

def Laws.layout_whole_when_room(hs, y, rows, fits):
  Screen.ps.layout_whole_when_room(hs, y, rows, fits)

# (S9) Local tiny models

def Laws.tiny_pick_in_chain(chain, up, m, used):
  Tiny.pn.tiny_pick_in_chain(chain, up, m, used)

def Laws.tiny_pick_first(pre, m, post, up, before, here):
  Tiny.pn.tiny_pick_first(pre, m, post, up, before, here)

def Laws.tiny_pick_unavailable(chain, up, none):
  Tiny.pn.tiny_pick_unavailable(chain, up, none)

def Laws.tiny_every_need_served(es, w):
  Tiny.pn.tiny_every_need_served(es, w)

def Laws.tiny_worker_current(es):
  Tiny.pn.tiny_worker_current(es)

def Laws.tiny_same_tag_joins(o, t, p):
  Tiny.pn.tiny_same_tag_joins(o, t, p)

# (S10) Reasoning depth

def Laws.effort_offered_plain(map):
  Effort.pe.effort_offered_plain(map)

def Laws.effort_offered_null(map, l, null):
  Effort.pe.effort_offered_null(map, l, null)

def Laws.effort_offered_ext(r, map, l, x, in):
  Effort.pe.effort_offered_ext(r, map, l, x, in)

def Laws.effort_offered_kept(map, l, k):
  Effort.pe.effort_offered_kept(map, l, k)

def Laws.effort_offered_asc(m):
  Effort.pe.effort_offered_asc(m)

def Laws.effort_clamp_offered(m, l, ne):
  Effort.pe.effort_clamp_offered(m, l, ne)

def Laws.effort_clamp_keeps(m, l, in):
  Effort.pe.effort_clamp_keeps(m, l, in)

def Laws.effort_clamp_idem(m, l):
  Effort.pe.effort_clamp_idem(m, l)

def Laws.effort_cycle_still(m, l, d, few):
  Effort.pe.effort_cycle_still(m, l, d, few)

def Laws.effort_cycle_next(m, pre, a, b, post, split):
  Effort.pe.effort_cycle_next(m, pre, a, b, post, split)

def Laws.effort_cycle_wrap(m, h, pre, z, split):
  Effort.pe.effort_cycle_wrap(m, h, pre, z, split)

def Laws.effort_cycle_prev(m, pre, a, b, post, split):
  Effort.pe.effort_cycle_prev(m, pre, a, b, post, split)

def Laws.effort_cycle_wrap_back(m, h, pre, z, split):
  Effort.pe.effort_cycle_wrap_back(m, h, pre, z, split)

def Laws.effort_cycle_inverse(m, l, in):
  Effort.pe.effort_cycle_inverse(m, l, in)

def Laws.effort_cycle_inverse_back(m, l, in):
  Effort.pe.effort_cycle_inverse_back(m, l, in)

def Laws.effort_unset_default(mo):
  Effort.pe.effort_unset_default(mo)

def Laws.effort_settle_offered(m, st, dflt, k, ne, settled):
  Effort.pe.effort_settle_offered(m, st, dflt, k, ne, settled)

def Laws.effort_stored_is_sent(s, dflt, acts):
  Effort.pe.effort_stored_is_sent(s, dflt, acts)

def Laws.effort_shown_is_sent(s, dflt, acts):
  Effort.pe.effort_shown_is_sent(s, dflt, acts)

# (R1) Release versions

def Release.semver_roundtrip(v):
  Semver.ps.roundtrip(v)

def Release.semver_le_refl(v):
  Semver.ps.le_refl(v)

def Release.semver_le_antisym(u, v, uv, vu):
  Semver.ps.le_anti(u, v, uv, vu)

def Release.semver_le_trans(u, v, w, uv, vw):
  Semver.ps.le_trans(u, v, w, uv, vw)

def Release.semver_le_total(u, v):
  Semver.ps.le_total(u, v)

def Release.semver_next_newer(s, xs, t, ys, v, parsed, ins):
  Semver.ps.next_newer(s, xs, t, ys, v, parsed, ins)

def Release.semver_next_not_tagged(s, xs, t, ys, v, parsed):
  Semver.ps.next_ne(s, xs, t, ys, v, parsed)

def Release.semver_next_tag_new(s, xs, t, ys):
  Semver.ps.tag_new(s, xs, t, ys)

def Release.semver_fresh_series(a, b, c, tags, none):
  Semver.ps.fresh(a, b, c, tags, none)

def Release.semver_other_series(s, xs, t, ys, other):
  Semver.ps.other(s, xs, t, ys, other)

def Release.semver_title(v):
  {==}

def Release.semver_tag_roundtrip(v):
  Semver.ps.roundtrip(v)

def Release.semver_release_newest(c, xs, t, ys, r, rel, v, parsed):
  Semver.ps.release_newest_of(c, xs, t, ys, r, rel, v, parsed)

def Release.semver_release_progress(c, a, b, tags, parsed, only):
  Semver.ps.progress(c, a, b, tags, parsed, only)

# (A1) One refresh flight per provider

def AuthFlight.flight_one_fetch(evs):
  AuthFlights.pf.flight_one_fetch(evs)

def AuthFlight.flight_board_joins(evs, j, lj, f, leads, flight, k, ok, boards):
  AuthFlights.pf.flight_board_joins(evs, j, lj, f, leads, flight, k, ok, boards)

def AuthFlight.flight_callers_get_its_outcome(evs, k, f, o, served):
  AuthFlights.pf.flight_callers_get_its_outcome(evs, k, f, o, served)

def AuthFlight.flight_landed_serves(s, k, f, o, ok, waits, landed):
  AuthFlights.pf.flight_landed_serves(s, k, f, o, ok, waits, landed)

def AuthFlight.flight_after_end_stored(evs, k, f, c, lands, ok):
  AuthFlights.pf.flight_after_end_stored(evs, k, f, c, lands, ok)

def AuthFlight.flight_after_end_served(evs, k, f, c, lands, ok, ok2, fresh):
  AuthFlights.pf.flight_after_end_served(evs, k, f, c, lands, ok, ok2, fresh)

# (T1) Themes

def Themes.theme_resolve_empty(src):
  ThemeProofs.theme_resolve_empty(src)

def Themes.theme_resolve_first(pre, nm, id, post, n, ne, miss, same):
  ThemeProofs.theme_resolve_first(pre, nm, id, post, n, ne, miss, same)

def Themes.theme_resolve_missing(src, n, ne, miss):
  ThemeProofs.theme_resolve_missing(src, n, ne, miss)

def Themes.theme_load_valid(r, f, loaded):
  ThemeProofs.theme_load_valid(r, f, loaded)

def Themes.theme_tokens_complete(f, v):
  ThemeProofs.theme_tokens_complete(f, v)

def Themes.theme_mode_background(f, g, same):
  ThemeProofs.theme_mode_background(f, g, same)

def Themes.theme_palette_name_free(f, n):
  ThemeProofs.theme_palette_name_free(f, n)

def Themes.theme_mode_name_free(f, n):
  ThemeProofs.theme_mode_name_free(f, n)

def Themes.theme_shipped_legible(s):
  ThemeProofs.theme_shipped_legible(s)

def Themes.theme_shipped_status_distinct(s):
  ThemeProofs.theme_shipped_status_distinct(s)

# (T2) Dashboard tokens

def DashTokens.tokens_paired(t, m):
  Tokens.tokens_paired(t, m)

def DashTokens.tokens_legible(m, pre, p, post, split):
  Tokens.tokens_legible(m, pre, p, post, split)

def DashTokens.tokens_layers_ordered():
  Tokens.tokens_layers_ordered()

def DashTokens.tokens_space_ascends():
  Tokens.tokens_space_ascends()

def DashTokens.tokens_type_ascends():
  Tokens.tokens_type_ascends()

# (H6, H7, M5, L5) Progress is new work; what the harness changes or drops is reported

def Prg.child_repeat_is_no_work(seen, loop, within):
  Progress.pp.repeat(seen, loop, within)

def Prg.child_loop_is_a_stall(cfg, w, hist, p, ps, loops, tok, long):
  Progress.pp.loop_stalls(cfg, w, hist, p, ps, loops, tok, long)

def Prg.child_new_work_is_progress(cfg, w, e, seen, seg, x, fresh, news, tok):
  Progress.pp.new_work_moves(cfg, w, e, seen, seg, x, fresh, news, tok)

def Prg.goal_stops_without_progress(cap, s, hist, seg, segs, repeats, long):
  Progress.pp.goal_stops(cap, s, hist, seg, segs, repeats, long)

def Prg.goal_progress_continues(cap, s, hist, seg, x, fresh, news):
  Progress.pp.grew_yes(cap, s, hist, seg, x, fresh, news)

def Prg.fallback_is_reported(ps, k, h):
  Reports.ppr.fallback_is_reported(ps, k, h)

def Prg.fallback_quiet_when_routed(ps, k, h):
  Reports.ppr.fallback_quiet_when_routed(ps, k, h)

def Prg.fallback_quiet_when_unset(p, ok, look, need):
  Reports.ppr.fallback_quiet_when_unset(p, ok, look, need)

def Prg.fallback_quiet_when_same(p, ok, look, need):
  Reports.ppr.fallback_quiet_when_same(p, ok, look, need)

def Prg.skill_failure_reported(cs, c, i):
  Reports.ppr.skill_failure_reported(cs, c, i)

def Prg.skill_loaded_not_failed(cs, n, d):
  Reports.ppr.skill_loaded_not_failed(cs, n, d)

def Ladder.quirk_ladder_explicit_first(e, rule):
  Quirks.pq.quirk_ladder_explicit_first(e, rule)

def Ladder.quirk_ladder_rule_second(l):
  Quirks.pq.quirk_ladder_rule_second(l)

def Ladder.quirk_ladder_default_last():
  Quirks.pq.quirk_ladder_default_last()

def Ladder.quirk_ladder_offered_exact(explicit, rule, d, l):
  Quirks.pq.quirk_ladder_offered_exact(explicit, rule, d, l)

def Ladder.quirk_ladder_plain_exact(explicit, rule, d, l):
  Quirks.pq.quirk_ladder_plain_exact(explicit, rule, d, l)

def Ladder.quirk_ladder_shipped_is_s10(r, map):
  Quirks.pq.quirk_ladder_shipped_is_s10(r, map)

# (K1) The kernel environment is local

def KernelLocal.kernel_session_never_downloads(f):
  KernelLocals.pk.session_never_downloads(f)

def KernelLocal.kernel_download_only_on_install(f, s, fetches):
  KernelLocals.pk.download_only_on_install(f, s, fetches)

def KernelLocal.kernel_fetch_verified_before_use(f, s):
  KernelLocals.pk.fetch_verified_before_use(f, s)

def KernelLocal.kernel_setup_runs(f, s):
  KernelLocals.pk.setup_runs(f, s)

def KernelLocal.kernel_install_fetches():
  {==}

def KernelLocal.kernel_missing_spares_tools(n, f, ok):
  KernelLocals.pk.missing_spares_tools(n, f, ok)

def KernelLocal.kernel_missing_names_install(f, failed):
  KernelLocals.pk.missing_names_install(f, failed)

def KernelLocal.kernel_lock_attempt_leaves_none(l):
  KernelLocals.pk.attempt_leaves_none(l)

def KernelLocal.kernel_lock_sweep_removes_dead(ls):
  KernelLocals.pk.sweep_removes_dead(ls)

def KernelLocal.kernel_lock_sweep_keeps_live(ls):
  KernelLocals.pk.sweep_keeps_live(ls)

# (D2) Storage and cron

def Storage.log_reads_lines(ls, t):
  Logs.pl.reads_lines(ls, t)

def Storage.log_ack_durable(d, e):
  Logs.pl.ack(d, e)

def Storage.log_only_commits(d, e):
  Logs.pl.only(d, e)

def Storage.publish_never_overwrites(s, t, es, taken):
  Stagings.pg.publish_taken(s, t, es, taken)

def Storage.publish_moves(s, t, es, free):
  Stagings.pg.publish_free(s, t, es, free)

def Storage.sweep_never_live(pre, i, k, s, o, post):
  Stagings.pg.sweep_never_live(pre, i, k, s, o, post)

def Storage.sweep_never_young(pre, i, k, h, o, post):
  Stagings.pg.sweep_never_young(pre, i, k, h, o, post)

def Storage.sweep_stays_out(pre, i, k, h, s, post):
  Stagings.pg.sweep_stays_out(pre, i, k, h, s, post)

def Storage.sweep_reaches_every_depth(pre, i, k, post, sw):
  Stagings.pg.sweep_reaches(pre, i, k, post, sw)

def Storage.list_one_location(es, n):
  Stagings.pg.one_location(es, n)

def Storage.list_import_lists_storage(es, s):
  Stagings.pg.import_lists(es, s)

def Storage.list_import_keeps_others(es, s, n, ne):
  Stagings.pg.import_keeps(es, s, n, ne)

# (H4) Every run ends

def Laws.run_ends(cfg, evs, long, more):
  Runs.run_ends(cfg, evs, long, more)

def Laws.run_end_stays(cfg, s, ended, e):
  Runs.end_stays(cfg, s, e, ended)

def Laws.run_abort_ends_now(cfg, s, live):
  Runs.abort_now(cfg, s, live)

def Laws.run_rounds_capped(cfg, evs):
  Runs.rounds_capped(cfg, evs)

def Laws.run_rounds_fail_at_cap(cfg, evs):
  Runs.rounds_fail_at_cap(cfg, evs)

def Laws.run_polls_need_defers(cfg, evs):
  Runs.polls_need_defers(cfg, evs)

def Laws.run_no_answer_is_an_error(cfg, r, c, a, n, p):
  Runs.no_answer(cfg, r, c, a, n, p)

def Laws.run_calls_never_answer(cfg, text, r, c, a, n, p):
  Runs.calls_never_answer(cfg, text, r, c, a, n, p)

def Laws.run_note_spends_no_retry(cfg, retryable, r, c, a, m, p):
  Runs.note_spends_no_retry(cfg, retryable, r, c, a, m, p)

def Laws.run_retry_spends_no_note(cfg, r, c, b, n, p):
  Runs.retry_spends_no_note(cfg, r, c, b, n, p)

# (H4.7) A retry never resends a request it cut

def Laws.run_retry_sends_a_new_request(cfg, evs):
  Retries.retry_sends_a_new_request(cfg, evs)

def Laws.run_cut_names_the_request(retryable, fin, got, pa, ctx, n, note, log):
  Retries.cut_names_the_request(retryable, fin, got, pa, ctx, n, note, log)

def Laws.run_note_is_never_logged(q):
  Retries.note_is_never_logged(q)

# (H4.8) A stuck model gets a recovery, each with a cap

def Rec.rec_length_retries_with_a_note(rc, k, row, same, last, under):
  Recover.length_retries_with_a_note(rc, k, row, same, last, under)

def Rec.rec_length_gives_up(rc, k, row, same, last, over):
  Recover.length_gives_up(rc, k, row, same, last, over)

def Rec.rec_leak_rebuilt_is_calls(rc, h, kept, r):
  Recover.leak_rebuilt_is_calls(rc, h, kept, r)

def Rec.rec_leak_retries_with_a_note(rc, h, kept, k, row, same, last, under):
  Recover.leak_retries_with_a_note(rc, h, kept, k, row, same, last, under)

def Rec.rec_leak_stands(rc, h, kept, k, row, same, last, over):
  Recover.leak_stands(rc, h, kept, k, row, same, last, over)

def Rec.rec_calls_run(rc, h, kept, k, row, same, last, fresh):
  Recover.calls_run(rc, h, kept, k, row, same, last, fresh)

def Rec.rec_repeat_never_runs(rc, h, kept, k, row, same, last, rep):
  Recover.repeat_never_runs(rc, h, kept, k, row, same, last, rep)

def Rec.rec_repeat_redirects(rc, h, kept, k, row, same, last, rep, under):
  Recover.repeat_redirects(rc, h, kept, k, row, same, last, rep, under)

def Rec.rec_repeat_gives_up(rc, h, kept, k, row, same, last, rep, over):
  Recover.repeat_gives_up(rc, h, kept, k, row, same, last, rep, over)

def Rec.rec_user_breaks_the_row(rc, k, row, same, last):
  Recover.user_breaks_the_row(rc, k, row, same, last)

def Rec.rec_notes_capped(rc, os):
  Recover.notes_capped(rc, os)

def Rec.rec_never_runs_a_repeat(rc, os):
  Recover.never_runs_a_repeat(rc, os)

def Rec.rec_stuck_gets_help(rc, o, r):
  Recover.stuck_gets_help(rc, o, r)

def Rec.rec_redo_is_noted(pass):
  Recover.redo_is_noted(pass)

def Rec.rec_quit_fails(cfg, pass, r, c, a, n, p):
  Recover.quit_fails(cfg, pass, r, c, a, n, p)

# (C1) The catalog union

def CatalogUnion.union_hides_nothing(bs, cs, k):
  CatalogUnions.pcu.hides_nothing(bs, cs, k)

def CatalogUnion.union_lists_each_model_once(bs, cs, k, ub, uc):
  CatalogUnions.pcu.lists_once(bs, cs, k, ub, uc)

def CatalogUnion.union_bundled_only(bs, cs, k, b, hb, hc):
  CatalogUnions.pcu.bundled_only(bs, cs, k, b, hb, hc)

def CatalogUnion.union_compiled_only(bs, cs, k, c, hb, hc):
  CatalogUnions.pcu.compiled_only(bs, cs, k, c, hb, hc)

def CatalogUnion.union_both_keeps_bundled(bs, cs, k, b, c, v, hb, hc, hv):
  CatalogUnions.pcu.both_keeps_bundled(bs, cs, k, b, c, v, hb, hc, hv)

def CatalogUnion.union_both_fills_from_compiled(bs, cs, k, b, c, hb, hc, hn, ha):
  CatalogUnions.pcu.both_fills(bs, cs, k, b, c, hb, hc, hn, ha)

def CatalogUnion.union_both_other_api(bs, cs, k, b, c, hb, hc, hn, ha):
  CatalogUnions.pcu.both_other_api(bs, cs, k, b, c, hb, hc, hn, ha)

def CatalogUnion.union_order_free(k, xs, xs2, ys, ys2, sx, sy):
  CatalogUnions.pcu.order_free(k, xs, xs2, ys, ys2, sx, sy)

# Cron

def Cronl.cron_fires_once(evs):
  Crons.pc.cron_fires_once(evs)

def Cronl.cron_once_finished_after_end(evs):
  Crons.pc.cron_once_finished_after_end(evs)

def Cronl.cron_never_drops(s, e, t, i):
  Crons.pc.cron_never_drops(s, e, t, i)

def Cronl.cron_claim_owned(s, e, i, x, o):
  Crons.pc.cron_claim_owned(s, e, i, x, o)

def Cronl.cron_backoff_bounded(evs, s, e, i, k, c, nx):
  Crons.pc.cron_backoff_bounded(evs, s, e, i, k, c, nx)

# (D1) Supervisor

def Sup.restart_gives_up(c, pre, g, gs, many, fast):
  Supervision.ps.restart_gives_up(c, pre, g, gs, many, fast)

def Sup.timeouts_ordered(t):
  Supervision.ps.timeouts_ordered(t)

def Sup.revive_after_refresh(h, pos, b, c, d, soon):
  Supervision.ps.revive_after_refresh(h, pos, b, c, d, soon)

def Sup.orphan_never_aborts_resumable(window, evs):
  Supervision.ps.orphan_never_aborts_resumable(window, evs)

def Sup.idle_shutdown_never_aborts(bs, ops):
  Supervision.ps.idle_shutdown_never_aborts(bs, ops)

def Sup.adopt_same_build(sup, w, adopted):
  Supervision.ps.adopt_same_build(sup, w, adopted)

def Sup.replace_never_downgrades(ss):
  Replacing.pr.replace_never_downgrades(ss)

def Sup.replacement_terminates(bs, ss, cover):
  Replacing.pr.replacement_terminates(bs, ss, cover)

def Sup.background_never_replaces(c, d):
  Replacing.pr.background_never_replaces(c, d)

def Sup.notice_shown_once(evs):
  Notices.pn.notice_shown_once(evs)

def Sup.notice_per_restore(evs):
  Notices.pn.notice_per_restore(evs)

# (G) The Signal gateway's tables

def GatewayWidth.table_aligned(pre, row, post):
  GatewayWidths.table_aligned(pre, row, post)

def GatewayWidth.ascii_unchanged(rows, ones):
  GatewayWidths.ascii_unchanged(rows, ones)

# (T3) Terminal colors

def TuiColor.tui_effort_ramp_length(lo, hi, n):
  TuiColors.tui_effort_ramp_length(lo, hi, n)

def TuiColor.tui_effort_ramp_ordered(lo, hi, n):
  TuiColors.tui_effort_ramp_ordered(lo, hi, n)

def TuiColor.tui_effort_ramp_distinct(lo, hi, n, fits):
  TuiColors.tui_effort_ramp_distinct(lo, hi, n, fits)

def TuiColor.tui_effort_shipped_distinct(s, n, fits):
  TuiColors.tui_effort_shipped_distinct(s, n, fits)

def TuiColor.tui_usage_bands_ascend():
  TuiColors.tui_usage_bands_ascend()

def TuiColor.tui_usage_band_monotone(t, e, w):
  TuiColors.tui_usage_band_monotone(t, e, w)

def TuiColor.tui_usage_band_fraction(k, t, w):
  TuiColors.tui_usage_band_fraction(k, t, w)

def TuiColor.tui_roles_resolve(f, v):
  TuiColors.tui_roles_resolve(f, v)

def TuiColor.tui_roles_shipped(s):
  TuiColors.tui_roles_shipped(s)

# File modes, the socket dir and the working dir

def Fm.socket_dir_owned(d, used):
  FileModes.owned(d, used)

def Fm.socket_dir_progress(d, safe):
  FileModes.progress(d, safe)

def Fm.socket_dir_created(mine, loose):
  FileModes.created(mine, loose)

def Fm.socket_dir_created_used():
  FileModes.created_used()

def Fm.peer_same_uid(p, own, ok):
  FileModes.peer_same(p, own, ok)

def Fm.peer_own_accepted(own):
  FileModes.peer_own(own)

def Fm.private_on_create(k):
  FileModes.private(k)

def Fm.cwd_is_explicit(c, p, ok):
  FileModes.explicit(c, p, ok)

def Fm.cwd_none_refused():
  {==}

def Fm.cwd_gone_refused(p):
  {==}

def Fm.cwd_file_refused(p):
  {==}

def Fm.cwd_dir_opens(p):
  {==}

# (G1) Path policy

def Pg.path_real_has_no_link(ls, segs):
  PathPolicy.pp.path_real_has_no_link(ls, segs)

def Pg.path_secret_wins(pol, ls, segs, hit):
  PathPolicy.pp.path_secret_wins(pol, ls, segs, hit)

def Pg.path_inside_is_safe(pol, ls, segs, inside):
  PathPolicy.pp.path_inside_is_safe(pol, ls, segs, inside)

def Pg.path_ancestor_guarded(pol, ls, segs, anc):
  PathPolicy.pp.path_ancestor_guarded(pol, ls, segs, anc)

def Pg.gate_write_auto_only_inside(c, auto, ans, ran, no):
  PathPolicy.pp.gate_write_auto_only_inside(c, auto, ans, ran, no)

def Pg.gate_secret_read_needs_yes(c, a, auto, ans, s, ran):
  PathPolicy.pp.gate_secret_read_needs_yes(c, a, auto, ans, s, ran)

def Pg.gate_yes_runs(c, a, auto):
  PathPolicy.pp.gate_yes_runs(c, a, auto)

def Pg.gate_inside_write_runs(auto, ans, w):
  PathPolicy.pp.gate_inside_write_runs(auto, ans, w)

def Pg.config_needs_yes(es, pol, ls, auto, cs, no):
  PathPolicy.pp.config_needs_yes(es, pol, ls, auto, cs, no)
