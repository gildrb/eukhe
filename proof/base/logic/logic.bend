# eukhe: lemmas the proofs of two or more areas share: logic/logic

import Base
import ../../../bend/fsmode.bend as Fs
import ../../../bend/path_policy.bend as Pp
import ../../../bend/retry.bend as R

# ---- wire nat (wn_): Bool kit (copied from the skill's examples/sort/proof/kit.bend) ----

def wn_Clash(b: Bool, G: Type) -> Type:
  match b:
    case False{}:
      Unit
    case True{}:
      G

def wn_absurd(-G: Type, e: {False{} == True{} : Bool}) -> G:
  %e : wn_Clash(_, G)
  Unit{}

# ---- wire: rest ----

# ---- wire (Bool, String, List, replies) ----

# Kit (copied from the bend skill, examples/sort/proof/u32_order.bend)
# ---

# a motive that is the goal G at True and trivial at False
def wr_clash(b: Bool, G: Type) -> Type:
  match b:
    case False{}:
      Unit
    case True{}:
      G

# False == True proves anything
def wr_absurd(-G: Type, e: {False{} == True{} : Bool}) -> G:
  %e : wr_clash(_, G)
  Unit{}

# Logic
# -----

# G when b is True, Unit when False
def cb_If(b: Bool, G: Type) -> Type:
  match b:
    case True{}:
      G
    case False{}:
      Unit

# False is not True: anything follows
def cb_absurd(-G: Type, e: {False{} == True{} : Bool}) -> G:
  %e : cb_If(_, G)
  Unit{}

# ---- fit ----

# proof_fit: the laws of a fit, of the summaries along a history, and of
# a compaction's view (LAWS.bend (e), (g)). A fit's merge is sound: best
# picks the first line of a mergeable pair (Has), so each merge drops a
# line and records a built parent; and complete: best finds none only
# when no pair can merge. Summarized survives every step: Info.set only
# adds built nodes, a merge inserts a built parent, a message a leaf.

# Logic
# -----

# a type picked by a Bool: a rewrite through it refutes True == False
def fit.pf.BD(b: Bool, t: Type, f: Type) -> Type:
  match b:
    case True{}:
      t
    case False{}:
      f

def pf.absurd_tf(-A: Type, e: {True{} == False{} : Bool}) -> A:
  %e : fit.pf.BD(_, Unit, A)
  Unit{}

def pf.absurd_ft(-A: Type, e: {False{} == True{} : Bool}) -> A:
  %e : fit.pf.BD(_, A, Unit)
  Unit{}

# ---- compactor ----

# proof_compactor: the laws of a compactor call (H1) and of the wait for
# a settled view (H2), for bend/compactor.bend and the need-first queue of
# bend/optchat.bend. Every proof is by induction: on the tries of a line,
# on the outcomes of the settle, on the view of the queue.

# Logic
# -----

def compactor.pc.BD(b: Bool, t: Type, f: Type) -> Type:
  match b:
    case True{}:
      t
    case False{}:
      f

def pc.absurd_ft(-A: Type, e: {False{} == True{} : Bool}) -> A:
  %e : compactor.pc.BD(_, A, Unit)
  Unit{}

def pc.absurd_tf(-A: Type, e: {True{} == False{} : Bool}) -> A:
  %e : compactor.pc.BD(_, Unit, A)
  Unit{}

# ---- child ----

# proof_child: the H5 laws of LAWS.bend (bend/child.bend, the life of one
# subagent).
#
# - The watch: a quiet poll takes 1 ms or more off the clock (`left`) and
#   a failed one a try (`tries`), so a run of them as long as the clock
#   ends the watch (`stalls_in_time`, `unreachable_in_time`); a clock
#   never grows past its full size (`clock_bounded`); progress sets it
#   back to full (`progress_is_not_a_stall`).
# - The report: an invariant `K` holds after any events: every submission
#   in the parent's inbox but the newest is withdrawn, under an id below
#   it (`Kin`), and the task owes the newest id, or the next one once the
#   newest is withdrawn (`Kowe`). Only the newest may be live, which gives
#   `one_live` and `report_once`; a delivery or withdrawal touches only the
#   newest. From any state that owes the report, a reopen and two task
#   steps (three when an abort mark is pending) leave the report queued
#   under the owed id or placed (`ready`), and a delivery of that id
#   places it (`delivered_once`). A potential (1 plus the withdrawn
#   submissions) bounds the inbox and grows only at a withdrawal
#   (`resubmits_per_abort`).

# Logic
# -----

def child.pc.BD(b: Bool, t: Type, f: Type) -> Type:
  match b:
    case True{}:
      t
    case False{}:
      f

def child.pc.absurd(-A: Type, e: {False{} == True{} : Bool}) -> A:
  %e : child.pc.BD(_, A, Unit)
  Unit{}

# ---- run ----

# proof_run: the H4 laws of LAWS.bend about bend/run.bend.
#
# - run_ends: an explicit measure M (the inputs a run may still take) falls
#   by at least one at every input to a live run: lexicographically, the
#   rounds left, then the compactions, and the retries and notes left in
#   the generation (one budget u = a + n: each retry, noted or not, spends
#   one of them), the polls left, then the phase (prepare > call >
#   compact; tools ends the generation). M is that order written as one
#   number, in mixed radix, and M at the start is bound(cfg).
# - end_stays, abort_ends_now: by computation on each phase.
# - rounds_capped, rounds_fail_at_cap: invariants of every run and its
#   counted rounds, by induction on its inputs.
# - polls_need_defers: an invariant of the run and its deferred replies in
#   a row, by induction on its inputs.
# - no_answer, calls_never_answer, note_spends_no_retry,
#   retry_spends_no_note: by computation: Ended.reply makes a message with
#   a tool call Calls, whatever its text, and one with no text and no call
#   a noted Error; a noted Error spends a note, any other a retry.

# Logic
# -----

def BD(b: Bool, t: Type, f: Type) -> Type:
  match b:
    case True{}:
      t
    case False{}:
      f

def absurd(-A: Type, e: {False{} == True{} : Bool}) -> A:
  %e : BD(_, A, Unit)
  Unit{}

# ---- tree ----

# proof_tree: the session tree laws of LAWS.bend (S1), about bend/tree.bend.
#
# Lookups first: a set or an unset changes only the lookup of its own key
# (`pt.get_set_*`, `pt.get_unset_*`), and both keep a tree sorted. A put
# keeps every parent (`pt.ok_set`); a delete keeps the parent of every
# node it keeps (`pt.rooted_prune_go`, by the nodes walked so far: kept,
# or with their key gone). So every record keeps a tree sound
# (`apply_sound`). A rewind's lookup at a key follows its ops on that key
# (`pt.look`); so after diff(a, b) the tree agrees with b on every key,
# and two sorted trees that agree are equal (`pt.ext`). A delete of the
# root (key 0) changes nothing, and no node of a rooted tree is the root
# (`pt.rooted_nz`); a delete of a node removes it and its subtree only.

# Logic
# -----

def tree.pt.BD(b: Bool, t: Type, f: Type) -> Type:
  match b:
    case True{}:
      t
    case False{}:
      f

def pt.absurd(-A: Type, e: {True{} == False{} : Bool}) -> A:
  %e : tree.pt.BD(_, Unit, A)
  Unit{}

def tree.pt.absurdF(-A: Type, e: {False{} == True{} : Bool}) -> A:
  %e : tree.pt.BD(_, A, Unit)
  Unit{}

# ---- job ----

# proof_job: the S2 laws of the job model in
# bend/job.bend: output caps and drops, one end per job, ended jobs stay
# ended, a blocking call never outlives its budget, a tool call's stream
# journals one final record carrying everything, and a rewind stops
# exactly the orphan jobs. Each job lemma speaks of a job at any state,
# by induction on the events it sees.

# Logic
# -----

def pj.BD(b: Bool, t: Type, f: Type) -> Type:
  match b:
    case True{}:
      t
    case False{}:
      f

def pj.absurdF(-A: Type, e: {False{} == True{} : Bool}) -> A:
  %e : pj.BD(_, A, Unit)
  Unit{}

# ---- cvar ----

# proof_cvar: the S4 laws of the cvar model in
# bend/cvar.bend.
#
# A layer of sets is read one set at a time (`pv.layer_cons`), so a set
# appended last acts on the value of the sets before it
# (`pv.layer_snoc`): a hit gives its value, a miss keeps the value.
# The registry adds a declaration only when its id is free and its
# default is well typed, which keeps it unique and typed; a hit is a
# valid set of the found declaration, so every layer keeps the type of
# the default. A set of a Global cvar never hits in an agent layer. The
# cfg an agent writes drops only sets that miss its persisted cvar. A
# toggle's set of x hits or misses the same way whatever its Bool, so
# a second toggle undoes the first. Expansion leaves only plain
# commands, and its depth bound turns a self-running alias into a
# cycle.

# Logic
# -----

def cvar.pv.BD(b: Bool, t: Type, f: Type) -> Type:
  match b:
    case True{}:
      t
    case False{}:
      f

def cvar.pv.absurd(-A: Type, e: {True{} == False{} : Bool}) -> A:
  %e : cvar.pv.BD(_, Unit, A)
  Unit{}

# ---- infer ----

# proof_infer: the inference layer laws of S6 (forced calls, the strict
# schema budget, the repetition guard, early compaction), about
# bend/infer.bend.
#
# A forced call: by induction on the replies and the retries; a retry's
# tries all carry the provider's support (`pi.flags_sup`). The budget:
# a take and its drop split every count (`pi.count_split`), ranking keeps
# every count (`pi.count_rank`) and sorts by priority (`pi.sorted_rank`),
# and a sorted list's take dominates its drop (`pi.dom_split`). The guard:
# the counter of period p is at least m exactly when the first m chunks
# each equal the chunk p before them (`pi.each_cycle`), so the guard fires
# exactly at a periodic window (`pi.fires_periodic`, `pi.cut_go`,
# `pi.keep_go`), and k equal chunks in a row end in one (`pi.run_loops`,
# `pi.rep_go`). Compaction:
# while below the threshold the next size stays within the limit
# (`pi.compact_go`).

# Logic
# -----

def pi.BD(b: Bool, t: Type, f: Type) -> Type:
  match b:
    case True{}:
      t
    case False{}:
      f

def pi.absurdF(-A: Type, e: {False{} == True{} : Bool}) -> A:
  %e : pi.BD(_, A, Unit)
  Unit{}

# ---- quirks ----

# proof_quirks: the quirks rulebook laws of S6, about bend/infer.bend.
#
# Compile: an unknown directive fails known_all (`pq.ka_app`); a clash
# makes the rulebook ambiguous (`pq.amb_app`); a swap of two neighbours
# changes neither known_all (`pq.ka_swap`) nor ambiguous (`pq.amb_swap`,
# clash is symmetric).
# Lookup: with no rule that applies the scan keeps None (`pq.none_go`);
# once a rule applies the best stays Some (`pq.stay_k`). Two rules that
# both apply and do not clash give the same best in either order
# (`pq.better_swap`: at one rank they agree on the value). In a rulebook
# that compiles, before r the best is below r's rank or equal to r
# (`pq.pre_ok`), and from r on it is r's rank and value (`pq.good`).
# The thinking ladder: the chosen ladder is a plain case split
# (reflexivity). A level is in the offer of a map exactly when the map
# keeps it (`pq.lad_has_keep`, from the S10 filter lemmas), and the filled
# map keeps a level exactly when the ladder rule does (`pq.lad_fill_keep`).
# With the shipped default ladders the ladder rule keeps what the S10
# rule keeps (`pq.lad_ship_e`), so the offers agree (`pq.lad_offer_fill`,
# by induction on the list).

# Logic
# -----

def pq.BD(b: Bool, t: Type, f: Type) -> Type:
  match b:
    case True{}:
      t
    case False{}:
      f

def pq.absurd(-A: Type, e: {True{} == False{} : Bool}) -> A:
  %e : pq.BD(_, Unit, A)
  Unit{}

def pq.absurdF(-A: Type, e: {False{} == True{} : Bool}) -> A:
  %e : pq.BD(_, A, Unit)
  Unit{}

# ---- tools ----

# proof_tools: the S7 laws of the tool surface model in
# bend/tools.bend. An event never touches the roster, and a turn sends
# the session's roster (`pl.sent_go`, by induction on the events). A join
# puts the tool in front of `dyn`; a quit drops every copy (`pl.drop_go`, with the head
# test as a parameter). `build` adds the intent parameter only when it is
# missing, and lifts the version to at least 1. A walk keeps its depth
# equal to the names it holds (`pl.esc`, `pl.ins`). The gate lemmas speak
# of `exec.go` at any head test: what ran is a prefix, a gated step that
# ran used one approval, a denial stops at the denied step, and a script
# that finished ran every step.

# Logic
# -----

def tools.pl.BD(b: Bool, t: Type, f: Type) -> Type:
  match b:
    case True{}:
      t
    case False{}:
      f

def tools.pl.absurdF(-A: Type, e: {False{} == True{} : Bool}) -> A:
  %e : tools.pl.BD(_, A, Unit)
  Unit{}

# ---- screen ----

# proof_screen: the S8 laws of the interface model in
# bend/screen.bend: the scrollback has no gap and only grows, a resize and
# a flush keep it in order, the pacer never runs ahead nor back and drains
# a backlog, only checked frames reach the terminal, and a vertical stack
# keeps its children inside the viewport, apart, and whole when they fit.

# Logic
# -----

def screen.ps.BD(b: Bool, t: Type, f: Type) -> Type:
  match b:
    case True{}:
      t
    case False{}:
      f

def screen.ps.absurdF(-A: Type, e: {False{} == True{} : Bool}) -> A:
  %e : screen.ps.BD(_, A, Unit)
  Unit{}

# ---- semver ----

# proof_semver: the R1 laws (LAWS.bend section release, release versions) of the
# model in bend/semver.bend.
#
# Numbers: incrementing the digits adds one to their value, so the digits
# Num.dec writes for n have the value n; Num.read takes them back, as they
# are the digits of their own value. Num.str writes digits that Sym.of
# reads back as those digits, so reading Ver.show(v) gives back the three
# fields of v. The order compares major, then minor, then patch: each
# level is reflexive, transitive, total and antisymmetric when the level
# below it is. The next release takes 1 + a patch at least as high as the
# patch of each tag of the series, under the same major and minor, so it
# is newer than each; a tag of another series never names it, and adds no
# patch to the highest one. A release passed its guard: it is newer than
# every version tag; with only tags of the series, the guard passes.
#
# A recursive proof takes the value it inspects as a parameter (Bend
# matches only parameters), with an equation that names it.

# Logic
# -----

def semver.ps.BD(b: Bool, t: Type, f: Type) -> Type:
  match b:
    case True{}:
      t
    case False{}:
      f

def semver.ps.absurd(-A: Type, e: {True{} == False{} : Bool}) -> A:
  %e : semver.ps.BD(_, Unit, A)
  Unit{}

def semver.ps.absurdF(-A: Type, e: {False{} == True{} : Bool}) -> A:
  %e : semver.ps.BD(_, A, Unit)
  Unit{}

# ---- auth_flight ----

# proof_auth_flight: the laws of LAWS.bend section auth_flight (A1). Every event
# keeps an invariant of the reachable states (`pf.Inv`): the callers that
# lead a flight are as many as the flights in flight (one or none); a
# leader leads the flight that lands next; a leader about to land a
# credential finds it stored, or a newer one; and a finished caller of a
# flight holds the outcome that flight landed with. The laws follow from
# it.

# Logic and numbers
# -----------------

def auth_flight.pf.BD(b: Bool, t: Type, f: Type) -> Type:
  match b:
    case True{}:
      t
    case False{}:
      f

def pf.absurd(-A: Type, e: {True{} == False{} : Bool}) -> A:
  %e : auth_flight.pf.BD(_, Unit, A)
  Unit{}

# ---- themes ----

# proof_themes: the T1 laws of the theme model
# in bend/theme.bend.
#
# Resolution scans the candidates in order: a candidate that does not
# resolve the name passes the scan on, so before the first one that does
# the scan finds nothing, and with none at all it ends at the default
# theme with a warning. A loaded file passed the validity check. The
# validity check asks of each token what its fill needs, so the fill of
# every token of a valid file has a value. The mode and the palette read
# only the colors and the export page, never the name. The shipped
# themes' contrasts and 256-color indices are finite: the checker
# computes them.

# Logic
# -----

def themes.pt.BD(b: Bool, t: Type, f: Type) -> Type:
  match b:
    case True{}:
      t
    case False{}:
      f

# ---- progress_report ----

# proof_progress_report: lemmas for the laws that a harness failure is
# reported (LAWS.bend section progress): the auxiliary-model fallback of
# bend/aux_fallback.bend and the skill and template loading of
# bend/skill_load.bend.
#
# Fallbacks. The events of a session come from one pass at a time
# (`Af.go`), so each law is an induction over the passes with any set of
# shown keys. A substitution event of key k comes with a notice of k
# unless the session showed k before; a key joins the shown set only with
# its notice. So every substituted key is shown or noticed, and from an
# empty set, noticed. The other way is simpler: a notice of k comes only
# right after the substitution event of k.
#
# Loading. Each candidate file adds its path to the loaded list when it is
# good, and a diagnostic with its path when it is not. So each candidate's
# path is on one of the two lists. A loaded path and a reported path are
# each the path of some candidate; when no two candidates share a path, no
# path is on both.
#
# A recursive proof takes the value it inspects as a parameter (Bend
# matches only parameters), with an equation that names it.

# Logic
# -----

def ppr.BD(b: Bool, t: Type, f: Type) -> Type:
  match b:
    case True{}:
      t
    case False{}:
      f

def ppr.absurd(-A: Type, e: {True{} == False{} : Bool}) -> A:
  %e : ppr.BD(_, Unit, A)
  Unit{}

def ppr.absurdF(-A: Type, e: {False{} == True{} : Bool}) -> A:
  %e : ppr.BD(_, A, Unit)
  Unit{}

# ---- supervisor ----

# proof_supervisor: the D1 laws of LAWS.bend section supervisor.
#
# - restart_gives_up: the failures of a crash loop stay in the window, so
#   their count only grows (`ps.block`), up to the give-up.
# - timeouts_ordered: each timeout is a sum that contains the timeouts it
#   waits for.
# - revive_after_refresh: the time since the last record stays below the
#   refresh period (`ps.since_lt`), so a boot within the boot window
#   finds the evidence within the max age.
# - orphan_never_aborts_resumable: every exit is sound (`ps.exit_sound`)
#   and an exit is final.
# - idle_shutdown_never_aborts: a closed gate never holds a run
#   (`ps.Inv`), so a commit, which needs every gate closed, stops no run.
# - adopt_same_build: an adoption reads equal build numbers.

# Logic
# -----

def supervisor.ps.BD(b: Bool, t: Type, f: Type) -> Type:
  match b:
    case True{}:
      t
    case False{}:
      f

def supervisor.ps.absurd(-A: Type, e: {True{} == False{} : Bool}) -> A:
  %e : supervisor.ps.BD(_, Unit, A)
  Unit{}

def supervisor.ps.absurdF(-A: Type, e: {False{} == True{} : Bool}) -> A:
  %e : supervisor.ps.BD(_, A, Unit)
  Unit{}

# ---- tui_color ----

# proof_tui_color: the T3 laws of
# the model in bend/tui_color.bend.
#
# Nat.divmod adds one to q * n + r per step and keeps r below n, so n
# times the quotient is at most x, and every q with n * q at most x is at
# most the quotient. So
# adding d to x never lowers the quotient, and raises it when d is at
# least n. A rung moves each channel from the last rung by such a step:
# the rising channels count the weight up, the falling ones count it
# down. So every channel moves toward the high end, and the widest
# channel, at least n wide, moves at each rung: a rung differs from all
# the rungs after it. A band is reached when w * num <= t * den; more
# tokens keep it reached, and a factor 1 + k on both t and w cancels.

# Logic
# -----

def pu.BD(+b: Bool, t: Type, f: Type) -> Type:
  match b:
    case True{}:
      t
    case False{}:
      f

def pu.absurd_ft(-A: Type, +e: {False{} == True{} : Bool}) -> A:
  %e : pu.BD(_, A, Unit)
  Unit{}

# ---- path_policy ----

# proof_path_policy: the (G1) laws (LAWS.bend section path_policy) of the path
# policy model in bend/path_policy.bend.
#
# A resolution keeps its invariant `looped or linkfree(at)`: a name it
# pushes is no link (the link test is the `look` it carries), `..` keeps
# a prefix, and a link's target starts from `/` or from the link's
# directory (`pp.go_lf`). The class picks Secret first and Inside last
# (`pp.pick_inside`, `pp.pick_guarded`); `demote` only moves Inside to
# Outside. Secret (code 6) is never grantable, so a write to a secret,
# or a read of one, reduces to the user's answer. A write that runs
# without a yes is not Secret, so its real location is no secret, and a
# write there leaves every secret cell as it was (`pp.secrets_set`).

# Logic
# -----

def path_policy.pp.BD(b: Bool, t: Type, f: Type) -> Type:
  match b:
    case True{}:
      t
    case False{}:
      f

def pp.absurd(-A: Type, e: {True{} == False{} : Bool}) -> A:
  %e : path_policy.pp.BD(_, Unit, A)
  Unit{}

# ---- approvals ----

# proof_approvals: the lemmas PROOF.bend proves the (G5) laws with
# (LAWS.bend section approvals), about the model in bend/approvals.bend.

# Logic
# -----

def approvals.pa.BD(b: Bool, t: Type, f: Type) -> Type:
  match b:
    case True{}:
      t
    case False{}:
      f

def approvals.pa.absurdF(-A: Type, e: {False{} == True{} : Bool}) -> A:
  %e : approvals.pa.BD(_, A, Unit)
  Unit{}

# ---- retry_policy ----

# proof_retry_policy: the laws of LAWS.bend section retry over the model in
# bend/retry.bend. Most decisions are a match on their inputs, so most
# laws follow by case analysis. A clash of two values is refuted with a
# motive that sends the expected value to the goal and the other to Unit.
#
# - retry_never_parked, retry_never_limit, retry_status_first: the park
#   and the limit are matched first; then each side computes to the same
#   value.
# - retry_never_client_error, retry_server_errors, retry_only_retryable:
#   a helper takes the result of `Nat.is_lt(s, 500n)` as a Bool with its
#   equation, and matches on it. Below 500, the status must be listed;
#   at 500 or more, the status is a server error.
# - retry_kind_before_text: a known kind has a class that is not Unsure,
#   so the text is not read.
# - retry_after_respected: the wait is `Nat.max(jitter, s)`, and
#   `Nat.max_ge_r` gives that it is at least s. A refused wait sends no
#   retry.
# - retry_refuses_past_cap: the two premises make the refusal test True.
# - The failover laws: each pick (`pick.fresh`, `pick.back`) is shown, by
#   induction on its order list, to give only a switch that satisfies its
#   own Bool condition (the equation of the condition goes into
#   `pick.sel`); its switch is never the last provider, since the order
#   holds no last (`rp.order_notin`: the order's first part is above
#   last, its second part below it). `next` then goes through `next.last`, `next.budget` and
#   `next.mode` with the equations of the last attempt, the budget and
#   the all-seen test. From these facts, `good` gets the five `Switch`
#   checks together; each failover law takes one of them.
# - deferred_pays_once, deferred_bounded_in_time: a step never sends
#   while the job is live, and never polls a live job with 0 ms left.
#   Induction over the replies, with any start tally, shows that the run
#   adds 0 to each count.
# - deferred_failed_poll_repolls: the two premises make the repoll test
#   True.
# - stall_retry_extends: idle < idle + idle when idle > 0.
# - stall_detection_bounded: induction over the events, with any start
#   time: a stall ends at the last event plus the deadline, a close at
#   the last event, which is at most it plus the deadline.
# - stall_silent_ends_at_deadline: by computation.
# - The exact laws (retry_classifier_exact, retry_wait_*, retry_step_exact,
#   retry_jitter_*, failover_exact, the saturation laws, the anchors):
#   each model helper is shown equal to its spec helper of LAWS.bend by
#   induction (rx.tried, rx.wait, rx.fresh, rx.back, ...). The bounded
#   doubling `R.double` is min(rs.twice, cap) (rx.double): a halted step
#   has b + b past cap, and twice(j, b + b) >= b + b. A saturated server
#   wait (min(w, c), c above max) keeps every wait at most max and keeps
#   every wait past max past max (rx.cw_sel); a saturated base at or past
#   max doubles to max either way (rx.base_sat).

# Clashes
# -------

def rp.BD(b: Bool, A: Type) -> Type:
  match b:
    case True{}:
      A
    case False{}:
      Unit

def rp.absurdF(-A: Type, e: {False{} == True{} : Bool}) -> A:
  %e : rp.BD(_, A)
  Unit{}

def rp.ND(b: Bool, A: Type) -> Type:
  match b:
    case True{}:
      Unit
    case False{}:
      A

def rp.absurdT(-A: Type, e: {True{} == False{} : Bool}) -> A:
  %e : rp.ND(_, A)
  Unit{}

# j < n and j = n at once
def pc.lt_ne(-A: Type, +j: Nat, +n: Nat, lt: {Nat.is_le(1n+j, n) == True{} : Bool}, eq: {Nat.is_eq(j, n) == True{} : Bool}) -> A:
  match j n:
    case 0n 0n:
      child.pc.absurd(A, lt)
    case 0n 1n+q:
      child.pc.absurd(A, eq)
    case 1n+p 0n:
      child.pc.absurd(A, eq)
    case 1n+p 1n+q:
      pc.lt_ne(A, p, q, lt, eq)

# nothing is below 0
def pc.lt_zero(-A: Type, a: Nat, e: {Nat.is_lt(a, 0n) == True{} : Bool}) -> A:
  match a:
    case 0n:
      pc.absurd_ft(A, e)
    case 1n+p:
      pc.absurd_ft(A, e)

def pt.lt_zero(-A: Type, p: Nat, lt: {Nat.is_lt(p, 0n) == True{} : Bool}) -> A:
  match p:
    case 0n:
      tree.pt.absurdF(A, lt)
    case 1n+q:
      tree.pt.absurdF(A, lt)

def ND(n: Nat, t: Type, f: Type) -> Type:
  match n:
    case 0n:
      t
    case 1n+p:
      f

# 0 is no successor
def zero_succ(-A: Type, -n: Nat, e: {0n == 1n+n : Nat}) -> A:
  %e : ND(_, Unit, A)
  Unit{}

def pf.ND(n: Nat, z: Type, s: Type) -> Type:
  match n:
    case 0n:
      z
    case 1n+p:
      s

def pf.succ_ne_zero(-A: Type, -n: Nat, e: {1n+n == 0n : Nat}) -> A:
  %e : pf.ND(_, A, Unit)
  Unit{}

def pf.OD(v: Fs.Open, A: Type) -> Type:
  match v:
    case Fs.Opened{p}:
      A
    case Fs.NeedsCwd{}:
      Unit
    case Fs.Gone{p}:
      Unit
    case Fs.NotDir{p}:
      Unit

def pf.needs_opened(-A: Type, +p: Nat, e: {Fs.NeedsCwd{} == Fs.Opened{p} : Fs.Open}) -> A:
  %e : pf.OD(_, A)
  Unit{}

def pf.gone_opened(-A: Type, +q: Nat, +p: Nat, e: {Fs.Gone{q} == Fs.Opened{p} : Fs.Open}) -> A:
  %e : pf.OD(_, A)
  Unit{}

def pf.notdir_opened(-A: Type, +q: Nat, +p: Nat, e: {Fs.NotDir{q} == Fs.Opened{p} : Fs.Open}) -> A:
  %e : pf.OD(_, A)
  Unit{}

def pf.snd(-A: Type, -B: Type, p: (A & B)) -> B:
  (a, b) = p
  b

def themes.pt.none_some(-A: Type, -B: Data, -b: B, e: {None{} == Some{b} : Maybe<&2, B>}) -> A:
  %e : themes.pt.BD(Maybe.is_some(&2, B, _), A, Unit)
  Unit{}

# the five checks of a switch together
def rp.Good(m: Maybe<&2, R.Switch>, len: Nat, ts: List<&2, R.Tried>, p: R.Policy) -> Type:
  {R.Switch.not_last(m, ts) == True{} : Bool} & ({R.Switch.fresh_first(m, len, ts) == True{} : Bool} & ({R.Switch.return_waits(m, ts) == True{} : Bool} & ({R.Switch.capped(m, R.Policy.max(p)) == True{} : Bool} & {R.Switch.within(m, ts, p) == True{} : Bool})))

def rp.good_none(+len: Nat, +ts: List<&2, R.Tried>, +p: R.Policy) -> rp.Good(None{}, len, ts, p):
  ({==}, ({==}, ({==}, ({==}, {==}))))

# A at Inside, Unit elsewhere: refutes {c == Inside} for c not Inside
def pp.CM(c: Pp.Cls, A: Type) -> Type:
  match c:
    case Pp.Inside{}:
      A
    case Pp.Outside{}:
      Unit
    case Pp.Protected{}:
      Unit
    case Pp.Secret{}:
      Unit

def pp.not_inside(-A: Type, c: Pp.Cls, n: {Pp.Cls.inside(c) == False{} : Bool}, e: {c == Pp.Inside{} : Pp.Cls}) -> A:
  match c:
    case Pp.Inside{}:
      pp.absurd(A, n)
    case Pp.Outside{}:
      %e : pp.CM(_, A)
      Unit{}
    case Pp.Protected{}:
      %e : pp.CM(_, A)
      Unit{}
    case Pp.Secret{}:
      %e : pp.CM(_, A)
      Unit{}
