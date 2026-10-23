# eukhe: the laws of area workflow

import Base
import ../bend/ffi_workflow.bend as FW
import ../bend/wire.bend as Wr
import ../bend/workflow.bend as W
import ./base.bend as LawsBase

# ---- workflow ----

# LAWS (WF, dynamic workflows): a run never holds more agents at once
# than its concurrency, never spawns more than its budget, spawns only
# the uncached keys when it resumes, and one failed agent never changes
# its siblings' results. An `agent()` call is admitted by one rule
# (W.admit, the Rust `admit` of globals.rs): a call whose ordinal the run
# admitted before never spawns again, a call the earlier run answered
# reuses the first such answer, and only then the budget decides. A run's
# concurrency is its size's, at most the subagent cap (W.effective, the
# Rust `effective_limits`). Each law is an open claim about the model in
# bend/workflow.bend; PROOF.bend proves them (as Laws.<law>) with the
# lemmas of PROOF.bend section workflow.

# Spec helpers
# ------------

# a row status that holds a finished answer: done, or served from cache
def wf_serves(s: W.Sts) -> Bool:
  match s:
    case W.Queued{}:
      False{}
    case W.Running{}:
      False{}
    case W.Finished{}:
      True{}
    case W.Erred{}:
      False{}
    case W.Cancelled{}:
      False{}
    case W.Cached{}:
      True{}

# what a repeated ordinal does: an ended row replays its answer, a
# queued or running one is reattached
def wf_again(s: W.Sts) -> W.Admit:
  match s:
    case W.Queued{}:
      W.Reattach{}
    case W.Running{}:
      W.Reattach{}
    case W.Finished{}:
      W.Ended{}
    case W.Erred{}:
      W.Ended{}
    case W.Cancelled{}:
      W.Ended{}
    case W.Cached{}:
      W.Ended{}

def wf_next(m: Maybe<&2, Nat>) -> Maybe<&2, Nat>:
  match m:
    case None{}:
      None{}
    case Some{i}:
      Some{1n+i}

def wf_first.at(hit: Bool, rest: Maybe<&2, Nat>) -> Maybe<&2, Nat>:
  match hit:
    case True{}:
      Some{0n}
    case False{}:
      wf_next(rest)

# the position of the first row of rs with key k and a finished answer
def wf_first(rs: List<&2, W.Row>, +k: Nat) -> Maybe<&2, Nat>:
  match rs:
    case Nil{}:
      None{}
    case W.Row{key, s} <> rest:
      wf_first.at(Bool.and(Nat.is_eq(key, k), wf_serves(s)), wf_first(rest, k))

# the smaller of a and b
def wf_min(a: Nat, b: Nat) -> Nat:
  match a b:
    case 0n _:
      0n
    case 1n+x 0n:
      0n
    case 1n+x 1n+y:
      1n+wf_min(x, y)

# LAW: after any asks and settles, the running agents and the free slots
# still add up to the concurrency: running never goes above it
law wf_running_within_concurrency:
  for cap: Nat
  for es: List<&2, W.Ev>
  {W.size(W.run(es, W.pool(cap))) == cap : Nat}

# LAW: after any number of spawn attempts, the spawned agents and the
# budget left add up to the run's max agents: spawned never goes above it
law wf_spawned_within_budget:
  for max: Nat
  for n: Nat
  {W.size(W.spawns(n, W.pool(max))) == max : Nat}

# LAW: a resumed call whose key the earlier run finished spawns nothing
law wf_cached_key_spawns_nothing:
  for k: Nat
  for cache: List<&2, Nat>
  for hit: {W.member(k, cache) == True{} : Bool}
  {W.cost(k, cache) == 0n : Nat}

# LAW: a resume with nothing cached spawns every key
law wf_empty_cache_spawns_all:
  for keys: List<&2, Nat>
  {W.resumed([], keys) == List.length(&2, Nat, keys) : Nat}

# LAW: a failed agent gives null in its own slot and leaves every
# sibling's result as it was
law wf_failure_spares_siblings:
  for xs: List<&2, W.Out>
  for ys: List<&2, W.Out>
  {W.results(W.cat(xs, W.Failed{} <> ys)) == W.rcat(W.results(xs), None{} <> W.results(ys)) : List<&2, Maybe<&2, Nat>>}

# LAW: a call whose ordinal the run admitted before (a replay after a
# restart) spawns nothing and takes no budget: an ended row replays its
# answer, a queued or running one is reattached
# EXCLUDES: a second agent for one ordinal, budget charged twice, a
#   running agent reported as ended or an ended one run again
law wf_admitted_never_respawns:
  for s: W.Sts
  for k: Nat
  for rs: List<&2, W.Row>
  for p: W.Pool
  {W.admit(Some{s}, k, rs, p) == (wf_again(s), p) : W.Admit & W.Pool}

# LAW: a new call whose key the earlier run answered reuses the first row
# with that key and a finished answer, and takes no budget
# EXCLUDES: a cached key spawned again, a failed or unfinished row
#   reused, a later duplicate reused instead of the first
law wf_reuses_first_answer:
  for +k: Nat
  for +rs: List<&2, W.Row>
  for p: W.Pool
  for i: Nat
  for hit: {wf_first(rs, k) == Some{i} : Maybe<&2, Nat>}
  {W.admit(None{}, k, rs, p) == (W.Reuse{i}, p) : W.Admit & W.Pool}

# LAW: a new call with no earlier answer spawns while the budget has an
# agent left, and takes one agent of it
# EXCLUDES: refusing a call the budget allows, a spawn that takes no budget
law wf_spawns_within_budget:
  for +k: Nat
  for +rs: List<&2, W.Row>
  for t: Nat
  for l: Nat
  for miss: {wf_first(rs, k) == None{} : Maybe<&2, Nat>}
  {W.admit(None{}, k, rs, W.Pool{t, 1n+l}) == (W.Spawn{}, W.Pool{1n+t, l}) : W.Admit & W.Pool}

# LAW: a new call with no earlier answer and no agent left is refused,
# and the budget stays
# EXCLUDES: a spawn past max agents
law wf_refused_when_spent:
  for +k: Nat
  for +rs: List<&2, W.Row>
  for t: Nat
  for miss: {wf_first(rs, k) == None{} : Maybe<&2, Nat>}
  {W.admit(None{}, k, rs, W.Pool{t, 0n}) == (W.Refused{}, W.Pool{t, 0n}) : W.Admit & W.Pool}

# LAW witness: the first answer skips rows of another key and rows
# without a finished answer, and a key with no answer has none
# EXCLUDES: a vacuous wf_reuses_first_answer or wf_spawns_within_budget
law wf_first_example:
  {(wf_first([W.Row{1n, W.Finished{}}, W.Row{2n, W.Running{}}, W.Row{2n, W.Erred{}}, W.Row{2n, W.Cached{}}, W.Row{2n, W.Finished{}}], 2n), wf_first([W.Row{1n, W.Finished{}}], 2n)) == (Some{3n}, None{}) : Maybe<&2, Nat> & Maybe<&2, Nat>}

# LAW: with no subagent cap (0) a run's limits are its size's
# EXCLUDES: a cap of 0 read as "no agents"
law wf_limits_uncapped:
  for c: Nat
  for m: Nat
  {W.effective(W.Limits{c, m}, 0n) == W.Limits{c, m} : W.Limits}

# LAW: under a subagent cap a run's concurrency is the smaller of its
# size's and the cap; its max agents stay
# EXCLUDES: a cap that raises the concurrency, a cap ignored, a cap
#   applied to the max agents
law wf_limits_capped:
  for +c: Nat
  for m: Nat
  for +x: Nat
  {W.effective(W.Limits{c, m}, 1n+x) == W.Limits{wf_min(c, 1n+x), m} : W.Limits}

# The wire codec of bend/ffi_workflow.bend (grammar: that file's header,
# crates/eukhe-bend/WIRE.md). R1: every request and reply reads back; R2:
# a well-formed request answers the model's answer (W.admit, W.effective),
# encoded; R3: a malformed or overlong request answers the error form,
# never a model answer. Every input is free.

# what fits the wire: every Nat (and every list length) at most 14 digits
def wfw_row_fits(r: W.Row) -> Bool:
  match r:
    case W.Row{k, s}:
      LawsBase.wire_fits(k)

def wfw_rows_fit(rs: List<&2, W.Row>) -> Bool:
  match rs:
    case Nil{}:
      True{}
    case Con{r, t}:
      Bool.and(wfw_row_fits(r), wfw_rows_fit(t))

def wfw_pool_fits(p: W.Pool) -> Bool:
  match p:
    case W.Pool{t, l}:
      Bool.and(LawsBase.wire_fits(t), LawsBase.wire_fits(l))

def wfw_req_fits(r: FW.Req) -> Bool:
  match r:
    case FW.AdmitReq{prior, k, +rows, p}:
      Bool.and(LawsBase.wire_fits(k), Bool.and(Bool.and(LawsBase.wire_fits(List.length(&2, W.Row, rows)), wfw_rows_fit(rows)), wfw_pool_fits(p)))
    case FW.LimitsReq{c, m, cap}:
      Bool.and(LawsBase.wire_fits(c), Bool.and(LawsBase.wire_fits(m), LawsBase.wire_fits(cap)))

def wfw_admit_fits(a: W.Admit) -> Bool:
  match a:
    case W.Ended{}:
      True{}
    case W.Reattach{}:
      True{}
    case W.Reuse{i}:
      LawsBase.wire_fits(i)
    case W.Spawn{}:
      True{}
    case W.Refused{}:
      True{}

def wfw_limits_fits(l: W.Limits) -> Bool:
  match l:
    case W.Limits{c, m}:
      Bool.and(LawsBase.wire_fits(c), LawsBase.wire_fits(m))

# LAW R1 a row's status reads back, and the rest is untouched
# EXCLUDES: two statuses with one tag, a status read as another
law wfw_sts_round_trip:
  for s: W.Sts
  for rest: String
  {FW.get_sts(FW.put_sts(s, rest)) == Wr.Got{s, rest} : Wr.Dec<W.Sts>}

# LAW R1 the prior row's status (none or one) reads back
# EXCLUDES: a missing prior read as a status, or a status dropped
law wfw_prior_round_trip:
  for m: Maybe<&2, W.Sts>
  for rest: String
  {FW.get_prior(FW.put_prior(m, rest)) == Wr.Got{m, rest} : Wr.Dec<Maybe<&2, W.Sts>>}

# LAW R1 a row that fits reads back
# EXCLUDES: a row's key or status lost or misread
law wfw_row_round_trip:
  for +r: W.Row
  for rest: String
  for h: {wfw_row_fits(r) == True{} : Bool}
  {FW.get_row(FW.put_row(r, rest)) == Wr.Got{r, rest} : Wr.Dec<W.Row>}

# LAW R1 a list of rows that fit, of a length that fits, reads back
# EXCLUDES: rows lost, added, reordered or misread, a wrong count
law wfw_rows_round_trip:
  for +rs: List<&2, W.Row>
  for rest: String
  for h: {Bool.and(LawsBase.wire_fits(List.length(&2, W.Row, rs)), wfw_rows_fit(rs)) == True{} : Bool}
  {Wr.get_list(~W.Row, ~FW.get_row, Wr.put_list(~W.Row, ~FW.put_row, rs, rest)) == Wr.Got{rs, rest} : Wr.Dec<List<&2, W.Row>>}

# LAW R1 a pool that fits reads back (request and reply)
# EXCLUDES: taken and left swapped or misread
law wfw_pool_round_trip:
  for +p: W.Pool
  for rest: String
  for h: {wfw_pool_fits(p) == True{} : Bool}
  {FW.get_pool(FW.put_pool(p, rest)) == Wr.Got{p, rest} : Wr.Dec<W.Pool>}

# LAW R1 a request that fits reads back, of either kind
# EXCLUDES: one kind read as the other, a field lost, swapped or misread
law wfw_req_round_trip:
  for +r: FW.Req
  for rest: String
  for h: {wfw_req_fits(r) == True{} : Bool}
  {FW.get_req(FW.put_req(r, rest)) == Wr.Got{r, rest} : Wr.Dec<FW.Req>}

# LAW R1 an admission decision that fits reads back
# EXCLUDES: two decisions with one tag, a reused row's index misread
law wfw_admit_round_trip:
  for +a: W.Admit
  for rest: String
  for h: {wfw_admit_fits(a) == True{} : Bool}
  {FW.get_admit(FW.put_admit(a, rest)) == Wr.Got{a, rest} : Wr.Dec<W.Admit>}

# LAW R1 the reply to an Admit, the decision then the pool, reads back
# EXCLUDES: a reply that drops the pool or puts it before the decision
law wfw_decision_round_trip:
  for +a: W.Admit
  for +p: W.Pool
  for rest: String
  for h: {Bool.and(wfw_admit_fits(a), wfw_pool_fits(p)) == True{} : Bool}
  {FW.get_decision(FW.put_decision((a, p), rest)) == Wr.Got{(a, p), rest} : Wr.Dec<+Sigma<W.Admit, x => W.Pool>>}

# LAW R1 the reply to a Limits request reads back
# EXCLUDES: concurrency and max agents swapped or misread
law wfw_limits_round_trip:
  for +l: W.Limits
  for rest: String
  for h: {wfw_limits_fits(l) == True{} : Bool}
  {FW.get_limits(FW.put_limits(l, rest)) == Wr.Got{l, rest} : Wr.Dec<W.Limits>}

# LAW R2 an encoded Admit request answers the model's admission, encoded
# EXCLUDES: an entry that decides other than W.admit, or drops a field
#   on the way in or out
law wfw_answers_admit:
  for prior: Maybe<&2, W.Sts>
  for +k: Nat
  for +rows: List<&2, W.Row>
  for p: W.Pool
  for h: {wfw_req_fits(FW.AdmitReq{prior, k, rows, p}) == True{} : Bool}
  {FW.ffi(FW.put_req(FW.AdmitReq{prior, k, rows, p}, "")) == FW.put_decision(W.admit(prior, k, rows, p), "") : String}

# LAW R2 an encoded Limits request answers the model's limits, encoded
# EXCLUDES: an entry that ignores the cap or the run's size
law wfw_answers_limits:
  for +c: Nat
  for +m: Nat
  for +cap: Nat
  for h: {wfw_req_fits(FW.LimitsReq{c, m, cap}) == True{} : Bool}
  {FW.ffi(FW.put_req(FW.LimitsReq{c, m, cap}, "")) == FW.put_limits(W.effective(W.Limits{c, m}, cap), "") : String}

# LAW R3 a malformed request answers the error form
# EXCLUDES: a default answer (a spawn, a limit) for a request it cannot read
law wfw_malformed:
  for +s: String
  for h: {FW.get_req(s) == Wr.Bad{} : Wr.Dec<FW.Req>}
  {FW.ffi(s) == Wr.err("workflow: malformed request") : String}

# LAW R3 a request with input left over answers the error form
# EXCLUDES: an entry that answers a request followed by garbage
law wfw_left_over:
  for +r: FW.Req
  for c: Char
  for rest: String
  for h: {wfw_req_fits(r) == True{} : Bool}
  {FW.ffi(FW.put_req(r, SCon{c, rest})) == Wr.err("workflow: input left over") : String}

# LAW R1 anchor: the tags of the header (Sts 0 queued | 1 running | 2 done
# | 3 failed | 4 cancelled | 5 cached; the decision 0 ended | 1 reattach |
# 2 i reuse | 3 spawn | 4 refused)
# EXCLUDES: tags in another order than the grammar's
law wfw_tags_example:
  {FW.put_sts(W.Queued{}, FW.put_sts(W.Running{}, FW.put_sts(W.Finished{}, FW.put_sts(W.Erred{}, FW.put_sts(W.Cancelled{}, FW.put_sts(W.Cached{}, "")))))) == "0,1,2,3,4,5," : String} & {FW.put_admit(W.Ended{}, FW.put_admit(W.Reattach{}, FW.put_admit(W.Reuse{9n}, FW.put_admit(W.Spawn{}, FW.put_admit(W.Refused{}, ""))))) == "0,1,2,9,3,4," : String}

# LAW R1 anchor: a prior status is 0 (none) or 1, then the status
# EXCLUDES: another spelling of a missing prior row
law wfw_prior_example:
  {FW.put_prior(None{}, FW.put_prior(Some{W.Finished{}}, "")) == "0,1,2," : String}

# LAW R1 anchor and witness: a row is its key, then its status
# EXCLUDES: a vacuous wfw_row_round_trip, fields in another order
law wfw_row_example:
  {wfw_row_fits(W.Row{3n, W.Erred{}}) == True{} : Bool} & {FW.put_row(W.Row{3n, W.Erred{}}, "") == "3,3," : String}

# LAW R1 anchor and witness: rows are their count, then each row
# EXCLUDES: a vacuous wfw_rows_round_trip
law wfw_rows_example:
  {Bool.and(LawsBase.wire_fits(List.length(&2, W.Row, [W.Row{3n, W.Erred{}}, W.Row{4n, W.Cached{}}])), wfw_rows_fit([W.Row{3n, W.Erred{}}, W.Row{4n, W.Cached{}}])) == True{} : Bool} & {Wr.put_list(~W.Row, ~FW.put_row, [W.Row{3n, W.Erred{}}, W.Row{4n, W.Cached{}}], "") == "2,3,3,4,5," : String}

# LAW R1 anchor and witness: a pool is taken, then left
# EXCLUDES: a vacuous wfw_pool_round_trip, fields in another order
law wfw_pool_example:
  {wfw_pool_fits(W.Pool{1n, 2n}) == True{} : Bool} & {FW.put_pool(W.Pool{1n, 2n}, "") == "1,2," : String}

# LAW R1 anchor and witness: an Admit request is 0, prior, key, rows, pool
# EXCLUDES: a vacuous wfw_req_round_trip or wfw_answers_admit, fields in
#   another order
law wfw_admit_req_example:
  {wfw_req_fits(FW.AdmitReq{Some{W.Cached{}}, 7n, [W.Row{3n, W.Erred{}}], W.Pool{1n, 2n}}) == True{} : Bool} & {FW.put_req(FW.AdmitReq{Some{W.Cached{}}, 7n, [W.Row{3n, W.Erred{}}], W.Pool{1n, 2n}}, "") == "0,1,5,7,1,3,3,1,2," : String}

# LAW R1 anchor and witness: a Limits request is 1, concurrency, max
# agents, cap
# EXCLUDES: a vacuous wfw_answers_limits, fields in another order
law wfw_limits_req_example:
  {wfw_req_fits(FW.LimitsReq{4n, 9n, 2n}) == True{} : Bool} & {FW.put_req(FW.LimitsReq{4n, 9n, 2n}, "") == "1,4,9,2," : String}

# LAW R1 anchor and witness: a reused row's decision carries its index
# EXCLUDES: a vacuous wfw_admit_round_trip
law wfw_admit_example:
  {wfw_admit_fits(W.Reuse{2n}) == True{} : Bool} & {FW.put_admit(W.Reuse{2n}, "") == "2,2," : String}

# LAW R1 anchor and witness: the reply to an Admit is the decision, then
# the pool
# EXCLUDES: a vacuous wfw_decision_round_trip
law wfw_decision_example:
  {Bool.and(wfw_admit_fits(W.Reuse{2n}), wfw_pool_fits(W.Pool{1n, 0n})) == True{} : Bool} & {FW.put_decision((W.Reuse{2n}, W.Pool{1n, 0n}), "") == "2,2,1,0," : String}

# LAW R1 anchor and witness: the reply to Limits is concurrency, max agents
# EXCLUDES: a vacuous wfw_limits_round_trip
law wfw_limits_example:
  {wfw_limits_fits(W.Limits{2n, 9n}) == True{} : Bool} & {FW.put_limits(W.Limits{2n, 9n}, "") == "2,9," : String}

# LAW R2 anchor: a run of concurrency 4 and 9 agents capped at 2 runs 2
# at once, 9 agents, end to end
# EXCLUDES: an entry that answers other bytes than the grammar's
law wfw_ffi_example:
  {FW.ffi("1,4,9,2,") == "2,9," : String}

# LAW R3 witness: a request with an unknown kind is malformed
# EXCLUDES: a vacuous wfw_malformed
law wfw_malformed_example:
  {FW.get_req("2,") == Wr.Bad{} : Wr.Dec<FW.Req>} & {FW.ffi("2,") == Wr.err("workflow: malformed request") : String}
