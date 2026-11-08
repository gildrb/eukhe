# eukhe: the laws of area workflow, section model: the workflow model (bend/workflow.bend) and the entry
# bend/ffi_workflow.bend by its wire and by the grammar's spelling

import Base
import ../../bend/ffi_workflow.bend as FW
import ../../bend/wire.bend as Wr
import ../../bend/workflow.bend as W
import ../base.bend as LawsBase

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
# bend/workflow.bend; PROOF.bend proves them (as Workflow.<law>) with the
# lemmas of proof/workflow/.

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

# what one semaphore event does to a pool: an ask moves a unit from left
# to taken while one is left (else the pool stays: the call waits), a
# settle moves a taken unit back to left (with none taken the pool stays)
def wf_step(e: W.Ev, p: W.Pool) -> W.Pool:
  match e:
    case W.Ask{}:
      match p:
        case W.Pool{t, l}:
          match l:
            case 0n:
              W.Pool{t, 0n}
            case 1n+m:
              W.Pool{1n+t, m}
    case W.Settle{}:
      match p:
        case W.Pool{t, l}:
          match t:
            case 0n:
              W.Pool{0n, l}
            case 1n+s:
              W.Pool{s, 1n+l}

# the pool after the events es, in order, from p: the fold of wf_step
def wf_run(es: List<&2, W.Ev>, p: W.Pool) -> W.Pool:
  match es:
    case Nil{}:
      p
    case e <> rest:
      wf_run(rest, wf_step(e, p))

# the units a pool holds in all: the taken ones and the left ones
def wf_units(p: W.Pool) -> Nat:
  match p:
    case W.Pool{t, l}:
      Nat.add(t, l)

# the budget after n spawn attempts from p: each takes one unit while
# any is left, so the smaller of n and the units left move from left to
# taken
def wf_spawns(+n: Nat, p: W.Pool) -> W.Pool:
  match p:
    case W.Pool{t, +l}:
      W.Pool{Nat.add(wf_min(n, l), t), Nat.sub(l, n)}

# the earlier run finished key k: k is one of the cached keys
def wf_cached(+k: Nat, cache: List<&2, Nat>) -> Bool:
  match cache:
    case Nil{}:
      False{}
    case c <> rest:
      Bool.or(Nat.is_eq(c, k), wf_cached(k, rest))

def wf_cost.of(hit: Bool) -> Nat:
  match hit:
    case True{}:
      0n
    case False{}:
      1n

# the agents one call of a resumed run spawns: none for a cached key, one
# for another
def wf_cost(+k: Nat, cache: List<&2, Nat>) -> Nat:
  wf_cost.of(wf_cached(k, cache))

def wf_resumed.one(hit: Bool, n: Nat) -> Nat:
  match hit:
    case True{}:
      n
    case False{}:
      1n+n

# the agents a resumed run spawns for its keys: one per key the earlier
# run did not finish
def wf_resumed(+cache: List<&2, Nat>, keys: List<&2, Nat>) -> Nat:
  match keys:
    case Nil{}:
      0n
    case k <> rest:
      wf_resumed.one(wf_cached(k, cache), wf_resumed(cache, rest))

# what the script gets for one agent: its answer, or null for a failure
def wf_result(o: W.Out) -> Maybe<&2, Nat>:
  match o:
    case W.Answer{n}:
      Some{n}
    case W.Failed{}:
      None{}

# every agent's result, in item order
def wf_results(os: List<&2, W.Out>) -> List<&2, Maybe<&2, Nat>>:
  match os:
    case Nil{}:
      Nil{}
    case o <> rest:
      wf_result(o) <> wf_results(rest)

# LAW wf_running_within_concurrency: after any asks and settles, the running agents and the free slots
# still add up to the concurrency: running never goes above it
law wf_running_within_concurrency:
  for cap: Nat
  for es: List<&2, W.Ev>
  {W.size(W.run(es, W.pool(cap))) == cap : Nat}

# LAW wf_spawned_within_budget: after any number of spawn attempts, the spawned agents and the
# budget left add up to the run's max agents: spawned never goes above it
law wf_spawned_within_budget:
  for max: Nat
  for n: Nat
  {W.size(W.spawns(n, W.pool(max))) == max : Nat}

# LAW wf_cached_key_spawns_nothing: a resumed call whose key the earlier run finished spawns nothing
law wf_cached_key_spawns_nothing:
  for k: Nat
  for cache: List<&2, Nat>
  for hit: {W.member(k, cache) == True{} : Bool}
  {W.cost(k, cache) == 0n : Nat}

# LAW wf_empty_cache_spawns_all: a resume with nothing cached spawns every key
law wf_empty_cache_spawns_all:
  for keys: List<&2, Nat>
  {W.resumed([], keys) == List.length(&2, Nat, keys) : Nat}

# LAW wf_failure_spares_siblings: a failed agent gives null in its own slot and leaves every
# sibling's result as it was
law wf_failure_spares_siblings:
  for xs: List<&2, W.Out>
  for ys: List<&2, W.Out>
  {W.results(W.cat(xs, W.Failed{} <> ys)) == W.rcat(W.results(xs), None{} <> W.results(ys)) : List<&2, Maybe<&2, Nat>>}

# LAW wf_admitted_never_respawns: a call whose ordinal the run admitted before (a replay after a
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

# LAW wf_reuses_first_answer: a new call whose key the earlier run answered reuses the first row
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

# LAW wf_spawns_within_budget: a new call with no earlier answer spawns while the budget has an
# agent left, and takes one agent of it
# EXCLUDES: refusing a call the budget allows, a spawn that takes no budget
law wf_spawns_within_budget:
  for +k: Nat
  for +rs: List<&2, W.Row>
  for t: Nat
  for l: Nat
  for miss: {wf_first(rs, k) == None{} : Maybe<&2, Nat>}
  {W.admit(None{}, k, rs, W.Pool{t, 1n+l}) == (W.Spawn{}, W.Pool{1n+t, l}) : W.Admit & W.Pool}

# LAW wf_refused_when_spent: a new call with no earlier answer and no agent left is refused,
# and the budget stays
# EXCLUDES: a spawn past max agents
law wf_refused_when_spent:
  for +k: Nat
  for +rs: List<&2, W.Row>
  for t: Nat
  for miss: {wf_first(rs, k) == None{} : Maybe<&2, Nat>}
  {W.admit(None{}, k, rs, W.Pool{t, 0n}) == (W.Refused{}, W.Pool{t, 0n}) : W.Admit & W.Pool}

# LAW wf_first_example (witness): the first answer skips rows of another key and rows
# without a finished answer, and a key with no answer has none
# EXCLUDES: a vacuous wf_reuses_first_answer or wf_spawns_within_budget
law wf_first_example:
  {(wf_first([W.Row{1n, W.Finished{}}, W.Row{2n, W.Running{}}, W.Row{2n, W.Erred{}}, W.Row{2n, W.Cached{}}, W.Row{2n, W.Finished{}}], 2n), wf_first([W.Row{1n, W.Finished{}}], 2n)) == (Some{3n}, None{}) : Maybe<&2, Nat> & Maybe<&2, Nat>}

# LAW wf_limits_uncapped: with no subagent cap (0) a run's limits are its size's
# EXCLUDES: a cap of 0 read as "no agents"
law wf_limits_uncapped:
  for c: Nat
  for m: Nat
  {W.effective(W.Limits{c, m}, 0n) == W.Limits{c, m} : W.Limits}

# LAW wf_limits_capped: under a subagent cap a run's concurrency is the smaller of its
# size's and the cap; its max agents stay
# EXCLUDES: a cap that raises the concurrency, a cap ignored, a cap
#   applied to the max agents
law wf_limits_capped:
  for +c: Nat
  for m: Nat
  for +x: Nat
  {W.effective(W.Limits{c, m}, 1n+x) == W.Limits{wf_min(c, 1n+x), m} : W.Limits}

# LAW wf_step_exact (WF): one semaphore event moves at most one unit: an
# ask takes a unit while one is left (else the pool stays and the call
# waits), a settle gives a taken unit back (with none taken the pool
# stays)
# EXCLUDES: a settle that gives nothing back (give(p) = p), an ask that
#   takes nothing, a unit moved twice, taken and left swapped
law wf_step_exact:
  for e: W.Ev
  for p: W.Pool
  {W.step(e, p) == wf_step(e, p) : W.Pool}

# LAW wf_run_exact (WF): the semaphore after any asks and settles, from
# any pool, is the fold of wf_step over them, in order
# EXCLUDES: a run that drops, repeats or reorders events, a run that
#   leaves the pool as it was
law wf_run_exact:
  for es: List<&2, W.Ev>
  for p: W.Pool
  {W.run(es, p) == wf_run(es, p) : W.Pool}

# LAW wf_pool_exact (WF): a run starts with every unit left and none
# taken, and a pool's size is its taken and left units together
# EXCLUDES: a run that starts with units taken, a size that counts one
#   counter only, or a constant
law wf_pool_exact:
  for cap: Nat
  for p: W.Pool
  {W.pool(cap) == W.Pool{0n, cap} : W.Pool} & {W.size(p) == wf_units(p) : Nat}

# LAW wf_spawns_exact (WF): n spawn attempts take one unit each while
# any is left: the smaller of n and the units left move to taken
# EXCLUDES: spawns(n, p) = p, a spawn that takes no budget or two
#   units, a spawn past the budget, taken and left swapped
law wf_spawns_exact:
  for n: Nat
  for p: W.Pool
  {W.spawns(n, p) == wf_spawns(n, p) : W.Pool}

# LAW wf_resume_exact (WF): a key is cached exactly when the earlier run
# finished it; one call of a resumed run spawns none for a cached key and
# one for another; a resumed run spawns one agent per uncached key
# EXCLUDES: member = False (a cached key spawned again, which leaves
#   wf_cached_key_spawns_nothing vacuous), member = True, a cost of 1 for
#   a cached key, a resume that counts every key, none, or a key twice
law wf_resume_exact:
  for +k: Nat
  for +cache: List<&2, Nat>
  for keys: List<&2, Nat>
  {W.member(k, cache) == wf_cached(k, cache) : Bool} & {W.cost(k, cache) == wf_cost(k, cache) : Nat} & {W.resumed(cache, keys) == wf_resumed(cache, keys) : Nat}

# LAW wf_results_exact (WF): an answered agent gives its answer, a failed
# one null, and `parallel` and `pipeline` give every item's result in
# item order
# EXCLUDES: result(Answer{n}) = None (every agent read as failed), an
#   answer changed, results dropped, added or reordered
law wf_results_exact:
  for o: W.Out
  for os: List<&2, W.Out>
  {W.result(o) == wf_result(o) : Maybe<&2, Nat>} & {W.results(os) == wf_results(os) : List<&2, Maybe<&2, Nat>>}

# LAW wf_cat_exact (WF): the joins wf_failure_spares_siblings reads put
# the first items, then the second, each kept
# EXCLUDES: cat(xs, ys) = ys with rcat(xs, ys) = ys (siblings before
#   the failed agent never checked), items dropped or reordered
law wf_cat_exact:
  for xs: List<&2, W.Out>
  for ys: List<&2, W.Out>
  for rs: List<&2, Maybe<&2, Nat>>
  for ss: List<&2, Maybe<&2, Nat>>
  {W.cat(xs, ys) == List.append(&2, W.Out, xs, ys) : List<&2, W.Out>} & {W.rcat(rs, ss) == List.append(&2, Maybe<&2, Nat>, rs, ss) : List<&2, Maybe<&2, Nat>>}

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

# LAW wfw_sts_round_trip (R1): a row's status reads back, and the rest is untouched
# EXCLUDES: two statuses with one tag, a status read as another
law wfw_sts_round_trip:
  for s: W.Sts
  for rest: String
  {FW.get_sts(FW.put_sts(s, rest)) == Wr.Got{s, rest} : Wr.Dec<W.Sts>}

# LAW wfw_prior_round_trip (R1): the prior row's status (none or one) reads back
# EXCLUDES: a missing prior read as a status, or a status dropped
law wfw_prior_round_trip:
  for m: Maybe<&2, W.Sts>
  for rest: String
  {FW.get_prior(FW.put_prior(m, rest)) == Wr.Got{m, rest} : Wr.Dec<Maybe<&2, W.Sts>>}

# LAW wfw_row_round_trip (R1): a row that fits reads back
# EXCLUDES: a row's key or status lost or misread
law wfw_row_round_trip:
  for +r: W.Row
  for rest: String
  for h: {wfw_row_fits(r) == True{} : Bool}
  {FW.get_row(FW.put_row(r, rest)) == Wr.Got{r, rest} : Wr.Dec<W.Row>}

# LAW wfw_rows_round_trip (R1): a list of rows that fit, of a length that fits, reads back
# EXCLUDES: rows lost, added, reordered or misread, a wrong count
law wfw_rows_round_trip:
  for +rs: List<&2, W.Row>
  for rest: String
  for h: {Bool.and(LawsBase.wire_fits(List.length(&2, W.Row, rs)), wfw_rows_fit(rs)) == True{} : Bool}
  {Wr.get_list(~W.Row, ~FW.get_row, Wr.put_list(~W.Row, ~FW.put_row, rs, rest)) == Wr.Got{rs, rest} : Wr.Dec<List<&2, W.Row>>}

# LAW wfw_pool_round_trip (R1): a pool that fits reads back (request and reply)
# EXCLUDES: taken and left swapped or misread
law wfw_pool_round_trip:
  for +p: W.Pool
  for rest: String
  for h: {wfw_pool_fits(p) == True{} : Bool}
  {FW.get_pool(FW.put_pool(p, rest)) == Wr.Got{p, rest} : Wr.Dec<W.Pool>}

# LAW wfw_req_round_trip (R1): a request that fits reads back, of either kind
# EXCLUDES: one kind read as the other, a field lost, swapped or misread
law wfw_req_round_trip:
  for +r: FW.Req
  for rest: String
  for h: {wfw_req_fits(r) == True{} : Bool}
  {FW.get_req(FW.put_req(r, rest)) == Wr.Got{r, rest} : Wr.Dec<FW.Req>}

# LAW wfw_admit_round_trip (R1): an admission decision that fits reads back
# EXCLUDES: two decisions with one tag, a reused row's index misread
law wfw_admit_round_trip:
  for +a: W.Admit
  for rest: String
  for h: {wfw_admit_fits(a) == True{} : Bool}
  {FW.get_admit(FW.put_admit(a, rest)) == Wr.Got{a, rest} : Wr.Dec<W.Admit>}

# LAW wfw_decision_round_trip (R1): the reply to an Admit, the decision then the pool, reads back
# EXCLUDES: a reply that drops the pool or puts it before the decision
law wfw_decision_round_trip:
  for +a: W.Admit
  for +p: W.Pool
  for rest: String
  for h: {Bool.and(wfw_admit_fits(a), wfw_pool_fits(p)) == True{} : Bool}
  {FW.get_decision(FW.put_decision((a, p), rest)) == Wr.Got{(a, p), rest} : Wr.Dec<+Sigma<W.Admit, x => W.Pool>>}

# LAW wfw_limits_round_trip (R1): the reply to a Limits request reads back
# EXCLUDES: concurrency and max agents swapped or misread
law wfw_limits_round_trip:
  for +l: W.Limits
  for rest: String
  for h: {wfw_limits_fits(l) == True{} : Bool}
  {FW.get_limits(FW.put_limits(l, rest)) == Wr.Got{l, rest} : Wr.Dec<W.Limits>}

# LAW wfw_answers_admit (R2): an encoded Admit request answers the model's admission, encoded
# EXCLUDES: an entry that decides other than W.admit, or drops a field
#   on the way in or out
law wfw_answers_admit:
  for prior: Maybe<&2, W.Sts>
  for +k: Nat
  for +rows: List<&2, W.Row>
  for p: W.Pool
  for h: {wfw_req_fits(FW.AdmitReq{prior, k, rows, p}) == True{} : Bool}
  {FW.ffi(FW.put_req(FW.AdmitReq{prior, k, rows, p}, "")) == FW.put_decision(W.admit(prior, k, rows, p), "") : String}

# LAW wfw_answers_limits (R2): an encoded Limits request answers the model's limits, encoded
# EXCLUDES: an entry that ignores the cap or the run's size
law wfw_answers_limits:
  for +c: Nat
  for +m: Nat
  for +cap: Nat
  for h: {wfw_req_fits(FW.LimitsReq{c, m, cap}) == True{} : Bool}
  {FW.ffi(FW.put_req(FW.LimitsReq{c, m, cap}, "")) == FW.put_limits(W.effective(W.Limits{c, m}, cap), "") : String}

# LAW wfw_malformed (R3): a malformed request answers the error form
# EXCLUDES: a default answer (a spawn, a limit) for a request it cannot read
law wfw_malformed:
  for +s: String
  for h: {FW.get_req(s) == Wr.Bad{} : Wr.Dec<FW.Req>}
  {FW.ffi(s) == Wr.err("workflow: malformed request") : String}

# LAW wfw_left_over (R3): a request with input left over answers the error form
# EXCLUDES: an entry that answers a request followed by garbage
law wfw_left_over:
  for +r: FW.Req
  for c: Char
  for rest: String
  for h: {wfw_req_fits(r) == True{} : Bool}
  {FW.ffi(FW.put_req(r, SCon{c, rest})) == Wr.err("workflow: input left over") : String}

# LAW wfw_tags_example (R1): anchor: the tags of the header (Sts 0 queued | 1 running | 2 done
# | 3 failed | 4 cancelled | 5 cached; the decision 0 ended | 1 reattach |
# 2 i reuse | 3 spawn | 4 refused)
# EXCLUDES: tags in another order than the grammar's
law wfw_tags_example:
  {FW.put_sts(W.Queued{}, FW.put_sts(W.Running{}, FW.put_sts(W.Finished{}, FW.put_sts(W.Erred{}, FW.put_sts(W.Cancelled{}, FW.put_sts(W.Cached{}, "")))))) == "0,1,2,3,4,5," : String} & {FW.put_admit(W.Ended{}, FW.put_admit(W.Reattach{}, FW.put_admit(W.Reuse{9n}, FW.put_admit(W.Spawn{}, FW.put_admit(W.Refused{}, ""))))) == "0,1,2,9,3,4," : String}

# LAW wfw_prior_example (R1): anchor: a prior status is 0 (none) or 1, then the status
# EXCLUDES: another spelling of a missing prior row
law wfw_prior_example:
  {FW.put_prior(None{}, FW.put_prior(Some{W.Finished{}}, "")) == "0,1,2," : String}

# LAW wfw_row_example (R1): anchor and witness: a row is its key, then its status
# EXCLUDES: a vacuous wfw_row_round_trip, fields in another order
law wfw_row_example:
  {wfw_row_fits(W.Row{3n, W.Erred{}}) == True{} : Bool} & {FW.put_row(W.Row{3n, W.Erred{}}, "") == "3,3," : String}

# LAW wfw_rows_example (R1): anchor and witness: rows are their count, then each row
# EXCLUDES: a vacuous wfw_rows_round_trip
law wfw_rows_example:
  {Bool.and(LawsBase.wire_fits(List.length(&2, W.Row, [W.Row{3n, W.Erred{}}, W.Row{4n, W.Cached{}}])), wfw_rows_fit([W.Row{3n, W.Erred{}}, W.Row{4n, W.Cached{}}])) == True{} : Bool} & {Wr.put_list(~W.Row, ~FW.put_row, [W.Row{3n, W.Erred{}}, W.Row{4n, W.Cached{}}], "") == "2,3,3,4,5," : String}

# LAW wfw_pool_example (R1): anchor and witness: a pool is taken, then left
# EXCLUDES: a vacuous wfw_pool_round_trip, fields in another order
law wfw_pool_example:
  {wfw_pool_fits(W.Pool{1n, 2n}) == True{} : Bool} & {FW.put_pool(W.Pool{1n, 2n}, "") == "1,2," : String}

# LAW wfw_admit_req_example (R1): anchor and witness: an Admit request is 0, prior, key, rows, pool
# EXCLUDES: a vacuous wfw_req_round_trip or wfw_answers_admit, fields in
#   another order
law wfw_admit_req_example:
  {wfw_req_fits(FW.AdmitReq{Some{W.Cached{}}, 7n, [W.Row{3n, W.Erred{}}], W.Pool{1n, 2n}}) == True{} : Bool} & {FW.put_req(FW.AdmitReq{Some{W.Cached{}}, 7n, [W.Row{3n, W.Erred{}}], W.Pool{1n, 2n}}, "") == "0,1,5,7,1,3,3,1,2," : String}

# LAW wfw_limits_req_example (R1): anchor and witness: a Limits request is 1, concurrency, max
# agents, cap
# EXCLUDES: a vacuous wfw_answers_limits, fields in another order
law wfw_limits_req_example:
  {wfw_req_fits(FW.LimitsReq{4n, 9n, 2n}) == True{} : Bool} & {FW.put_req(FW.LimitsReq{4n, 9n, 2n}, "") == "1,4,9,2," : String}

# LAW wfw_admit_example (R1): anchor and witness: a reused row's decision carries its index
# EXCLUDES: a vacuous wfw_admit_round_trip
law wfw_admit_example:
  {wfw_admit_fits(W.Reuse{2n}) == True{} : Bool} & {FW.put_admit(W.Reuse{2n}, "") == "2,2," : String}

# LAW wfw_decision_example (R1): anchor and witness: the reply to an Admit is the decision, then
# the pool
# EXCLUDES: a vacuous wfw_decision_round_trip
law wfw_decision_example:
  {Bool.and(wfw_admit_fits(W.Reuse{2n}), wfw_pool_fits(W.Pool{1n, 0n})) == True{} : Bool} & {FW.put_decision((W.Reuse{2n}, W.Pool{1n, 0n}), "") == "2,2,1,0," : String}

# LAW wfw_limits_example (R1): anchor and witness: the reply to Limits is concurrency, max agents
# EXCLUDES: a vacuous wfw_limits_round_trip
law wfw_limits_example:
  {wfw_limits_fits(W.Limits{2n, 9n}) == True{} : Bool} & {FW.put_limits(W.Limits{2n, 9n}, "") == "2,9," : String}

# LAW wfw_ffi_example (R2): anchor: a run of concurrency 4 and 9 agents capped at 2 runs 2
# at once, 9 agents, end to end
# EXCLUDES: an entry that answers other bytes than the grammar's
law wfw_ffi_example:
  {FW.ffi("1,4,9,2,") == "2,9," : String}

# LAW wfw_malformed_example (R3): witness: a request with an unknown kind is malformed
# EXCLUDES: a vacuous wfw_malformed
law wfw_malformed_example:
  {FW.get_req("2,") == Wr.Bad{} : Wr.Dec<FW.Req>} & {FW.ffi("2,") == Wr.err("workflow: malformed request") : String}

# The spelled laws of the entry: the bytes Rust writes (globals.rs
# `decide`, size.rs `effective_limits`) and reads, spelled here from the
# wire's Wr.put_nat alone, never through the entry's own put_* or get_*
# (a tag that drifts on both sides of the entry, a swapped field or a
# reversed order passes every round trip above). Every input of FW.ffi
# is pinned: a spelled request that fits answers wfw_spell_answer
# (wfw_answers_spelled); the same request with more input after it, the
# left-over error (wfw_left_over_spelled); an input that does not begin
# with a spelled request that fits, the malformed error
# (wfw_malformed_unless_request).

# a row status: queued 0, running 1, done 2, failed 3, cancelled 4,
# cached 5
def wfw_spell_sts(s: W.Sts, rest: String) -> String:
  match s:
    case W.Queued{}:
      Wr.put_nat(0n, rest)
    case W.Running{}:
      Wr.put_nat(1n, rest)
    case W.Finished{}:
      Wr.put_nat(2n, rest)
    case W.Erred{}:
      Wr.put_nat(3n, rest)
    case W.Cancelled{}:
      Wr.put_nat(4n, rest)
    case W.Cached{}:
      Wr.put_nat(5n, rest)

# the prior row's status: 0 none, or 1 then the status
def wfw_spell_prior(m: Maybe<&2, W.Sts>, rest: String) -> String:
  match m:
    case None{}:
      Wr.put_nat(0n, rest)
    case Some{s}:
      Wr.put_nat(1n, wfw_spell_sts(s, rest))

# a row: its key, then its status
def wfw_spell_row(r: W.Row, rest: String) -> String:
  match r:
    case W.Row{k, s}:
      Wr.put_nat(k, wfw_spell_sts(s, rest))

# the rows of rs, each spelled, then rest
def wfw_spell_rows.items(rs: List<&2, W.Row>, rest: String) -> String:
  match rs:
    case Nil{}:
      rest
    case Con{r, t}:
      wfw_spell_row(r, wfw_spell_rows.items(t, rest))

# a list of rows: its count, then each row
def wfw_spell_rows(+rs: List<&2, W.Row>, rest: String) -> String:
  Wr.put_nat(List.length(&2, W.Row, rs), wfw_spell_rows.items(rs, rest))

# a pool: the agents taken, then the agents left
def wfw_spell_pool(p: W.Pool, rest: String) -> String:
  match p:
    case W.Pool{t, l}:
      Wr.put_nat(t, Wr.put_nat(l, rest))

# a request: an Admit is 0, the prior, the key, the rows, the pool; a
# Limits is 1, the concurrency, the max agents, the cap
def wfw_spell_req(q: FW.Req, rest: String) -> String:
  match q:
    case FW.AdmitReq{prior, k, rows, p}:
      Wr.put_nat(0n, wfw_spell_prior(prior, Wr.put_nat(k, wfw_spell_rows(rows, wfw_spell_pool(p, rest)))))
    case FW.LimitsReq{c, m, cap}:
      Wr.put_nat(1n, Wr.put_nat(c, Wr.put_nat(m, Wr.put_nat(cap, rest))))

# a decision: ended 0, reattach 1, reuse 2 then the row's index, spawn 3,
# refused 4
def wfw_spell_admit(a: W.Admit, rest: String) -> String:
  match a:
    case W.Ended{}:
      Wr.put_nat(0n, rest)
    case W.Reattach{}:
      Wr.put_nat(1n, rest)
    case W.Reuse{i}:
      Wr.put_nat(2n, Wr.put_nat(i, rest))
    case W.Spawn{}:
      Wr.put_nat(3n, rest)
    case W.Refused{}:
      Wr.put_nat(4n, rest)

# the reply to an Admit: the decision, then the pool after it
def wfw_spell_decision(d: W.Admit & W.Pool) -> String:
  (a, p) = d
  wfw_spell_admit(a, wfw_spell_pool(p, ""))

# the reply to a Limits: the concurrency, then the max agents
def wfw_spell_limits(l: W.Limits) -> String:
  match l:
    case W.Limits{c, m}:
      Wr.put_nat(c, Wr.put_nat(m, ""))

# the spelled reply to the request q: the model's admission (W.admit,
# pinned by the wf_* laws above) or the run's limits (W.effective)
def wfw_spell_answer(q: FW.Req) -> String:
  match q:
    case FW.AdmitReq{prior, k, rows, p}:
      wfw_spell_decision(W.admit(prior, k, rows, p))
    case FW.LimitsReq{c, m, cap}:
      wfw_spell_limits(W.effective(W.Limits{c, m}, cap))

# LAW wfw_answers_spelled: a request spelled by the grammar, every number within the wire, is
# answered with the grammar's spelling of the model's answer: to an Admit
# the decision of W.admit (ended 0, reattach 1, reuse 2 then the row,
# spawn 3, refused 4) then the pool after it (taken, left); to a Limits
# the concurrency then the max agents of W.effective
# EXCLUDES: a kind, prior, status or decision tag that drifts from the
#   grammar Rust reads and writes (swapped on both sides of the entry
#   alike), a field lost, swapped or defaulted, a reply in another order
law wfw_answers_spelled:
  for +q: FW.Req
  for fits: {wfw_req_fits(q) == True{} : Bool}
  {FW.ffi(wfw_spell_req(q, "")) == wfw_spell_answer(q) : String}

# LAW wfw_left_over_spelled: a spelled request that fits, followed by any more input, answers
# the error form "workflow: input left over"
# EXCLUDES: trailing input ignored, or read as part of the request, or
#   answered with another error text
law wfw_left_over_spelled:
  for +q: FW.Req
  for fits: {wfw_req_fits(q) == True{} : Bool}
  for +c: Char
  for +rest: String
  {FW.ffi(wfw_spell_req(q, SCon{c, rest})) == Wr.err("workflow: input left over") : String}

# LAW wfw_unknown_kind: a request kind tag of 2 or more (of any length) answers the error
# form "workflow: malformed request", whatever follows
# EXCLUDES: an unknown kind read as an Admit or a Limits
law wfw_unknown_kind:
  for +n: Nat
  for +rest: String
  {FW.ffi(Wr.put_nat(2n+n, rest)) == Wr.err("workflow: malformed request") : String}

# LAW wfw_unknown_prior: an Admit whose prior tag is 2 or more (of any length) answers the
# error form "workflow: malformed request", whatever follows
# EXCLUDES: an unknown prior tag read as none or as some status
law wfw_unknown_prior:
  for +n: Nat
  for +rest: String
  {FW.ffi(Wr.put_nat(0n, Wr.put_nat(2n+n, rest))) == Wr.err("workflow: malformed request") : String}

# LAW wfw_unknown_prior_sts: an Admit whose prior status tag is 6 or more (of any length)
# answers the error form "workflow: malformed request", whatever follows
# EXCLUDES: an unknown status read as a known one
law wfw_unknown_prior_sts:
  for +n: Nat
  for +rest: String
  {FW.ffi(Wr.put_nat(0n, Wr.put_nat(1n, Wr.put_nat(6n+n, rest)))) == Wr.err("workflow: malformed request") : String}

# LAW wfw_unknown_row_sts: an Admit with a spelled prior, a key and a row count of one or
# more that fit, whose first row has a key that fits and a status tag of
# 6 or more (of any length), answers the error form "workflow: malformed
# request", whatever follows
# EXCLUDES: an unknown row status read as a known one, or the row skipped
law wfw_unknown_row_sts:
  for +m: Maybe<&2, W.Sts>
  for +k: Nat
  for +c: Nat
  for +key: Nat
  for fits: {Bool.and(LawsBase.wire_fits(k), Bool.and(LawsBase.wire_fits(1n+c), LawsBase.wire_fits(key))) == True{} : Bool}
  for +n: Nat
  for +rest: String
  {FW.ffi(Wr.put_nat(0n, wfw_spell_prior(m, Wr.put_nat(k, Wr.put_nat(1n+c, Wr.put_nat(key, Wr.put_nat(6n+n, rest))))))) == Wr.err("workflow: malformed request") : String}

# LAW wfw_reads_only_requests: an answer that is not the error form answers a request: the
# input is exactly the spelling of a request whose numbers fit the wire,
# and the answer is the spelled reply of the model on it
# EXCLUDES: a decoder that accepts an unknown tag (kind, prior, status), a
#   missing or extra field or row, a count larger than the rows, or input
#   left over, and answers it anyway (a default instead of the error form)
law wfw_reads_only_requests:
  for +s: String
  for ok: {LawsBase.wire_opens_err(FW.ffi(s)) == False{} : Bool}
  exs q: FW.Req
  {(s, (wfw_req_fits(q), FW.ffi(s))) == (wfw_spell_req(q, ""), (True{}, wfw_spell_answer(q))) : String & (Bool & String)}

# LAW wfw_malformed_unless_request: every answer but the error form "workflow: malformed request"
# comes from an input that begins with a spelled request that fits
# EXCLUDES: the left-over error (or any answer) for input that does not
#   begin with a request, the malformed error spelled with another text
law wfw_malformed_unless_request:
  for +s: String
  for other: {String.eq(FW.ffi(s), Wr.err("workflow: malformed request")) == False{} : Bool}
  exs q: FW.Req
  exs rest: String
  {(s, wfw_req_fits(q)) == (wfw_spell_req(q, rest), True{}) : String & Bool}

# LAW wfw_reader_unknown_decision: the model of the Rust reader of a reply (FW.get_admit, not
# run in production) refuses a decision tag of 5 or more, as Rust's
# `tag_of(5, "an admission")` does in globals.rs `decide`
# EXCLUDES: a reader model that reads an unknown decision as a known one
#   (its round trip laws hold all the same)
law wfw_reader_unknown_decision:
  for +n: Nat
  for +rest: String
  {FW.get_admit(Wr.put_nat(5n+n, rest)) == Wr.Bad{} : Wr.Dec<W.Admit>}

# LAW wfw_ffi_tags_example: anchor: the bytes Rust sends and reads: a new call (no prior,
# key 7, no rows) spawns while an agent is left (3 then the pool 1 taken,
# 2 left) and is refused when none is (4); a row of key 7 failed then
# cached reuses row 1, queued then done reuses row 1, cancelled then
# running reuses none; a prior queued or running reattaches (1), done,
# failed, cancelled or cached ends (0); a Limits of 4 and 9 capped at 2
# is 2 and 9, uncapped 4 and 9; an empty input, kind 2, prior tag 2,
# status 6 (prior or row), a missing cap and a leading zero are
# malformed; a whole request with input after it is left over
# EXCLUDES: a tag table both sides of the Bend entry agree on but Rust
#   does not, an unknown tag read as a known one, a reply in another order
law wfw_ffi_tags_example:
  {[FW.ffi("0,0,7,0,0,3,"), FW.ffi("0,0,7,0,2,0,"), FW.ffi("0,0,7,2,7,3,7,5,0,3,"), FW.ffi("0,0,7,2,7,0,7,2,0,0,"), FW.ffi("0,0,7,2,7,4,7,1,0,0,"), FW.ffi("0,1,0,7,0,0,3,"), FW.ffi("0,1,1,7,0,0,3,"), FW.ffi("0,1,2,7,0,0,3,"), FW.ffi("0,1,3,7,0,0,3,"), FW.ffi("0,1,4,7,0,0,3,"), FW.ffi("0,1,5,7,0,0,3,"), FW.ffi("1,4,9,2,"), FW.ffi("1,4,9,0,")] == ["3,1,2,", "4,2,0,", "2,1,0,3,", "2,1,0,0,", "4,0,0,", "1,0,3,", "1,0,3,", "0,0,3,", "0,0,3,", "0,0,3,", "0,0,3,", "2,9,", "4,9,"] : List<&2, String>} & {[FW.ffi(""), FW.ffi("2,0,"), FW.ffi("0,2,7,0,0,3,"), FW.ffi("0,1,6,7,0,0,3,"), FW.ffi("0,0,7,1,7,6,0,3,"), FW.ffi("1,4,9,"), FW.ffi("1,04,9,2,"), FW.ffi("1,4,9,2,x"), FW.ffi("0,0,7,0,0,3,0,")] == [Wr.err("workflow: malformed request"), Wr.err("workflow: malformed request"), Wr.err("workflow: malformed request"), Wr.err("workflow: malformed request"), Wr.err("workflow: malformed request"), Wr.err("workflow: malformed request"), Wr.err("workflow: malformed request"), Wr.err("workflow: input left over"), Wr.err("workflow: input left over")] : List<&2, String>}
