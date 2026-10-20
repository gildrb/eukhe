# LAWS (WF, dynamic workflows): a run never holds more agents at once
# than its concurrency, never spawns more than its budget, spawns only
# the uncached keys when it resumes, and one failed agent never changes
# its siblings' results. Each law is an open claim about the model in
# bend/workflow.bend; PROOF.bend proves them (as Wf.<law>) with the
# lemmas of bend/proof_workflow.bend. The Rust bridge test
# (crates/eukhe-core/src/durable/workflow/bridge.rs) runs `admit` and
# `effective_limits` against bend/bridge_workflow.bend.

import Base
import ../bend/workflow.bend as W

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
