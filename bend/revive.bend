# revive: the model of the busy evidence of a long run (docs/daemon.md
# D1). The Rust code is the worker's busy refresh (crates/eukhe-daemon/
# src/worker.rs, every `timeouts::BUSY_REFRESH_MS`) and
# `revival_gate::busy_evidence_fresh`; the bridge (bend/bridge_revive.bend,
# crates/eukhe-daemon/src/supervision_bridge.rs) runs both on the same runs.
#
# A run records busy evidence at its start and again every h ms while it
# runs (a refresh). The worker crashes c ms into the run; a boot follows d
# ms after the crash. The evidence is fresh at the boot when its age is at
# most the max age m. A run may take any time: the age counts from the
# last refresh.

import Base

def tick.put(at: Bool, r: Nat) -> Nat:
  match at:
    case True{}:
      0n
    case False{}:
      1n+r

# one ms of the run: r ms since the last record become r + 1, or 0 when
# the refresh is due (a refresh every h ms)
def tick(+h: Nat, +r: Nat) -> Nat:
  tick.put(Nat.is_eq(1n+r, h), r)

# the ms since the last record, c ms into a run whose last record was r
# ms ago
def since(c: Nat, +h: Nat, r: Nat) -> Nat:
  match c:
    case 0n:
      r
    case 1n+p:
      since(p, h, tick(h, r))

# the evidence's age at a boot d ms after a crash c ms into a run
def age(+h: Nat, c: Nat, d: Nat) -> Nat:
  Nat.add(since(c, h, 0n), d)

# the evidence of age a revives, with the max age m
def fresh(m: Nat, a: Nat) -> Bool:
  Nat.is_le(a, m)
