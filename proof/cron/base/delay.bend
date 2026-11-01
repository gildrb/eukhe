# eukhe: a lemma the proofs of area cron share: the model's pause in
# minutes is the spec's table.

import Base
import ../../../bend/cron.bend as Cr
import ../../../laws/cron_store.bend as CronStore

def creq.delay(k: Nat) -> {Cr.delay(k) == CronStore.pause_min_spec(k) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n:
      {==}
    case 2n:
      {==}
    case 3n:
      {==}
    case 4n:
      {==}
    case 5n:
      {==}
    case 6n+r:
      {==}
