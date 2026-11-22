# eukhe: the proof of LAW rec_again_counts_the_rounds
#
# PROOF: by cases on `same` and on whether the hashes are equal.

import Base
import ../../bend/run/recovery.bend as RnRecovery
import ../../laws/run/recover.bend as RunRecover

def rag.zero(eq: Bool) -> {1n == RunRecover.rounds.eq(eq, 0n) : Nat}:
  match eq:
    case True{}:
      {==}
    case False{}:
      {==}

def rag.more(eq: Bool, -k: Nat) -> {RnRecovery.again.eq(eq, k) == RunRecover.rounds.eq(eq, 1n+k) : Nat}:
  match eq:
    case True{}:
      {==}
    case False{}:
      {==}

def RunRecover.rec_again_counts_the_rounds(same, last, h):
  match same:
    case 0n:
      rag.zero(Nat.is_eq(last, h))
    case 1n+k:
      rag.more(Nat.is_eq(last, h), k)
