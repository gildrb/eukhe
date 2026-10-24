# infer_threshold: which compaction threshold one request's context is
# over (bend/infer.bend section 5, early compaction, as the harness asks it
# per request: crates/eukhe-durable generation.rs `threshold_compaction`).
# The limit is L = window - reserve; the code compares strictly, so a
# context of t tokens (a whole count) is over the limit when t >= L + 1
# and, with a margin m > 0, over the background threshold when
# t >= L - m + 1: the thresholds `first_at` reads. Reserve and margin are
# whole numbers of tokens with a sign (Rust rounds each up at the
# boundary). laws/infer_threshold.bend pins `over` to `t + reserve >
# window` and `t + reserve + margin > window`, and that the first request
# over each threshold is `first_at`'s; bend/ffi_infer_threshold.bend runs
# it as the compiled core. The arithmetic never adds more than two wire
# numbers, so it stays below the runtime's 2^48 - 1.

import Base

# a whole number with a sign: Up{n} is n, Down{n} is -(1+n) (one spelling
# each)
type Z is Data:
  Up{n: Nat}
  Down{n: Nat}

# which threshold a context is over
type Over is Data:
  Under{}   # none: no compaction
  Early{}   # the background threshold: compaction runs beside the request
  Blocks{}  # the blocking threshold: the request waits for compaction

# L + 1 = window - reserve + 1, at least 0: the first whole token count
# over the limit
def limit_at(w: Nat, r: Z) -> Nat:
  match r:
    case Up{a}:
      Nat.sub(1n+w, a)
    case Down{a}:
      Nat.add(2n+a, w)

def over.early(early: Bool) -> Over:
  match early:
    case True{}:
      Early{}
    case False{}:
      Under{}

# under the limit: over the background threshold L - m + 1 when the
# margin m is positive
def over.margin(+lim: Nat, t: Nat, m: Z) -> Over:
  match m:
    case Up{c}:
      match c:
        case 0n:
          Under{}
        case 1n+b:
          over.early(Nat.is_le(Nat.sub(lim, 1n+b), t))
    case Down{c}:
      Under{}

def over.at(blocks: Bool, +lim: Nat, t: Nat, m: Z) -> Over:
  match blocks:
    case True{}:
      Blocks{}
    case False{}:
      over.margin(lim, t, m)

# the threshold a context of t tokens is over, with compaction on (or
# off), a window of w tokens (0: unknown), reserve r and margin m
def over(on: Bool, +t: Nat, w: Nat, r: Z, m: Z) -> Over:
  match on:
    case False{}:
      Under{}
    case True{}:
      match w:
        case 0n:
          Under{}
        case 1n+v:
          +lim = limit_at(1n+v, r)
          over.at(Nat.is_le(lim, t), lim, t, m)
