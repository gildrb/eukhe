# infer_threshold: which compaction threshold one request's context is
# over (bend/infer.bend section 5, early compaction, as the harness asks it
# per request: crates/eukhe-durable generation.rs `threshold_compaction`),
# and where a compaction cuts the transcript (`plan`). The limit is
# L = window - reserve; the code compares strictly, so a context of t
# tokens (a whole count) is over the limit when t >= L + 1 and, with a
# margin m > 0, over the background threshold when t >= L - m + 1: the
# thresholds `first_at` reads. Reserve and margin are whole numbers of
# tokens with a sign (Rust rounds each up at the boundary).
# laws/infer_threshold.bend pins `over` to `t + reserve > window` and
# `t + reserve + margin > window`, that the first request over each
# threshold is `first_at`'s, and the cut and the hysteresis of `plan`;
# bend/ffi_infer_threshold.bend runs `plan` as the compiled core. The
# arithmetic never adds more than the sizes of one transcript, so it stays
# below the runtime's 2^48 - 1.

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

# The cut and the hysteresis
# --------------------------
# A compaction summarizes the transcript before its cut and keeps the
# entries after it. Rust sends the entries after the head newest first,
# as their sizes in tokens (calibrated on the provider's counts; system
# entries count 0: a compaction writes the system prompt again), the
# places a cut may keep from (`cuts`: k keeps the k newest entries) and
# `full`: the k at which nothing would be left to summarize (the oldest
# entry with a message is the full-th newest; 0: none). What a cut
# cannot remove is the base: the context's tokens less the entries'.
#
# The target is half the first context over any threshold. A compaction
# keeps the most entries that keep base + kept within the target and
# within `keep` (the policy's keepRecentTokens); when no cut fits, the
# newest cut (the least it can keep). So a compaction leaves the context
# at the target, below every threshold, and the next one waits until the
# context grows past a threshold again. A context over the background
# threshold compacts early only when its compaction reaches the target:
# else it would compact again at the next turn, and the blocking
# threshold compacts it when it must.

# the first whole count over any threshold of a window w > 0: L + 1, or
# L + 1 - c with a margin c > 0 (at least 0)
def start(w: Nat, r: Z, m: Z) -> Nat:
  match m:
    case Up{c}:
      Nat.sub(limit_at(w, r), c)
    case Down{c}:
      limit_at(w, r)

# the size a compaction brings the context down to: half the start
def target(w: Nat, r: Z, m: Z) -> Nat:
  Nat.div(start(w, r, m), 2n)

def least(a: Nat, b: Nat, le: Bool) -> Nat:
  match le:
    case True{}:
      a
    case False{}:
      b

# the tokens the kept entries may hold: keep, and with a known window at
# most what the target leaves over the base
def budget(w: Nat, r: Z, m: Z, +keep: Nat, base: Nat) -> Nat:
  match w:
    case 0n:
      keep
    case 1n+v:
      +room = Nat.sub(target(1n+v, r, m), base)
      least(keep, room, Nat.is_le(keep, room))

# k is one of cuts
def has(cuts: List<&2, Nat>, +k: Nat) -> Bool:
  match cuts:
    case Nil{}:
      False{}
    case c <> rest:
      Bool.or(Nat.is_eq(c, k), has(rest, k))

# the sum of sizes
def total(xs: List<&2, Nat>) -> Nat:
  match xs:
    case Nil{}:
      0n
    case x <> rest:
      Nat.add(x, total(rest))

# the tokens the k newest entries hold
def kept(xs: List<&2, Nat>, k: Nat) -> Nat:
  match xs:
    case Nil{}:
      0n
    case x <> rest:
      match k:
        case 0n:
          0n
        case 1n+j:
          Nat.add(x, kept(rest, j))

def newest.end(hit: Bool, k: Nat) -> Maybe<&2, Nat>:
  match hit:
    case True{}:
      Some{k}
    case False{}:
      None{}

# the newest cut that keeps k or more, k kept so far (hit: k is a cut),
# xs the older entries
def newest(xs: List<&2, Nat>, +cuts: List<&2, Nat>, +k: Nat, hit: Bool) -> Maybe<&2, Nat>:
  match xs:
    case Nil{}:
      newest.end(hit, k)
    case x <> rest:
      match hit:
        case True{}:
          Some{k}
        case False{}:
          newest(rest, cuts, 1n+k, has(cuts, 1n+k))

def walk.cut(c: Bool, +k: Nat, best: Maybe<&2, Nat>) -> Maybe<&2, Nat>:
  match c:
    case True{}:
      Some{k}
    case False{}:
      best

# the walk once it passed the budget at the entry that keeps k: the best
# cut so far, else the newest cut (none fits), xs the entries after it
def walk.over(best: Maybe<&2, Nat>, xs: List<&2, Nat>, +cuts: List<&2, Nat>, +k: Nat) -> Maybe<&2, Nat>:
  match best:
    case None{}:
      newest(xs, cuts, k, has(cuts, k))
    case Some{j}:
      Some{j}

# the newest entry of xs keeps the walk within b: acc + x <= b
def walk.fits(xs: List<&2, Nat>, +b: Nat, acc: Nat) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case x <> rest:
      Nat.is_le(Nat.add(acc, x), b)

# the walk from the newest entry: acc the tokens of the k entries kept so
# far, best the oldest cut within the budget b so far, fits: the next
# entry stays within b; the sizes are whole, so once past b every older
# cut is past it too
def walk(xs: List<&2, Nat>, +cuts: List<&2, Nat>, +b: Nat, acc: Nat, +k: Nat, best: Maybe<&2, Nat>, fits: Bool) -> Maybe<&2, Nat>:
  match xs:
    case Nil{}:
      best
    case x <> +rest:
      match fits:
        case True{}:
          +a = Nat.add(acc, x)
          walk(rest, cuts, b, a, 1n+k, walk.cut(has(cuts, 1n+k), 1n+k, best), walk.fits(rest, b, a))
        case False{}:
          walk.over(best, rest, cuts, 1n+k)

def cut.left.at(lt: Bool, k: Nat) -> Maybe<&2, Nat>:
  match lt:
    case True{}:
      Some{k}
    case False{}:
      None{}

# a cut that keeps k leaves something to summarize when k < full
def cut.left(c: Maybe<&2, Nat>, full: Nat) -> Maybe<&2, Nat>:
  match c:
    case None{}:
      None{}
    case Some{+k}:
      cut.left.at(Nat.is_lt(k, full), k)

# the cut within the budget b: how many of the newest entries it keeps
def cut(+xs: List<&2, Nat>, +cuts: List<&2, Nat>, +b: Nat, full: Nat) -> Maybe<&2, Nat>:
  cut.left(walk(xs, cuts, b, 0n, 0n, None{}, walk.fits(xs, b, 0n)), full)

# The plan of one request: the threshold it compacts at, and the cut
type Plan is Data:
  Plan{over: Over, cut: Maybe<&2, Nat>}

def Plan.over(p: Plan) -> Over:
  match p:
    case Plan{o, c}:
      o

def Plan.cut(p: Plan) -> Maybe<&2, Nat>:
  match p:
    case Plan{o, c}:
      c

# an early compaction runs when its cut reaches the target
def early.reach(c: Maybe<&2, Nat>, xs: List<&2, Nat>, base: Nat, tgt: Nat) -> Over:
  match c:
    case None{}:
      Under{}
    case Some{k}:
      over.early(Nat.is_le(Nat.add(base, kept(xs, k)), tgt))

# a threshold compacts only with a cut; the background one only when the
# cut reaches the target
def gate(o: Over, c: Maybe<&2, Nat>, xs: List<&2, Nat>, base: Nat, tgt: Nat) -> Over:
  match o:
    case Under{}:
      Under{}
    case Early{}:
      early.reach(c, xs, base, tgt)
    case Blocks{}:
      match c:
        case None{}:
          Under{}
        case Some{k}:
          Blocks{}

# the plan for a context of t tokens, compaction on (or off), window w (0:
# unknown), reserve r, margin m, keepRecentTokens keep, the entries after
# the head newest first (sizes xs, cuts, full)
def plan(on: Bool, +t: Nat, +w: Nat, +r: Z, +m: Z, +keep: Nat, full: Nat, +xs: List<&2, Nat>, +cuts: List<&2, Nat>) -> Plan:
  +base = Nat.sub(t, total(xs))
  +c = cut(xs, cuts, budget(w, r, m, keep, base), full)
  Plan{gate(over(on, t, w, r, m), c, xs, base, target(w, r, m)), c}
