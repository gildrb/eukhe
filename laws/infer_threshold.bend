# eukhe: the laws of area infer_threshold

import Base
import ../bend/infer.bend as If
import ../bend/infer_threshold.bend as M
import ../bend/ffi_infer_threshold.bend as FT
import ../bend/wire.bend as Wr
import ./base.bend as LawsBase

# (S6.6) Early compaction, one request at a time
# ----------------------------------------------
# The model `first_at` in bend/infer.bend section
# 5; the harness asks the compiled core (bend/ffi_infer_threshold.bend)
# which threshold each request's context is over and where a compaction
# cuts (`plan`). Every input is free: compaction on or off, any token
# count, window, reserve, margin, keepRecentTokens, sizes and cuts.

# The decision, independently, on whole numbers: with compaction on and
# a window w > 0, a context of t tokens is over the blocking threshold
# when t + reserve > w (the code compares strictly), else over the
# background threshold when the margin is positive and t + reserve +
# margin > w, else over none; with compaction off or the window unknown
# (0) over none. A reserve or margin Up{n} is n, Down{n} is -(1+n).

# t + r > w
def above(t: Nat, r: M.Z, w: Nat) -> Bool:
  match r:
    case M.Up{a}:
      Nat.is_lt(w, Nat.add(a, t))
    case M.Down{a}:
      Nat.is_lt(Nat.add(1n+a, w), t)

# t + r + c > w, for a margin c > 0
def above_by(t: Nat, r: M.Z, c: Nat, w: Nat) -> Bool:
  match r:
    case M.Up{a}:
      Nat.is_lt(w, Nat.add(a, Nat.add(c, t)))
    case M.Down{a}:
      Nat.is_lt(Nat.add(1n+a, w), Nat.add(c, t))

def over_spec.early(b: Bool) -> M.Over:
  match b:
    case True{}:
      M.Early{}
    case False{}:
      M.Under{}

def over_spec.margin(+t: Nat, +r: M.Z, m: M.Z, +w: Nat) -> M.Over:
  match m:
    case M.Up{c}:
      match c:
        case 0n:
          M.Under{}
        case 1n+b:
          over_spec.early(above_by(t, r, 1n+b, w))
    case M.Down{c}:
      M.Under{}

def over_spec.on(blocks: Bool, +t: Nat, +r: M.Z, m: M.Z, +w: Nat) -> M.Over:
  match blocks:
    case True{}:
      M.Blocks{}
    case False{}:
      over_spec.margin(t, r, m, w)

def over_spec(on: Bool, +t: Nat, w: Nat, +r: M.Z, m: M.Z) -> M.Over:
  match on:
    case False{}:
      M.Under{}
    case True{}:
      match w:
        case 0n:
          M.Under{}
        case 1n++v:
          over_spec.on(above(t, r, 1n+v), t, r, m, 1n+v)

# LAW infer_threshold_over_exact: the threshold a context is over is exactly: none with compaction off or the window unknown; blocking when tokens + reserve > window; else background when the margin is positive and tokens + reserve + margin > window; else none
law infer_threshold_over_exact:
  for on: Bool
  for +t: Nat
  for w: Nat
  for +r: M.Z
  for m: M.Z
  {M.over(on, t, w, r, m) == over_spec(on, t, w, r, m) : M.Over}

# the threshold `first_at` reads for the limit window - r: the least whole
# count over it, at least 0
def lim_spec(w: Nat, r: M.Z) -> Nat:
  match r:
    case M.Up{a}:
      Nat.sub(1n+w, a)
    case M.Down{a}:
      Nat.add(2n+a, w)

def is_blocks(o: M.Over) -> Bool:
  match o:
    case M.Blocks{}:
      True{}
    case M.Early{}:
      False{}
    case M.Under{}:
      False{}

def is_over(o: M.Over) -> Bool:
  match o:
    case M.Blocks{}:
      True{}
    case M.Early{}:
      True{}
    case M.Under{}:
      False{}

# the first context of xs is over the blocking threshold (b) or any
# threshold
def head.blocks(xs: List<&2, Nat>, +w: Nat, +r: M.Z, +m: M.Z) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case x <> rest:
      is_blocks(M.over(True{}, x, w, r, m))

def head.over(xs: List<&2, Nat>, +w: Nat, +r: M.Z, +m: M.Z) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case x <> rest:
      is_over(M.over(True{}, x, w, r, m))

# the requests of a run as the harness asks them, the first at index i:
# the index of the first over the blocking threshold (hit: the first of
# xs is), or over any threshold
def first_blocks(xs: List<&2, Nat>, +i: Nat, +w: Nat, +r: M.Z, +m: M.Z, hit: Bool) -> Maybe<&2, Nat>:
  match xs:
    case Nil{}:
      None{}
    case x <> +rest:
      match hit:
        case True{}:
          Some{i}
        case False{}:
          first_blocks(rest, 1n+i, w, r, m, head.blocks(rest, w, r, m))

def first_over(xs: List<&2, Nat>, +i: Nat, +w: Nat, +r: M.Z, +m: M.Z, hit: Bool) -> Maybe<&2, Nat>:
  match xs:
    case Nil{}:
      None{}
    case x <> +rest:
      match hit:
        case True{}:
          Some{i}
        case False{}:
          first_over(rest, 1n+i, w, r, m, head.over(rest, w, r, m))

# LAW infer_threshold_blocks_steps: over a run of requests (context sizes xs), with a known window, the first the entry finds over the blocking threshold is `first_at` at the limit window - reserve + 1, whatever the margin
law infer_threshold_blocks_steps:
  for +xs: List<&2, Nat>
  for +v: Nat
  for +r: M.Z
  for +m: M.Z
  {first_blocks(xs, 0n, 1n+v, r, m, head.blocks(xs, 1n+v, r, m)) == If.first_at(xs, lim_spec(1n+v, r), 0n) : Maybe<&2, Nat>}

# LAW infer_threshold_early_steps: with a positive margin c, the first request the entry finds over any threshold is `first_at` at the background threshold window - reserve - c + 1: so every law of `first_at` (compact_starts_early) holds for them
law infer_threshold_early_steps:
  for +xs: List<&2, Nat>
  for +v: Nat
  for +r: M.Z
  for +b: Nat
  {first_over(xs, 0n, 1n+v, r, M.Up{1n+b}, head.over(xs, 1n+v, r, M.Up{1n+b})) == If.first_at(xs, Nat.sub(lim_spec(1n+v, r), 1n+b), 0n) : Maybe<&2, Nat>}

# (S6.6b) After the turn
# ----------------------
# A compaction runs once the context actually crossed a threshold: the
# thresholds read the tokens the last turn reached (the provider's count
# of the newest answer since the last compaction), never the request
# about to go. The request only has to stay within the hard window: with
# compaction on and a window w > 0 it blocks when t > w, or t + reserve >
# w with a negative reserve (a request never outgrows the window, nor the
# limit a negative reserve sets past it).

# t > w, or t + r > w with a negative reserve r
def past_spec(t: Nat, r: M.Z, w: Nat) -> Bool:
  match r:
    case M.Up{a}:
      Nat.is_lt(w, t)
    case M.Down{a}:
      Nat.is_lt(Nat.add(1n+a, w), t)

def due_spec.at(past: Bool, +last: Nat, +r: M.Z, m: M.Z, +w: Nat) -> M.Over:
  match past:
    case True{}:
      M.Blocks{}
    case False{}:
      over_spec(True{}, last, w, r, m)

# the threshold a request of t tokens compacts at, after a turn that
# reached last tokens
def due_spec(on: Bool, +t: Nat, +last: Nat, w: Nat, +r: M.Z, m: M.Z) -> M.Over:
  match on:
    case False{}:
      M.Under{}
    case True{}:
      match w:
        case 0n:
          M.Under{}
        case 1n++v:
          due_spec.at(past_spec(t, r, 1n+v), last, r, m, 1n+v)

# (S6.7) The cut and the hysteresis
# ---------------------------------
# The entries after the head come newest first: their sizes xs (Rust
# calibrates them on the provider's counts), the cuts (k keeps the k
# newest entries) and full (a cut keeping k leaves something to summarize
# when k < full). The base is what no cut removes: t less the sizes. The
# target is half the start, the first context over any threshold: the
# least whole count over the limit window - reserve, less a positive
# margin. A compaction keeps the most entries whose tokens stay within
# keepRecentTokens and keep base + kept within the target; when no cut
# does, the newest cut. The threshold is the one the request compacts at
# (S6.6b); it compacts only with a cut, the background one only when its
# cut reaches the target.

# the tokens of the k newest of xs
def held(k: Nat, xs: List<&2, Nat>) -> Nat:
  match k:
    case 0n:
      0n
    case 1n+j:
      match xs:
        case Nil{}:
          0n
        case x <> rest:
          Nat.add(held(j, rest), x)

# the tokens of all of xs
def sum(xs: List<&2, Nat>) -> Nat:
  match xs:
    case Nil{}:
      0n
    case x <> rest:
      Nat.add(sum(rest), x)

def mem.at(eq: Bool, rest: Bool) -> Bool:
  match eq:
    case True{}:
      True{}
    case False{}:
      rest

# k is in cuts
def mem(cuts: List<&2, Nat>, +k: Nat) -> Bool:
  match cuts:
    case Nil{}:
      False{}
    case c <> rest:
      mem.at(Nat.is_eq(c, k), mem(rest, k))

# k is a cut of n entries: 1 <= k <= n, and in cuts
def is_cut(cuts: List<&2, Nat>, +n: Nat, +k: Nat) -> Bool:
  Bool.and(Nat.is_lt(0n, k), Bool.and(Nat.is_le(k, n), mem(cuts, k)))

def fit_spec.at(ok: Bool, +k: Nat, rest: Maybe<&2, Nat>) -> Maybe<&2, Nat>:
  match ok:
    case True{}:
      Some{k}
    case False{}:
      rest

# the largest cut k <= j of the n entries xs whose tokens are within b
def fit_spec(+xs: List<&2, Nat>, +cuts: List<&2, Nat>, +n: Nat, +b: Nat, j: Nat) -> Maybe<&2, Nat>:
  match j:
    case 0n:
      None{}
    case 1n++i:
      fit_spec.at(Bool.and(is_cut(cuts, n, 1n+i), Nat.is_le(held(1n+i, xs), b)), 1n+i, fit_spec(xs, cuts, n, b, i))

# the least cut of n entries among k, k + 1, ... k + d - 1
def least_cut(d: Nat, +cuts: List<&2, Nat>, +n: Nat, +k: Nat) -> Maybe<&2, Nat>:
  match d:
    case 0n:
      None{}
    case 1n+e:
      fit_spec.at(is_cut(cuts, n, k), k, least_cut(e, cuts, n, 1n+k))

def or_else(a: Maybe<&2, Nat>, b: Maybe<&2, Nat>) -> Maybe<&2, Nat>:
  match a:
    case None{}:
      b
    case Some{k}:
      Some{k}

def left_spec(c: Maybe<&2, Nat>, +full: Nat) -> Maybe<&2, Nat>:
  match c:
    case None{}:
      None{}
    case Some{+k}:
      fit_spec.at(Nat.is_lt(k, full), k, None{})

# the newest cut of xs: the least
def newest_spec(+xs: List<&2, Nat>, +cuts: List<&2, Nat>) -> Maybe<&2, Nat>:
  +n = List.length(&2, Nat, xs)
  least_cut(n, cuts, n, 1n)

# the cut within the budget b: the largest cut within b, else the
# newest cut, kept only when something is left to summarize
def cut_spec(+xs: List<&2, Nat>, +cuts: List<&2, Nat>, +b: Nat, +full: Nat) -> Maybe<&2, Nat>:
  +n = List.length(&2, Nat, xs)
  left_spec(or_else(fit_spec(xs, cuts, n, b, n), newest_spec(xs, cuts)), full)

# the first context over any threshold of a window w > 0
def start_spec(+w: Nat, +r: M.Z, m: M.Z) -> Nat:
  match m:
    case M.Up{c}:
      Nat.sub(lim_spec(w, r), c)
    case M.Down{c}:
      lim_spec(w, r)

# the target: half the start
def target_spec(+w: Nat, +r: M.Z, m: M.Z) -> Nat:
  Nat.div(start_spec(w, r, m), 2n)

def budget_spec.min(le: Bool, a: Nat, b: Nat) -> Nat:
  match le:
    case True{}:
      a
    case False{}:
      b

# what the kept entries may hold: keep, and with a window at most the
# target less the base
def budget_spec(w: Nat, +r: M.Z, m: M.Z, +keep: Nat, +base: Nat) -> Nat:
  match w:
    case 0n:
      keep
    case 1n+v:
      +room = Nat.sub(target_spec(1n+v, r, m), base)
      budget_spec.min(Nat.is_le(keep, room), keep, room)

def reach_spec.at(le: Bool) -> M.Over:
  match le:
    case True{}:
      M.Early{}
    case False{}:
      M.Under{}

def reach_spec(c: Maybe<&2, Nat>, +xs: List<&2, Nat>, +base: Nat, +tgt: Nat) -> M.Over:
  match c:
    case None{}:
      M.Under{}
    case Some{k}:
      reach_spec.at(Nat.is_le(Nat.add(base, held(k, xs)), tgt))

def gate_spec(o: M.Over, c: Maybe<&2, Nat>, +xs: List<&2, Nat>, +base: Nat, +tgt: Nat) -> M.Over:
  match o:
    case M.Under{}:
      M.Under{}
    case M.Early{}:
      reach_spec(c, xs, base, tgt)
    case M.Blocks{}:
      match c:
        case None{}:
          M.Under{}
        case Some{k}:
          M.Blocks{}

# the plan, independently
def plan_spec(on: Bool, +t: Nat, +last: Nat, +w: Nat, +r: M.Z, +m: M.Z, +keep: Nat, +full: Nat, +xs: List<&2, Nat>, +cuts: List<&2, Nat>) -> M.Plan:
  +base = Nat.sub(t, sum(xs))
  +c = cut_spec(xs, cuts, budget_spec(w, r, m, keep, base), full)
  M.Plan{gate_spec(due_spec(on, t, last, w, r, m), c, xs, base, target_spec(w, r, m)), c}

# LAW infer_threshold_plan_exact: the plan of every request is exactly: the cut keeps the largest number of the newest entries that is a cut and whose tokens stay within keepRecentTokens and (with a known window) the target less the request's base, else the newest cut, and none when that leaves nothing to summarize; the threshold is blocking for a request past the hard window, else the one the context the last turn reached is over, kept only with a cut, and the background one only when its cut brings base + kept within the target
# EXCLUDES: a cut that keeps an older entry past the budget (the 8
#   compactions of bench longmem: each kept the paste that crossed the
#   keep window, so the next turn compacted again), a cut that keeps
#   fewer entries than fit, a cut off the cuts, a compaction with nothing
#   to summarize, an early compaction that leaves the context over the
#   start again, a compaction without a cut, a threshold read off the
#   request rather than the turn (the 4 compactions of bench longmem: the
#   context plus the next paste crossed it before any turn did), a
#   request sent past the window
law infer_threshold_plan_exact:
  for on: Bool
  for +t: Nat
  for +last: Nat
  for +w: Nat
  for +r: M.Z
  for +m: M.Z
  for +keep: Nat
  for +full: Nat
  for +xs: List<&2, Nat>
  for +cuts: List<&2, Nat>
  {M.plan(on, t, last, w, r, m, keep, full, xs, cuts) == plan_spec(on, t, last, w, r, m, keep, full, xs, cuts) : M.Plan}

# kept stays within keep and base + kept within the target
def fits_spec(+k: Nat, +xs: List<&2, Nat>, +base: Nat, +tgt: Nat, +keep: Nat) -> Bool:
  Bool.and(Nat.is_le(Nat.add(base, held(k, xs)), tgt), Nat.is_le(held(k, xs), keep))

# k is the newest cut
def is_newest(n: Maybe<&2, Nat>, +k: Nat) -> Bool:
  match n:
    case None{}:
      False{}
    case Some{j}:
      Nat.is_eq(j, k)

# the cut keeping k leaves base + kept within the target and kept within
# keep, or it is the newest cut
def within(+k: Nat, +xs: List<&2, Nat>, +cuts: List<&2, Nat>, +base: Nat, +tgt: Nat, +keep: Nat) -> Bool:
  Bool.or(fits_spec(k, xs, base, tgt, keep), is_newest(newest_spec(xs, cuts), k))

# LAW infer_threshold_cut_within_target: with a known window and a base within the target, a compaction leaves the context within the target (base + kept) and keeps at most keepRecentTokens, unless no cut does: then it keeps only the newest cut
# EXCLUDES: a compaction that leaves the next turn no room (kept past the
#   target while a smaller cut fits)
law infer_threshold_cut_within_target:
  for on: Bool
  for +t: Nat
  for +last: Nat
  for +v: Nat
  for +r: M.Z
  for +m: M.Z
  for +keep: Nat
  for +full: Nat
  for +xs: List<&2, Nat>
  for +cuts: List<&2, Nat>
  for +k: Nat
  for room: {Nat.is_le(Nat.sub(t, sum(xs)), target_spec(1n+v, r, m)) == True{} : Bool}
  for cut: {M.Plan.cut(M.plan(on, t, last, 1n+v, r, m, keep, full, xs, cuts)) == Some{k} : Maybe<&2, Nat>}
  {within(k, xs, cuts, Nat.sub(t, sum(xs)), target_spec(1n+v, r, m), keep) == True{} : Bool}

# LAW infer_threshold_target_under: with a known window that leaves an empty context under every threshold, a request within the target after a turn within the target compacts at no threshold: after a compaction to the target, none runs until a turn grows the context past a threshold again
# EXCLUDES: a target at or past the background start (compaction again at
#   the next request), a plan that compacts under every threshold
law infer_threshold_target_under:
  for +t: Nat
  for +last: Nat
  for +v: Nat
  for +r: M.Z
  for +m: M.Z
  for +keep: Nat
  for +full: Nat
  for +xs: List<&2, Nat>
  for +cuts: List<&2, Nat>
  for live: {over_spec(True{}, 0n, 1n+v, r, m) == M.Under{} : M.Over}
  for small: {Nat.is_le(t, target_spec(1n+v, r, m)) == True{} : Bool}
  for settled: {Nat.is_le(last, target_spec(1n+v, r, m)) == True{} : Bool}
  {M.Plan.over(M.plan(True{}, t, last, 1n+v, r, m, keep, full, xs, cuts)) == M.Under{} : M.Over}

# LAW infer_threshold_turn_under: with compaction on and a known window, a request within the hard window after a turn whose context is under every threshold compacts at no threshold, however far the request itself is past them: a compaction runs only after the context actually crossed a threshold
# EXCLUDES: a compaction before a request because the context plus the
#   next turn would cross the threshold (bench longmem: 4 compactions a
#   run, where compacting after the turn that crossed takes 2), a
#   threshold read off the request
law infer_threshold_turn_under:
  for +t: Nat
  for +last: Nat
  for +v: Nat
  for +r: M.Z
  for +m: M.Z
  for +keep: Nat
  for +full: Nat
  for +xs: List<&2, Nat>
  for +cuts: List<&2, Nat>
  for within: {past_spec(t, r, 1n+v) == False{} : Bool}
  for under: {over_spec(True{}, last, 1n+v, r, m) == M.Under{} : M.Over}
  {M.Plan.over(M.plan(True{}, t, last, 1n+v, r, m, keep, full, xs, cuts)) == M.Under{} : M.Over}

# LAW infer_threshold_past_window_blocks: with compaction on and a known window, a request past the hard window that has a cut blocks, whatever its last turn reached: it waits for its compaction and never goes out past the window
# EXCLUDES: a request sent past the window because the last turn stayed
#   under every threshold (left to the provider's overflow), a background
#   compaction beside a request that cannot fit
law infer_threshold_past_window_blocks:
  for +t: Nat
  for +last: Nat
  for +v: Nat
  for +r: M.Z
  for +m: M.Z
  for +keep: Nat
  for +full: Nat
  for +xs: List<&2, Nat>
  for +cuts: List<&2, Nat>
  for +k: Nat
  for past: {past_spec(t, r, 1n+v) == True{} : Bool}
  for cut: {M.Plan.cut(M.plan(True{}, t, last, 1n+v, r, m, keep, full, xs, cuts)) == Some{k} : Maybe<&2, Nat>}
  {M.Plan.over(M.plan(True{}, t, last, 1n+v, r, m, keep, full, xs, cuts)) == M.Blocks{} : M.Over}

# The entry (bend/ffi_infer_threshold.bend)
# -----------------------------------------
# The spellers write what Rust writes, with the wire primitives only.

def spell_z(z: M.Z, rest: String) -> String:
  match z:
    case M.Up{n}:
      Wr.put_nat(0n, Wr.put_nat(n, rest))
    case M.Down{n}:
      Wr.put_nat(1n, Wr.put_nat(n, rest))

# a list of Nats, then rest
def spell_nats(xs: List<&2, Nat>, rest: String) -> String:
  Wr.put_list(~Nat, ~Wr.put_nat, xs, rest)

# a request: on, tokens, the last turn's tokens, window, reserve, margin,
# keepRecentTokens, full, the sizes, the cuts
def spell_req(on: Bool, t: Nat, last: Nat, w: Nat, r: M.Z, m: M.Z, keep: Nat, full: Nat, xs: List<&2, Nat>, cuts: List<&2, Nat>) -> String:
  Wr.put_bool(on, Wr.put_nat(t, Wr.put_nat(last, Wr.put_nat(w, spell_z(r, spell_z(m, Wr.put_nat(keep, Wr.put_nat(full, spell_nats(xs, spell_nats(cuts, ""))))))))))

# what Rust reads: 0 none | 1 background | 2 blocking, then rest
def spell_over(o: M.Over, rest: String) -> String:
  match o:
    case M.Under{}:
      Wr.put_nat(0n, rest)
    case M.Early{}:
      Wr.put_nat(1n, rest)
    case M.Blocks{}:
      Wr.put_nat(2n, rest)

# the cut: 0 none | 1 then how many entries it keeps
def spell_cut(c: Maybe<&2, Nat>) -> String:
  match c:
    case None{}:
      Wr.put_nat(0n, "")
    case Some{k}:
      Wr.put_nat(1n, Wr.put_nat(k, ""))

# the reply: the threshold, then the cut
def spell_plan(p: M.Plan) -> String:
  match p:
    case M.Plan{o, c}:
      spell_over(o, spell_cut(c))

def z_fits(z: M.Z) -> Bool:
  match z:
    case M.Up{n}:
      LawsBase.wire_fits(n)
    case M.Down{n}:
      LawsBase.wire_fits(n)

# a list fits the wire: its count and every item
def nats_fit(+xs: List<&2, Nat>) -> Bool:
  Bool.and(LawsBase.wire_fits(List.length(&2, Nat, xs)), LawsBase.wire_nats_fit(xs))

# every number of a request fits the wire
def req_fits(t: Nat, last: Nat, w: Nat, r: M.Z, m: M.Z, keep: Nat, full: Nat, xs: List<&2, Nat>, cuts: List<&2, Nat>) -> Bool:
  Bool.and(LawsBase.wire_fits(t), Bool.and(LawsBase.wire_fits(last), Bool.and(LawsBase.wire_fits(w), Bool.and(z_fits(r), Bool.and(z_fits(m), Bool.and(LawsBase.wire_fits(keep), Bool.and(LawsBase.wire_fits(full), Bool.and(nats_fit(xs), nats_fit(cuts)))))))))

# Reader: the requests the entry accepts, read with the wire primitives
type Ask is Data:
  Ask{on: Bool, t: Nat, last: Nat, w: Nat, r: M.Z, m: M.Z, keep: Nat, full: Nat, xs: List<&2, Nat>, cuts: List<&2, Nat>}

def read_z.up(d: Wr.Dec<Nat>) -> Wr.Dec<M.Z>:
  match d:
    case Wr.Got{n, s}:
      Wr.Got{M.Up{n}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def read_z.down(d: Wr.Dec<Nat>) -> Wr.Dec<M.Z>:
  match d:
    case Wr.Got{n, s}:
      Wr.Got{M.Down{n}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def read_z.tag(t: Nat, s: String) -> Wr.Dec<M.Z>:
  match t:
    case 0n:
      read_z.up(Wr.get_nat(s))
    case 1n:
      read_z.down(Wr.get_nat(s))
    case 2n+p:
      Wr.Bad{}

def read_z(d: Wr.Dec<Nat>) -> Wr.Dec<M.Z>:
  match d:
    case Wr.Got{t, s}:
      read_z.tag(t, s)
    case Wr.Bad{}:
      Wr.Bad{}

def read_ask.cuts(on: Bool, t: Nat, last: Nat, w: Nat, r: M.Z, m: M.Z, keep: Nat, full: Nat, xs: List<&2, Nat>, d: Wr.Dec<List<&2, Nat>>) -> Wr.Dec<Ask>:
  match d:
    case Wr.Got{cuts, s}:
      Wr.Got{Ask{on, t, last, w, r, m, keep, full, xs, cuts}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def read_ask.sizes(on: Bool, t: Nat, last: Nat, w: Nat, r: M.Z, m: M.Z, keep: Nat, full: Nat, d: Wr.Dec<List<&2, Nat>>) -> Wr.Dec<Ask>:
  match d:
    case Wr.Got{xs, s}:
      read_ask.cuts(on, t, last, w, r, m, keep, full, xs, Wr.get_list(~Nat, ~Wr.get_nat, s))
    case Wr.Bad{}:
      Wr.Bad{}

def read_ask.full(on: Bool, t: Nat, last: Nat, w: Nat, r: M.Z, m: M.Z, keep: Nat, d: Wr.Dec<Nat>) -> Wr.Dec<Ask>:
  match d:
    case Wr.Got{full, s}:
      read_ask.sizes(on, t, last, w, r, m, keep, full, Wr.get_list(~Nat, ~Wr.get_nat, s))
    case Wr.Bad{}:
      Wr.Bad{}

def read_ask.keep(on: Bool, t: Nat, last: Nat, w: Nat, r: M.Z, m: M.Z, d: Wr.Dec<Nat>) -> Wr.Dec<Ask>:
  match d:
    case Wr.Got{keep, s}:
      read_ask.full(on, t, last, w, r, m, keep, Wr.get_nat(s))
    case Wr.Bad{}:
      Wr.Bad{}

def read_ask.margin(on: Bool, t: Nat, last: Nat, w: Nat, r: M.Z, d: Wr.Dec<M.Z>) -> Wr.Dec<Ask>:
  match d:
    case Wr.Got{m, s}:
      read_ask.keep(on, t, last, w, r, m, Wr.get_nat(s))
    case Wr.Bad{}:
      Wr.Bad{}

def read_ask.reserve(on: Bool, t: Nat, last: Nat, w: Nat, d: Wr.Dec<M.Z>) -> Wr.Dec<Ask>:
  match d:
    case Wr.Got{r, s}:
      read_ask.margin(on, t, last, w, r, read_z(Wr.get_nat(s)))
    case Wr.Bad{}:
      Wr.Bad{}

def read_ask.window(on: Bool, t: Nat, last: Nat, d: Wr.Dec<Nat>) -> Wr.Dec<Ask>:
  match d:
    case Wr.Got{w, s}:
      read_ask.reserve(on, t, last, w, read_z(Wr.get_nat(s)))
    case Wr.Bad{}:
      Wr.Bad{}

def read_ask.last(on: Bool, t: Nat, d: Wr.Dec<Nat>) -> Wr.Dec<Ask>:
  match d:
    case Wr.Got{last, s}:
      read_ask.window(on, t, last, Wr.get_nat(s))
    case Wr.Bad{}:
      Wr.Bad{}

def read_ask.tokens(on: Bool, d: Wr.Dec<Nat>) -> Wr.Dec<Ask>:
  match d:
    case Wr.Got{t, s}:
      read_ask.last(on, t, Wr.get_nat(s))
    case Wr.Bad{}:
      Wr.Bad{}

def read_ask.go(d: Wr.Dec<Bool>) -> Wr.Dec<Ask>:
  match d:
    case Wr.Got{on, s}:
      read_ask.tokens(on, Wr.get_nat(s))
    case Wr.Bad{}:
      Wr.Bad{}

def read_ask.end(whole: Bool, a: Ask) -> Maybe<&2, Ask>:
  match whole:
    case True{}:
      Some{a}
    case False{}:
      None{}

def read_ask.whole(d: Wr.Dec<Ask>) -> Maybe<&2, Ask>:
  match d:
    case Wr.Got{a, s}:
      read_ask.end(Wr.end(s), a)
    case Wr.Bad{}:
      None{}

# the request s is, when s is exactly one request
def read_ask(s: String) -> Maybe<&2, Ask>:
  read_ask.whole(read_ask.go(Wr.get_bool(s)))

# LAW infer_threshold_ffi_answers: for every request whose numbers fit the wire, the entry answers the model's plan: the threshold, then the cut
law infer_threshold_ffi_answers:
  for +on: Bool
  for +t: Nat
  for +last: Nat
  for +w: Nat
  for +r: M.Z
  for +m: M.Z
  for +keep: Nat
  for +full: Nat
  for +xs: List<&2, Nat>
  for +cuts: List<&2, Nat>
  for fits: {req_fits(t, last, w, r, m, keep, full, xs, cuts) == True{} : Bool}
  {FT.ffi(spell_req(on, t, last, w, r, m, keep, full, xs, cuts)) == spell_plan(M.plan(on, t, last, w, r, m, keep, full, xs, cuts)) : String}

# LAW infer_threshold_ffi_malformed_exact: every input that is not exactly one request gets exactly the error form 'E ', then "infer_threshold: malformed request"
law infer_threshold_ffi_malformed_exact:
  for +s: String
  for no: {read_ask(s) == None{} : Maybe<&2, Ask>}
  {FT.ffi(s) == SCon{'E', SCon{' ', "infer_threshold: malformed request"}} : String}

# The entry, whole: what it answers to every input, from the spec plan
# (plan_spec) and the spec reader (read_ask) only, never the entry's codec
# or the model `plan`

def reply_spec(a: Ask) -> String:
  match a:
    case Ask{on, t, last, w, r, m, keep, full, xs, cuts}:
      spell_plan(plan_spec(on, t, last, w, r, m, keep, full, xs, cuts))

def entry_spec.of(q: Maybe<&2, Ask>) -> String:
  match q:
    case None{}:
      SCon{'E', SCon{' ', "infer_threshold: malformed request"}}
    case Some{a}:
      reply_spec(a)

# the answer to the input s: the spec's plan for the one request s is,
# else the error form
def entry_spec(s: String) -> String:
  entry_spec.of(read_ask(s))

# LAW infer_threshold_ffi_spec: for every input, the entry answers exactly the spec's: the plan plan_spec gives (the threshold 0 none, 1 background, 2 blocking, then the cut 0 none or 1 and the entries it keeps) when the input is exactly one request, else the error form 'E ', then "infer_threshold: malformed request"
# EXCLUDES: an answer for an input that is not exactly one request (input
#   left over, an unknown sign tag, a short list, a malformed field), a
#   threshold or a cut other than the spec's for any request, numbers too
#   long for the wire included
law infer_threshold_ffi_spec:
  for +s: String
  {FT.ffi(s) == entry_spec(s) : String}

# LAW infer_threshold_ffi_example: anchor: the bytes Rust sends and reads, window 10 and reserve 2 (limit 8, start 6, target 3, hard window 10), margin 3, keep 9, two entries (newest first) and a cut that keeps the newest: a request of 5 after a turn of 5 is under; a request of 9 after a turn of 5 is under too (past the limit, within the window); after a turn of 6 a request over the background threshold compacts early when the cut brings it to the target (base 2 + 1), not when it cannot (base 2 + 2); after a turn of 9 it blocks; a request of 11 blocks after any turn; with no cut nothing compacts; compaction off, none; with the window unknown keep alone bounds the cut (keep 2 keeps 2 of 3 sizes 1, 1, 1); a cut that leaves nothing to summarize is none; an unknown tag and input left over are refused
law infer_threshold_ffi_example:
  {FT.ffi("T5,5,10,0,2,0,3,9,2,2,1,3,1,1,") == "0,1,1," : String} &
  {FT.ffi("T9,5,10,0,2,0,3,9,2,2,1,3,1,1,") == "0,1,1," : String} &
  {FT.ffi("T6,6,10,0,2,0,3,9,2,2,1,3,1,1,") == "1,1,1," : String} &
  {FT.ffi("T6,6,10,0,2,0,3,9,2,2,2,2,1,1,") == "0,1,1," : String} &
  {FT.ffi("T9,9,10,0,2,0,3,9,2,2,1,3,1,1,") == "2,1,1," : String} &
  {FT.ffi("T11,0,10,0,2,0,3,9,2,2,1,3,1,1,") == "2,1,1," : String} &
  {FT.ffi("T9,9,10,0,2,0,3,9,2,2,1,3,0,") == "0,0," : String} &
  {FT.ffi("F9,9,10,0,2,0,3,9,2,2,1,3,1,1,") == "0,1,1," : String} &
  {FT.ffi("T5,5,0,0,2,0,3,2,3,3,1,1,1,3,1,2,3,") == "0,1,2," : String} &
  {FT.ffi("T5,5,0,0,2,0,3,9,1,2,1,1,1,1,") == "0,0," : String} &
  {FT.ffi("T5,5,10,0,2,2,3,9,2,2,1,3,1,1,") == SCon{'E', SCon{' ', "infer_threshold: malformed request"}} : String} &
  {FT.ffi("T5,5,10,0,2,0,3,9,2,2,1,3,1,1,x") == SCon{'E', SCon{' ', "infer_threshold: malformed request"}} : String}
