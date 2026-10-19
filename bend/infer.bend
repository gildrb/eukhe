# infer: the model of the inference layer's rules (docs/inference.md, S6).
#
# 1. The quirks rulebook. A rule says: at a layer (a model family, a
#    model, a host), for a target id of that layer, directive d has value
#    v. A query names a family, a model and a host. The compiler rejects
#    a rule with an unknown directive, and two rules of one layer, target
#    and directive with different values (ambiguous precedence). A lookup
#    takes the rule of the highest layer that applies: host over model
#    over family. No rule that applies: the answer is Unknown.
# 2. A forced tool call. Every attempt carries a soft prompt. The first
#    attempt sets the native flag only when the provider supports it and
#    it is free (no cache cost). Each retry sets the flag when the provider
#    supports it. After the retries, the call fails and says so.
# 3. The strict schema budget. A provider takes at most `cap` strict
#    schemas. The tools of highest priority get them; the other tools are
#    loose: the client repairs their output.
# 4. The repetition guard. A stream whose last k chunks are periodic,
#    with a period of at most k/4 (at least 1), is cut.
# 5. Early compaction. Compaction starts when the context reaches the
#    threshold, a margin below the limit.
# 6. The thinking ladder. Every ladder is rulebook data. The chosen ladder
#    of a model is its explicit map, else the ladder that the rulebook
#    gives it, else no ladder (every entry missing). A reasoning model
#    offers each level whose chosen entry is a wire string, and each
#    level with no chosen entry that the default ladder lists; a null
#    entry removes the level. A model without reasoning offers the levels
#    that the plain default ladder lists.
#
# A recursive scan takes the test of its first item as a parameter (Bend
# matches only parameters); `*.at` computes that test.

import Base
import ./effort.bend as Ef

def elem(xs: List<&2, Nat>, +x: Nat) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case y <> rest:
      Bool.or(Nat.is_eq(y, x), elem(rest, x))

# 1. The quirks rulebook
# ----------------------

type Lay is Data:
  Fam{}
  Mod{}
  Host{}

def Lay.rank(l: Lay) -> Nat:
  match l:
    case Fam{}:
      0n
    case Mod{}:
      1n
    case Host{}:
      2n

def Lay.eq(a: Lay, b: Lay) -> Bool:
  Nat.is_eq(Lay.rank(a), Lay.rank(b))

type Rule is Data:
  Rule{lay: Lay, target: Nat, dir: Nat, val: Nat}

def Rule.dir(r: Rule) -> Nat:
  match r:
    case Rule{l, t, d, v}:
      d

def Rule.val(r: Rule) -> Nat:
  match r:
    case Rule{l, t, d, v}:
      v

def Rule.rank(r: Rule) -> Nat:
  match r:
    case Rule{l, t, d, v}:
      Lay.rank(l)

type Query is Data:
  Query{fam: Nat, mod: Nat, host: Nat}

# rule r applies to query q
def applies(q: Query, r: Rule) -> Bool:
  match q:
    case Query{f, m, h}:
      match r:
        case Rule{l, t, d, v}:
          match l:
            case Fam{}:
              Nat.is_eq(t, f)
            case Mod{}:
              Nat.is_eq(t, m)
            case Host{}:
              Nat.is_eq(t, h)

# two rules of one layer, target and directive with different values
def clash(a: Rule, b: Rule) -> Bool:
  match a b:
    case Rule{la, ta, da, va} Rule{lb, tb, db, vb}:
      Bool.and(Lay.eq(la, lb), Bool.and(Nat.is_eq(ta, tb), Bool.and(Nat.is_eq(da, db), Bool.not(Nat.is_eq(va, vb)))))

# r clashes with a rule of rs
def clashes(+r: Rule, rs: List<&2, Rule>) -> Bool:
  match rs:
    case Nil{}:
      False{}
    case +s <> rest:
      Bool.or(clash(r, s), clashes(r, rest))

# some two rules of rs clash
def ambiguous(rs: List<&2, Rule>) -> Bool:
  match rs:
    case Nil{}:
      False{}
    case +r <> +rest:
      Bool.or(clashes(r, rest), ambiguous(rest))

# every rule of rs has a known directive
def known_all(rs: List<&2, Rule>, +known: List<&2, Nat>) -> Bool:
  match rs:
    case Nil{}:
      True{}
    case +r <> rest:
      Bool.and(elem(known, Rule.dir(r)), known_all(rest, known))

# the rulebook compiles: every directive known, no ambiguity
def compiles(+known: List<&2, Nat>, +rs: List<&2, Rule>) -> Bool:
  Bool.and(known_all(rs, known), Bool.not(ambiguous(rs)))

type Ans is Data:
  Known{val: Nat}
  Unknown{}

# the best rule so far: its rank and value
type Best is Data:
  Best{rank: Nat, val: Nat}

# keep the rule of higher rank; at an equal rank keep the first
def better.at(up: Bool, x: Best, +r: Rule) -> Maybe<&2, Best>:
  match up:
    case True{}:
      Some{Best{Rule.rank(r), Rule.val(r)}}
    case False{}:
      Some{x}

def Best.rank(x: Best) -> Nat:
  match x:
    case Best{k, v}:
      k

def better(b: Maybe<&2, Best>, +r: Rule) -> Maybe<&2, Best>:
  match b:
    case None{}:
      Some{Best{Rule.rank(r), Rule.val(r)}}
    case Some{+x}:
      better.at(Nat.is_lt(Best.rank(x), Rule.rank(r)), x, r)

# the first rule of rs applies to q with directive d
def use.at(+rs: List<&2, Rule>, +q: Query, +d: Nat) -> Bool:
  match rs:
    case Nil{}:
      False{}
    case +r <> rest:
      Bool.and(applies(q, r), Nat.is_eq(Rule.dir(r), d))

# the best rule of rs that applies to q with directive d; hit is
# use.at(rs, q, d)
def look.go(rs: List<&2, Rule>, +q: Query, +d: Nat, b: Maybe<&2, Best>, hit: Bool) -> Maybe<&2, Best>:
  match rs:
    case Nil{}:
      b
    case +r <> +rest:
      match hit:
        case True{}:
          look.go(rest, q, d, better(b, r), use.at(rest, q, d))
        case False{}:
          look.go(rest, q, d, b, use.at(rest, q, d))

def ans(b: Maybe<&2, Best>) -> Ans:
  match b:
    case None{}:
      Unknown{}
    case Some{x}:
      match x:
        case Best{k, v}:
          Known{v}

# the answer of the rulebook rs for query q and directive d
def lookup(+rs: List<&2, Rule>, +q: Query, +d: Nat) -> Ans:
  ans(look.go(rs, q, d, None{}, use.at(rs, q, d)))

# some rule of rs applies to q with directive d at layer rank k or above
def any_at(rs: List<&2, Rule>, +q: Query, +d: Nat, +k: Nat) -> Bool:
  match rs:
    case Nil{}:
      False{}
    case +r <> rest:
      Bool.or(Bool.and(Bool.and(applies(q, r), Nat.is_eq(Rule.dir(r), d)), Nat.is_le(k, Rule.rank(r))), any_at(rest, q, d, k))

def is_known(a: Ans) -> Bool:
  match a:
    case Known{v}:
      True{}
    case Unknown{}:
      False{}

# 2. A forced tool call
# ---------------------

# One attempt: the soft prompt is always there; flag says whether the
# native flag is set too
type Try is Data:
  Try{flag: Bool}

type Forced is Data:
  Called{}  # the model called the tool
  Missed{}  # every attempt went without the call: the call fails

# the attempts and the outcome: replies (True: the model called the
# tool) in attempt order, r retries left; flag is this attempt's flag
def force.next(t: Try, p: List<&2, Try> & Forced) -> List<&2, Try> & Forced:
  (ts, o) = p
  (t <> ts, o)

# the last attempt: the model called the tool (c) or the call fails
def force.last(c: Bool, +flag: Bool) -> List<&2, Try> & Forced:
  match c:
    case True{}:
      ([Try{flag}], Called{})
    case False{}:
      ([Try{flag}], Missed{})

# an attempt with a retry left; more is the retries' outcome
def force.again(c: Bool, +flag: Bool, more: List<&2, Try> & Forced) -> List<&2, Try> & Forced:
  match c:
    case True{}:
      ([Try{flag}], Called{})
    case False{}:
      force.next(Try{flag}, more)

def force.go(replies: List<&2, Bool>, r: Nat, +flag: Bool, +sup: Bool) -> List<&2, Try> & Forced:
  match replies:
    case Nil{}:
      ([Try{flag}], Missed{})
    case c <> rest:
      match r:
        case 0n:
          force.last(c, flag)
        case 1n+q:
          force.again(c, flag, force.go(rest, q, sup, sup))

# a forced call with r retries, the provider's support of the flag and
# whether it is free; a missing reply counts as no call
def force(r: Nat, replies: List<&2, Bool>, +sup: Bool, free: Bool) -> List<&2, Try> & Forced:
  force.go(replies, r, Bool.and(sup, free), sup)

def Try.flag(t: Try) -> Bool:
  match t:
    case Try{f}:
      f

# every try of ts sets the flag exactly when f says
def flags(ts: List<&2, Try>, +f: Bool) -> Bool:
  match ts:
    case Nil{}:
      True{}
    case t <> rest:
      Bool.and(Bool.not(Bool.xor(Try.flag(t), f)), flags(rest, f))

# the model called the tool within the first n replies
def called_within(n: Nat, replies: List<&2, Bool>) -> Bool:
  match n:
    case 0n:
      False{}
    case 1n+m:
      match replies:
        case Nil{}:
          False{}
        case c <> rest:
          Bool.or(c, called_within(m, rest))

def Forced.called(o: Forced) -> Bool:
  match o:
    case Called{}:
      True{}
    case Missed{}:
      False{}

# 3. The strict schema budget
# ---------------------------

type Tool is Data:
  Tool{id: Nat, prio: Nat}

def Tool.prio(t: Tool) -> Nat:
  match t:
    case Tool{i, p}:
      p

# the first tool of ts has a priority no higher than t
def low.at(+ts: List<&2, Tool>, +t: Tool) -> Bool:
  match ts:
    case Nil{}:
      False{}
    case u <> rest:
      Nat.is_le(Tool.prio(u), Tool.prio(t))

# insert t into ts (by priority, highest first; before its equals, so
# rank keeps the given order among equals: the earlier tool wins a tie);
# hit is low.at(ts, t)
def ins.go(ts: List<&2, Tool>, +t: Tool, hit: Bool) -> List<&2, Tool>:
  match ts:
    case Nil{}:
      [t]
    case +u <> +rest:
      match hit:
        case True{}:
          t <> u <> rest
        case False{}:
          u <> ins.go(rest, t, low.at(rest, t))

def ins(+ts: List<&2, Tool>, +t: Tool) -> List<&2, Tool>:
  ins.go(ts, t, low.at(ts, t))

def rank(ts: List<&2, Tool>) -> List<&2, Tool>:
  match ts:
    case Nil{}:
      Nil{}
    case t <> rest:
      ins(rank(rest), t)

# the tools that get strict schemas (at most cap) and the loose ones
def strict(+cap: Nat, +ts: List<&2, Tool>) -> List<&2, Tool> & List<&2, Tool>:
  +r = rank(ts)
  (List.take(&2, Tool, r, cap), List.drop(&2, Tool, r, cap))

# every tool of xs has a priority of at least p
def all_ge(xs: List<&2, Tool>, +p: Nat) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case +x <> rest:
      Bool.and(Nat.is_le(p, Tool.prio(x)), all_ge(rest, p))

# every tool of xs has a priority of at least every one of ys
def dominates(+xs: List<&2, Tool>, ys: List<&2, Tool>) -> Bool:
  match ys:
    case Nil{}:
      True{}
    case +y <> rest:
      Bool.and(all_ge(xs, Tool.prio(y)), dominates(xs, rest))

def Tool.id(t: Tool) -> Nat:
  match t:
    case Tool{i, p}:
      i

# the first tool of ts has id i
def tid.at(+ts: List<&2, Tool>, +i: Nat) -> Bool:
  match ts:
    case Nil{}:
      False{}
    case t <> rest:
      Nat.is_eq(Tool.id(t), i)

# the number of copies of tool id i in ts; hit is tid.at(ts, i)
def count.go(ts: List<&2, Tool>, +i: Nat, hit: Bool) -> Nat:
  match ts:
    case Nil{}:
      0n
    case t <> +rest:
      match hit:
        case True{}:
          1n+count.go(rest, i, tid.at(rest, i))
        case False{}:
          count.go(rest, i, tid.at(rest, i))

def count(+ts: List<&2, Tool>, +i: Nat) -> Nat:
  count.go(ts, i, tid.at(ts, i))

# 4. The repetition guard
# -----------------------
#
# Chunks read so far are kept newest first (`seen`). Period 1+q has a
# counter: how many chunks, from the newest, each equal the chunk 1+q
# places before it. The guard cuts after the chunk that brings the
# counter of some period 1+q (1+q at most periods(k)) to k - (1+q): then
# the last k chunks repeat with that period. Period 1 is the old rule:
# k equal chunks in a row.

type Cut is Data:
  Whole{}        # the stream went to its end
  CutAt{at: Nat} # the stream was cut after `at` chunks

# k/4, rounded down
def quarter(+k: Nat) -> Nat:
  match k:
    case 0n:
      0n
    case 1n+a:
      match a:
        case 0n:
          0n
        case 1n+b:
          match b:
            case 0n:
              0n
            case 1n+c:
              match c:
                case 0n:
                  0n
                case 1n+d:
                  1n+quarter(d)

# the longest period the guard checks: q, but at least 1
def periods.of(q: Nat) -> Nat:
  match q:
    case 0n:
      1n
    case 1n+r:
      1n+r

# the longest period the guard checks for k: k/4, but at least 1
def periods(+k: Nat) -> Nat:
  periods.of(quarter(k))

# the chunk i places back in s (0: the newest) is x
def back(s: List<&2, Nat>, +i: Nat, +x: Nat) -> Bool:
  match s i:
    case Nil{} _:
      False{}
    case y <> rest 0n:
      Nat.is_eq(x, y)
    case y <> rest 1n+j:
      back(rest, j, x)

# the newest chunk of s equals the chunk 1+q places before it
def cycle.at(s: List<&2, Nat>, +q: Nat) -> Bool:
  match s:
    case Nil{}:
      False{}
    case x <> rest:
      back(rest, q, x)

# the counter of period 1+q; hit is cycle.at(s, q)
def cycle.go(s: List<&2, Nat>, +q: Nat, hit: Bool) -> Nat:
  match s:
    case Nil{}:
      0n
    case x <> +rest:
      match hit:
        case True{}:
          1n+cycle.go(rest, q, cycle.at(rest, q))
        case False{}:
          0n

# the counter of period 1+q on s: how many chunks, from the newest, each
# equal the chunk 1+q places before it
def cycle(+s: List<&2, Nat>, +q: Nat) -> Nat:
  cycle.go(s, q, cycle.at(s, q))

# the counter of some period 1+q, q < n, reaches k - (1+q)
def fires.go(+s: List<&2, Nat>, +k: Nat, +n: Nat) -> Bool:
  match n:
    case 0n:
      False{}
    case 1n+q:
      Bool.or(Nat.is_le(Nat.sub(k, 1n+q), cycle(s, q)), fires.go(s, k, q))

# after the chunks s (newest first), the guard cuts
def fires(+s: List<&2, Nat>, +k: Nat) -> Bool:
  fires.go(s, k, periods(k))

# the first chunk of xs, read after seen, cuts the stream
def fire.at(xs: List<&2, Nat>, +k: Nat, +seen: List<&2, Nat>) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case x <> rest:
      fires(x <> seen, k)

# read chunks; seen the chunks read so far, newest first; n chunks read so
# far; hit is fire.at(xs, k, seen)
def guard.go(xs: List<&2, Nat>, +k: Nat, +seen: List<&2, Nat>, n: Nat, hit: Bool) -> Cut:
  match xs:
    case Nil{}:
      Whole{}
    case +x <> +rest:
      match hit:
        case True{}:
          CutAt{1n+n}
        case False{}:
          guard.go(rest, k, x <> seen, 1n+n, fire.at(rest, k, x <> seen))

# the guard with a window of k chunks (k = 64 by default): it cuts the
# stream after the chunk that makes the last k chunks periodic with a
# period of at most periods(k); a k of at most 1 cuts at the first chunk
def guard(+xs: List<&2, Nat>, +k: Nat) -> Cut:
  guard.go(xs, k, Nil{}, 0n, fire.at(xs, k, Nil{}))

# each of the first m chunks of s (newest first) equals the chunk 1+q
# places before it
def each(s: List<&2, Nat>, +q: Nat, m: Nat) -> Bool:
  match s m:
    case _ 0n:
      True{}
    case Nil{} 1n+n:
      False{}
    case x <> +rest 1n+n:
      Bool.and(back(rest, q, x), each(rest, q, n))

# the last k chunks of s (newest first) are periodic with some period 1+q,
# q < n: each of the last k - (1+q) equals the chunk 1+q before it
def periodic.go(+s: List<&2, Nat>, +k: Nat, +n: Nat) -> Bool:
  match n:
    case 0n:
      False{}
    case 1n+q:
      Bool.or(each(s, q, Nat.sub(k, 1n+q)), periodic.go(s, k, q))

# the last k chunks of s are periodic with a period of at most periods(k)
def periodic(+s: List<&2, Nat>, +k: Nat) -> Bool:
  periodic.go(s, k, periods(k))

# some window of xs (read after seen) is periodic: the last k chunks of
# some prefix
def loops.go(xs: List<&2, Nat>, +k: Nat, +seen: List<&2, Nat>) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case +x <> +rest:
      Bool.or(periodic(x <> seen, k), loops.go(rest, k, x <> seen))

# some window of k chunks of xs is periodic with a period of at most
# periods(k)
def loops(+xs: List<&2, Nat>, +k: Nat) -> Bool:
  loops.go(xs, k, Nil{})

# how many chunks at the start of xs equal x
def same_run.at(+xs: List<&2, Nat>, +x: Nat) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case y <> rest:
      Nat.is_eq(y, x)

def same_run.go(xs: List<&2, Nat>, +x: Nat, hit: Bool) -> Nat:
  match xs:
    case Nil{}:
      0n
    case y <> +rest:
      match hit:
        case True{}:
          1n+same_run.go(rest, x, same_run.at(rest, x))
        case False{}:
          0n

def same_run(+xs: List<&2, Nat>, +x: Nat) -> Nat:
  same_run.go(xs, x, same_run.at(xs, x))

# xs holds some chunk k times in a row
def repeats(xs: List<&2, Nat>, +k: Nat) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case +x <> +rest:
      Bool.or(Nat.is_le(k, 1n+same_run(rest, x)), repeats(rest, k))

def Cut.cut(c: Cut) -> Bool:
  match c:
    case Whole{}:
      False{}
    case CutAt{n}:
      True{}

# 5. Early compaction
# -------------------

# the index of the first size of xs at or above t (from i), if any
def reach.at(+xs: List<&2, Nat>, +t: Nat) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case x <> rest:
      Nat.is_le(t, x)

def first_at.go(xs: List<&2, Nat>, +t: Nat, i: Nat, hit: Bool) -> Maybe<&2, Nat>:
  match xs:
    case Nil{}:
      None{}
    case x <> +rest:
      match hit:
        case True{}:
          Some{i}
        case False{}:
          first_at.go(rest, t, 1n+i, reach.at(rest, t))

def first_at(+xs: List<&2, Nat>, +t: Nat, i: Nat) -> Maybe<&2, Nat>:
  first_at.go(xs, t, i, reach.at(xs, t))

# each size of xs is at most m above the one before it (from prev)
def steps_le(xs: List<&2, Nat>, +m: Nat, +prev: Nat) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case +x <> rest:
      Bool.and(Nat.is_le(x, Nat.add(prev, m)), steps_le(rest, m, x))

def m.lt(a: Maybe<&2, Nat>, b: Maybe<&2, Nat>) -> Bool:
  match a:
    case None{}:
      Maybe.is_none(&2, Nat, b)
    case Some{x}:
      match b:
        case None{}:
          True{}
        case Some{y}:
          Nat.is_lt(x, y)

# 6. The thinking ladder
# ----------------------

# The default ladders of the rulebook: the levels a reasoning model and a
# model without reasoning offer where the chosen ladder has no entry
type Defaults is Data:
  Defaults{reasoning: List<&2, Ef.Lv>, plain: List<&2, Ef.Lv>}

def Defaults.reasoning(d: Defaults) -> List<&2, Ef.Lv>:
  match d:
    case Defaults{r, p}:
      r

def Defaults.plain(d: Defaults) -> List<&2, Ef.Lv>:
  match d:
    case Defaults{r, p}:
      p

# the shipped default ladders (rulebook.json `thinking_defaults`)
def lad.shipped() -> Defaults:
  Defaults{[Ef.Off{}, Ef.Minimal{}, Ef.Low{}, Ef.Medium{}, Ef.High{}], [Ef.Off{}]}

# the chosen ladder: the explicit map, else the rulebook's ladder, else
# no ladder
def lad.chosen(explicit: Maybe<&2, Ef.LvMap>, rule: Maybe<&2, Ef.LvMap>) -> Ef.LvMap:
  match explicit:
    case Some{e}:
      e
    case None{}:
      match rule:
        case Some{r}:
          r
        case None{}:
          Ef.LvMap.none()

# whether a level with chosen entry e is offered, given the default ladder
# dl: a wire string offers it, null does not, no entry offers it when dl
# lists it
def lad.keep(+l: Ef.Lv, e: Ef.Ent, +dl: List<&2, Ef.Lv>) -> Bool:
  match e:
    case Ef.Missing{}:
      Ef.has(dl, l)
    case Ef.Null{}:
      False{}
    case Ef.Wire{}:
      True{}

def lad.ent(b: Bool) -> Ef.Ent:
  match b:
    case True{}:
      Ef.Wire{}
    case False{}:
      Ef.Null{}

# entry e of level l with the default ladder dl filled in where e is
# missing
def lad.fill.e(+l: Ef.Lv, e: Ef.Ent, +dl: List<&2, Ef.Lv>) -> Ef.Ent:
  match e:
    case Ef.Missing{}:
      lad.ent(Ef.has(dl, l))
    case Ef.Null{}:
      Ef.Null{}
    case Ef.Wire{}:
      Ef.Wire{}

# the map with the default ladder dl filled in where it has no entry
def lad.fill(map: Ef.LvMap, +dl: List<&2, Ef.Lv>) -> Ef.LvMap:
  match map:
    case Ef.LvMap{o, mi, lo, me, hi, xh, mx}:
      Ef.LvMap{lad.fill.e(Ef.Off{}, o, dl), lad.fill.e(Ef.Minimal{}, mi, dl), lad.fill.e(Ef.Low{}, lo, dl), lad.fill.e(Ef.Medium{}, me, dl), lad.fill.e(Ef.High{}, hi, dl), lad.fill.e(Ef.Xhigh{}, xh, dl), lad.fill.e(Ef.Max{}, mx, dl)}

# the levels offered with the chosen ladder map and the default ladders d
def lad.offered.of(r: Bool, map: Ef.LvMap, d: Defaults) -> List<&2, Ef.Lv>:
  match r:
    case True{}:
      Ef.offer(lad.fill(map, Defaults.reasoning(d)), Ef.ladder())
    case False{}:
      Ef.offer(lad.fill(Ef.LvMap.none(), Defaults.plain(d)), Ef.ladder())

# the levels a model offers: reasoning or not, its explicit map, the
# rulebook's ladder for it, the default ladders
def lad.offered(r: Bool, explicit: Maybe<&2, Ef.LvMap>, rule: Maybe<&2, Ef.LvMap>, d: Defaults) -> List<&2, Ef.Lv>:
  lad.offered.of(r, lad.chosen(explicit, rule), d)
