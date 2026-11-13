# limits: the limits of a run (Rust: eukhe-bend rules/limits.rs). Run as
# the compiled core by bend/ffi_limits.bend.
#
# A run is what one request of the principal starts (a message sent while
# the session is idle, a `-p` prompt, an SDK prompt, a cron fire, a
# `/loop`, an autoresearch run). Each dimension of a run (money, tokens,
# time, tool calls, model requests) holds a number or `unlimited`, and the
# source it came from.
#
# fill: the limit the principal set for the run; else the last `/b`
#   preset that names the dimension; else, with limits on
#   (`budget.limits`), the principal's profile for the run's kind, else
#   the limits profile (the table below); else unlimited, until finished.
#   Only the principal (set, a preset, a profile) gives `unlimited`.
# plan_wraps: the first plan window whose last reading is at or past
#   1000 - reserve permille used.
# plan_notice: one notice per window each time its reading reaches
#   1000 - reserve permille; a reading below it arms the window again.
# floor: the first dimension in which a run's limits cannot hold its
#   first work request with its final-answer reserve (budget.bend's
#   need and lack), if any.
# renew: an account's free becomes each limit less what the run spent
#   since its start, holds and lent; its deadline is now plus the time
#   limit. Spent, holds, lent and the overrun are kept.
# prefix: the `/b` words at the start of a message: preset names and
#   key=value pairs, then the rest of the message verbatim.
# Pure: no IO, no @unsafe.

import Base
import ./budget.bend as B

# The kind of a run
type Run is Data:
  Interactive{}
  Headless{}
  Sdk{}
  Scheduled{}
  Loop{}
  Autoresearch{}

# How the run's model is paid: a plan login, an API key, a local model
type Auth is Data:
  Plan{}
  ApiKey{}
  Local{}

# Whether unset dimensions fill from the profiles (`budget.limits`)
type Toggle is Data:
  Off{}
  On{}

# One dimension's limit: not given, a number, unlimited
type Val is Data:
  Unset{}
  At{n: Nat}
  Unlimited{}

# A limit per dimension: money (micro-dollars), tokens, time (ms), tool
# calls, model requests
type Lims is Data:
  Lims{cost: Val, tok: Val, ms: Val, calls: Val, reqs: Val}

# Where a dimension's limit came from; a preset by its place among the
# presets given
type Src is Data:
  UntilFinished{}
  Set{}
  LimitsProfile{}
  Profile{}
  Preset{i: Nat}

type Srcs is Data:
  Srcs{cost: Src, tok: Src, ms: Src, calls: Src, reqs: Src}

# The filled limits (never Unset) and their sources
type Filled is Data:
  Filled{lims: Lims, srcs: Srcs}

# A shipped preset
type Scale is Data:
  Quick{}
  Deep{}

# Limits profile
# --------------

# The time of a kind's limits profile, in ms
def table_ms(k: Run) -> Nat:
  match k:
    case Interactive{}:
      14400000n
    case Headless{}:
      14400000n
    case Sdk{}:
      14400000n
    case Scheduled{}:
      3600000n
    case Loop{}:
      28800000n
    case Autoresearch{}:
      43200000n

# The tool calls of a kind's limits profile
def table_calls(k: Run) -> Nat:
  match k:
    case Interactive{}:
      4000n
    case Headless{}:
      4000n
    case Sdk{}:
      4000n
    case Scheduled{}:
      4000n
    case Loop{}:
      8000n
    case Autoresearch{}:
      12000n

# The model requests of a kind's limits profile
def table_reqs(k: Run) -> Nat:
  match k:
    case Interactive{}:
      3200n
    case Headless{}:
      3200n
    case Sdk{}:
      3200n
    case Scheduled{}:
      3200n
    case Loop{}:
      6400n
    case Autoresearch{}:
      9600n

# a local model's runs have no tool-call limit in the limits profile
def table_calls.of(+k: Run, a: Auth) -> Val:
  match a:
    case Plan{}:
      At{table_calls(k)}
    case ApiKey{}:
      At{table_calls(k)}
    case Local{}:
      Unset{}

# The limits profile of a kind and auth: time, tool calls (none for a
# local model) and model requests; money and tokens are not filled
def profile(+k: Run, a: Auth) -> Lims:
  Lims{Unset{}, Unset{}, At{table_ms(k)}, table_calls.of(k, a), At{table_reqs(k)}}

def scale.n(s: Scale, n: Nat) -> Nat:
  match s:
    case Quick{}:
      Nat.div(n, 4n)
    case Deep{}:
      Nat.mul(n, 4n)

def scale.val(+s: Scale, v: Val) -> Val:
  match v:
    case Unset{}:
      Unset{}
    case At{n}:
      At{scale.n(s, n)}
    case Unlimited{}:
      Unlimited{}

# the limits l scaled by s
def scale.lims(+s: Scale, l: Lims) -> Lims:
  match l:
    case Lims{c, t, m, n, r}:
      Lims{scale.val(s, c), scale.val(s, t), scale.val(s, m), scale.val(s, n), scale.val(s, r)}

# A shipped preset: quick a quarter of the limits profile, deep four
# times it
def preset(s: Scale, k: Run, a: Auth) -> Lims:
  scale.lims(s, profile(k, a))

# Fill
# ----

def Lims.cost(l: Lims) -> Val:
  match l:
    case Lims{c, t, m, n, r}:
      c

def Lims.tok(l: Lims) -> Val:
  match l:
    case Lims{c, t, m, n, r}:
      t

def Lims.ms(l: Lims) -> Val:
  match l:
    case Lims{c, t, m, n, r}:
      m

def Lims.calls(l: Lims) -> Val:
  match l:
    case Lims{c, t, m, n, r}:
      n

def Lims.reqs(l: Lims) -> Val:
  match l:
    case Lims{c, t, m, n, r}:
      r

# the limit of a dimension
def get(d: B.Dim, l: Lims) -> Val:
  match d:
    case B.Cost{}:
      Lims.cost(l)
    case B.Tok{}:
      Lims.tok(l)
    case B.Time{}:
      Lims.ms(l)
    case B.Calls{}:
      Lims.calls(l)
    case B.Reqs{}:
      Lims.reqs(l)

# A dimension's limit and its source
type Pick is Data:
  Pick{v: Val, src: Src}

def last.take(v: Val, i: Nat, acc: Maybe<&2, Pick>) -> Maybe<&2, Pick>:
  match v:
    case Unset{}:
      acc
    case At{n}:
      Some{Pick{At{n}, Preset{i}}}
    case Unlimited{}:
      Some{Pick{Unlimited{}, Preset{i}}}

# the last preset of ps (the first at place i) that gives dimension d
def last(+d: B.Dim, ps: List<&2, Lims>, +i: Nat, acc: Maybe<&2, Pick>) -> Maybe<&2, Pick>:
  match ps:
    case Nil{}:
      acc
    case Con{h, t}:
      last(d, t, 1n+i, last.take(get(d, h), i, acc))

# with limits on and no profile value: the limits profile, else until
# finished
def on.table(v: Val) -> Pick:
  match v:
    case Unset{}:
      Pick{Unlimited{}, UntilFinished{}}
    case At{n}:
      Pick{At{n}, LimitsProfile{}}
    case Unlimited{}:
      Pick{Unlimited{}, UntilFinished{}}

# with limits on: the principal's profile, else the table's
def on.profile(v: Val, table: Val) -> Pick:
  match v:
    case Unset{}:
      on.table(table)
    case At{n}:
      Pick{At{n}, Profile{}}
    case Unlimited{}:
      Pick{Unlimited{}, Profile{}}

def unset(t: Toggle, own: Val, table: Val) -> Pick:
  match t:
    case Off{}:
      Pick{Unlimited{}, UntilFinished{}}
    case On{}:
      on.profile(own, table)

def by_preset(m: Maybe<&2, Pick>, t: Toggle, own: Val, table: Val) -> Pick:
  match m:
    case None{}:
      unset(t, own, table)
    case Some{p}:
      p

def by_set(v: Val, +d: B.Dim, t: Toggle, ps: List<&2, Lims>, own: Lims, table: Lims) -> Pick:
  match v:
    case Unset{}:
      by_preset(last(d, ps, 0n, None{}), t, get(d, own), get(d, table))
    case At{n}:
      Pick{At{n}, Set{}}
    case Unlimited{}:
      Pick{Unlimited{}, Set{}}

# one dimension: set, else the last preset, else unset's fill
def one(+d: B.Dim, t: Toggle, set: Lims, ps: List<&2, Lims>, own: Lims, table: Lims) -> Pick:
  by_set(get(d, set), d, t, ps, own, table)

def Pick.v(p: Pick) -> Val:
  match p:
    case Pick{v, s}:
      v

def Pick.src(p: Pick) -> Src:
  match p:
    case Pick{v, s}:
      s

def fill.done(+c: Pick, +k: Pick, +m: Pick, +n: Pick, +r: Pick) -> Filled:
  Filled{Lims{Pick.v(c), Pick.v(k), Pick.v(m), Pick.v(n), Pick.v(r)}, Srcs{Pick.src(c), Pick.src(k), Pick.src(m), Pick.src(n), Pick.src(r)}}

def fill.with(+t: Toggle, +set: Lims, +ps: List<&2, Lims>, +own: Lims, +table: Lims) -> Filled:
  fill.done(one(B.Cost{}, t, set, ps, own, table), one(B.Tok{}, t, set, ps, own, table), one(B.Time{}, t, set, ps, own, table), one(B.Calls{}, t, set, ps, own, table), one(B.Reqs{}, t, set, ps, own, table))

# The limits of a run of kind k paid by a: set (the principal's limits
# for this run), the presets in the order given, own (the principal's
# profile for the kind)
def fill(t: Toggle, k: Run, a: Auth, set: Lims, ps: List<&2, Lims>, own: Lims) -> Filled:
  fill.with(t, set, ps, own, profile(k, a))

# Plan share
# ----------

def wraps.at(over: Bool, i: Nat, rest: Maybe<&2, Nat>) -> Maybe<&2, Nat>:
  match over:
    case True{}:
      Some{i}
    case False{}:
      rest

def wraps.go(us: List<&2, Nat>, +line: Nat, +i: Nat) -> Maybe<&2, Nat>:
  match us:
    case Nil{}:
      None{}
    case Con{u, t}:
      wraps.at(Nat.is_le(line, u), i, wraps.go(t, line, 1n+i))

# the place of the first window whose used permille is at or past
# 1000 - reserve
def plan_wraps(us: List<&2, Nat>, reserve: Nat) -> Maybe<&2, Nat>:
  wraps.go(us, Nat.sub(1000n, reserve), 0n)

# A plan window's last reading: its label and its used permille
type Win is Data:
  Win{label: String, used: Nat}

# The windows to tell of now (their places) and the labels told of
type Told is Data:
  Told{now: List<&2, Nat>, told: List<&2, String>}

def same.chr(p: U32, q: U32, rest: Bool) -> Bool:
  Bool.and(U32.is_eq(p, q), rest)

# a and b are the same chars
def same(a: String, b: String) -> Bool:
  match a b:
    case SNil{} SNil{}:
      True{}
    case SNil{} SCon{y, v}:
      False{}
    case SCon{x, u} SNil{}:
      False{}
    case SCon{Chr{p}, u} SCon{Chr{q}, v}:
      same.chr(p, q, same(u, v))

def has.or(hit: Bool, rest: Bool) -> Bool:
  match hit:
    case True{}:
      True{}
    case False{}:
      rest

# a label of ls is s
def has(+s: String, ls: List<&2, String>) -> Bool:
  match ls:
    case Nil{}:
      False{}
    case Con{h, t}:
      has.or(same(h, s), has(s, t))

def drop.keep(hit: Bool, h: String, rest: List<&2, String>) -> List<&2, String>:
  match hit:
    case True{}:
      rest
    case False{}:
      h <> rest

# ls without s
def drop(+s: String, ls: List<&2, String>) -> List<&2, String>:
  match ls:
    case Nil{}:
      Nil{}
    case Con{+h, t}:
      drop.keep(same(h, s), h, drop(s, t))

def notice.new(seen: Bool, i: Nat, +label: String, now: List<&2, Nat>, told: List<&2, String>) -> Told:
  match seen:
    case True{}:
      Told{now, told}
    case False{}:
      Told{List.append(&2, Nat, now, [i]), label <> told}

def notice.win(over: Bool, i: Nat, +label: String, now: List<&2, Nat>, +told: List<&2, String>) -> Told:
  match over:
    case True{}:
      notice.new(has(label, told), i, label, now, told)
    case False{}:
      Told{now, drop(label, told)}

def notice.step(acc: Told, over: Bool, i: Nat, label: String) -> Told:
  match acc:
    case Told{now, told}:
      notice.win(over, i, label, now, told)

# the windows ws (the first at place i) told of after acc
def notice.go(ws: List<&2, Win>, +line: Nat, +i: Nat, acc: Told) -> Told:
  match ws:
    case Nil{}:
      acc
    case Con{Win{label, u}, t}:
      notice.go(t, line, 1n+i, notice.step(acc, Nat.is_le(line, u), i, label))

# The windows to tell of: each reading at or past 1000 - reserve permille
# whose label was not told of; a reading below it forgets its label
def plan_notice(ws: List<&2, Win>, reserve: Nat, told: List<&2, String>) -> Told:
  notice.go(ws, Nat.sub(1000n, reserve), 0n, Told{Nil{}, told})

# Floor
# -----

def bound(v: Val, x: Nat) -> Nat:
  match v:
    case Unset{}:
      0n
    case At{n}:
      x
    case Unlimited{}:
      0n

def cap(v: Val) -> Nat:
  match v:
    case Unset{}:
      0n
    case At{n}:
      n
    case Unlimited{}:
      0n

# an ask counted only in the dimensions the limits bound
def bounded(l: Lims, c: B.Ask) -> B.Ask:
  match l c:
    case Lims{lc, lk, lm, ln, lr} B.Ask{B.Amt{xc, xk, xn, xr}, m}:
      B.Ask{B.Amt{bound(lc, xc), bound(lk, xk), bound(ln, xn), bound(lr, xr)}, bound(lm, m)}

def caps(l: Lims) -> B.Amt:
  match l:
    case Lims{lc, lk, lm, ln, lr}:
      B.Amt{cap(lc), cap(lk), cap(ln), cap(lr)}

# The first dimension in which limits l cannot hold the run's first work
# request c with its final-answer reserve keep, if any; an unbounded
# dimension holds anything
def floor(+l: Lims, c: B.Ask, keep: B.Ask) -> Maybe<&2, B.Dim>:
  B.lack(B.need(B.Work{}, B.Ask{B.zero(), 0n}, bounded(l, keep), bounded(l, c)), caps(l), 0n, cap(Lims.ms(l)))

# Renewal
# -------

def hold.amt(h: B.Hold) -> B.Amt:
  match h:
    case B.Hold{id, x}:
      x

# what the holds hold in all
def holding(hs: List<&2, B.Hold>) -> B.Amt:
  match hs:
    case Nil{}:
      B.zero()
    case Con{h, t}:
      B.add4(hold.amt(h), holding(t))

def renew.dim(v: Val, f: Nat, used: Nat) -> Nat:
  match v:
    case Unset{}:
      f
    case At{n}:
      Nat.sub(n, used)
    case Unlimited{}:
      f

def renew.until(v: Val, now: Nat, u: Nat) -> Nat:
  match v:
    case Unset{}:
      u
    case At{m}:
      Nat.add(now, m)
    case Unlimited{}:
      u

def renew.free(l: Lims, f: B.Amt, used: B.Amt) -> B.Amt:
  match l f used:
    case Lims{lc, lk, lm, ln, lr} B.Amt{fc, fk, fn, fr} B.Amt{uc, uk, un, ur}:
      B.Amt{renew.dim(lc, fc, uc), renew.dim(lk, fk, uk), renew.dim(ln, fn, un), renew.dim(lr, fr, ur)}

# An account's free in each bounded dimension becomes its limit less what
# the run used: spent since mark (the account's spent when the run
# started), held and lent; a time limit puts the deadline at now plus it.
# Spent, lent, the overrun and the holds stay.
def renew(+l: Lims, mark: B.Amt, now: Nat, a: B.Acct) -> B.Acct:
  match a:
    case B.Acct{f, +sp, +le, o, +hs, u}:
      B.Acct{renew.free(l, f, B.add4(B.sub4(sp, mark), B.add4(holding(hs), le))), sp, le, o, hs, renew.until(Lims.ms(l), now, u)}

# Prefix
# ------

# A key of a pair
type Key is Data:
  KCost{}
  KTok{}
  KTime{}
  KCalls{}
  KReqs{}

# A key=value word: its key and its value as read
type KV is Data:
  KV{key: Key, value: String}

# The words of a `/b` prefix and the message after them; or the word
# that is refused
type Prefix is Data:
  Read{presets: List<&2, Nat>, pairs: List<&2, KV>, rest: String}
  Refused{word: String}

def fold.space(wide: Bool, c: Char) -> Char:
  match wide:
    case True{}:
      ' '
    case False{}:
      c

def fold.in(form: Bool, +n: Nat, c: Char) -> Char:
  match form:
    case True{}:
      Chr{U32.from_nat(Nat.sub(n, 65248n))}
    case False{}:
      fold.space(Nat.is_eq(n, 12288n), c)

def fold.code(+n: Nat, c: Char) -> Char:
  fold.in(Bool.and(Nat.is_le(65281n, n), Nat.is_le(n, 65374n)), n, c)

# the char a full-width form reads as (NFKC): U+FF01..U+FF5E as
# U+0021..U+007E, U+3000 as a space; any other char as itself
def fold(c: Char) -> Char:
  match c:
    case Chr{+x}:
      fold.code(U32.to_nat(x), Chr{x})

def code.of(c: Char) -> Nat:
  match c:
    case Chr{x}:
      U32.to_nat(x)

# the code of a char folded
def code(c: Char) -> Nat:
  code.of(fold(c))

def is_space.n(+n: Nat) -> Bool:
  Bool.or(Nat.is_eq(n, 32n), Bool.or(Nat.is_eq(n, 9n), Bool.or(Nat.is_eq(n, 10n), Nat.is_eq(n, 13n))))

# a space ends a word: space, tab, line feed, carriage return (folded)
def is_space(c: Char) -> Bool:
  is_space.n(code(c))

def skip.at(sp: Bool, c: Char, t: String, after: String) -> String:
  match sp:
    case True{}:
      after
    case False{}:
      SCon{c, t}

# s without its leading spaces
def skip(s: String) -> String:
  match s:
    case SNil{}:
      SNil{}
    case SCon{+c, +t}:
      skip.at(is_space(c), c, t, skip(t))

# A text cut in two
type Cut is Data:
  Cut{a: String, b: String}

def word.cons(c: Char, p: Cut) -> Cut:
  match p:
    case Cut{w, r}:
      Cut{SCon{c, w}, r}

def word.at(sp: Bool, c: Char, t: String, after: Cut) -> Cut:
  match sp:
    case True{}:
      Cut{SNil{}, SCon{c, t}}
    case False{}:
      word.cons(c, after)

# the word at the start of s (up to a space) and what follows it
def word(s: String) -> Cut:
  match s:
    case SNil{}:
      Cut{SNil{}, SNil{}}
    case SCon{+c, +t}:
      word.at(is_space(c), c, t, word(t))

# the chars of s folded
def folded(s: String) -> String:
  match s:
    case SNil{}:
      SNil{}
    case SCon{c, t}:
      SCon{fold(c), folded(t)}

def decimal.at(comma: Bool, c: Char) -> Char:
  match comma:
    case True{}:
      '.'
    case False{}:
      fold(c)

# the chars of a value folded, a comma read as a point
def decimal(s: String) -> String:
  match s:
    case SNil{}:
      SNil{}
    case SCon{+c, t}:
      SCon{decimal.at(Nat.is_eq(code(c), 44n), c), decimal(t)}

def named.at(hit: Bool, i: Nat, after: Maybe<&2, Nat>) -> Maybe<&2, Nat>:
  match hit:
    case True{}:
      Some{i}
    case False{}:
      after

# the place of the first name of ns that is w
def named(+w: String, ns: List<&2, String>, +i: Nat) -> Maybe<&2, Nat>:
  match ns:
    case Nil{}:
      None{}
    case Con{n, t}:
      named.at(same(w, n), i, named(w, t, 1n+i))

def key.is(hit: Bool, k: Key, rest: Maybe<&2, Key>) -> Maybe<&2, Key>:
  match hit:
    case True{}:
      Some{k}
    case False{}:
      rest

# the key a folded word before its '=' names
def key(+k: String) -> Maybe<&2, Key>:
  key.is(same(k, "cost"), KCost{}, key.is(same(k, "tokens"), KTok{}, key.is(same(k, "time"), KTime{}, key.is(same(k, "calls"), KCalls{}, key.is(same(k, "requests"), KReqs{}, None{})))))

def split.cons(c: Char, m: Maybe<&2, Cut>) -> Maybe<&2, Cut>:
  match m:
    case None{}:
      None{}
    case Some{Cut{a, b}}:
      Some{Cut{SCon{c, a}, b}}

def split.at(eq: Bool, c: Char, t: String, after: Maybe<&2, Cut>) -> Maybe<&2, Cut>:
  match eq:
    case True{}:
      Some{Cut{SNil{}, t}}
    case False{}:
      split.cons(c, after)

# the word before its first '=' and the word after it, if it has one
def split(s: String) -> Maybe<&2, Cut>:
  match s:
    case SNil{}:
      None{}
    case SCon{+c, +t}:
      split.at(Nat.is_eq(code(c), 61n), c, t, split(t))

def key_is(a: Key, b: Key) -> Bool:
  match a b:
    case KCost{} KCost{}:
      True{}
    case KTok{} KTok{}:
      True{}
    case KTime{} KTime{}:
      True{}
    case KCalls{} KCalls{}:
      True{}
    case KReqs{} KReqs{}:
      True{}
    case _ _:
      False{}

def pair.key(p: KV) -> Key:
  match p:
    case KV{k, v}:
      k

# a pair of ps has key k
def given(+k: Key, ps: List<&2, KV>) -> Bool:
  match ps:
    case Nil{}:
      False{}
    case Con{p, t}:
      Bool.or(key_is(pair.key(p), k), given(k, t))

# What a word of the prefix is
type Wd is Data:
  WPreset{i: Nat}
  WPair{p: KV}
  WBad{}
  WEnd{}

def pair.at(bad: Bool, k: Key, v: String) -> Wd:
  match bad:
    case True{}:
      WBad{}
    case False{}:
      WPair{KV{k, decimal(v)}}

# a word with a known key before its '=': a pair, refused when its value
# is empty or its key was given
def pair(+k: Key, +v: String, ps: List<&2, KV>) -> Wd:
  pair.at(Bool.or(String.is_empty(v), given(k, ps)), k, v)

def word_kv.key(m: Maybe<&2, Key>, v: String, ps: List<&2, KV>) -> Wd:
  match m:
    case None{}:
      WEnd{}
    case Some{k}:
      pair(k, v, ps)

def word_kv(m: Maybe<&2, Cut>, ps: List<&2, KV>) -> Wd:
  match m:
    case None{}:
      WEnd{}
    case Some{Cut{k, v}}:
      word_kv.key(key(folded(k)), v, ps)

def classify.at(m: Maybe<&2, Nat>, w: String, ps: List<&2, KV>) -> Wd:
  match m:
    case Some{i}:
      WPreset{i}
    case None{}:
      word_kv(split(w), ps)

# what word w is: a preset name, a key=value pair, refused, or the start
# of the message
def classify(+w: String, ns: List<&2, String>, ps: List<&2, KV>) -> Wd:
  classify.at(named(folded(w), ns, 0n), w, ps)

# Where the reading of the prefix is: the input left, the presets and
# pairs so far (reversed); or done
type St is Data:
  Reading{s: String, ks: List<&2, Nat>, ps: List<&2, KV>}
  Finished{p: Prefix}

def words.on(x: Wd, w: String, r: String, ks: List<&2, Nat>, ps: List<&2, KV>, s: String) -> St:
  match x:
    case WPreset{i}:
      Reading{r, i <> ks, ps}
    case WPair{p}:
      Reading{r, ks, p <> ps}
    case WBad{}:
      Finished{Refused{w}}
    case WEnd{}:
      Finished{Read{List.reverse(&2, Nat, ks), List.reverse(&2, KV, ps), s}}

def words.word(p: Cut, ns: List<&2, String>, ks: List<&2, Nat>, +ps: List<&2, KV>, s: String) -> St:
  match p:
    case Cut{+w, r}:
      words.on(classify(w, ns, ps), w, r, ks, ps, s)

def words.at(s: String, ns: List<&2, String>, ks: List<&2, Nat>, ps: List<&2, KV>) -> St:
  match s:
    case SNil{}:
      Finished{Read{List.reverse(&2, Nat, ks), List.reverse(&2, KV, ps), ""}}
    case SCon{+c, +t}:
      words.word(word(SCon{c, t}), ns, ks, ps, SCon{c, t})

# the next word of the prefix
def words.step(st: St, ns: List<&2, String>) -> St:
  match st:
    case Reading{s, ks, ps}:
      words.at(skip(s), ns, ks, ps)
    case Finished{p}:
      Finished{p}

def words.end(st: St) -> Prefix:
  match st:
    case Reading{s, ks, ps}:
      Read{List.reverse(&2, Nat, ks), List.reverse(&2, KV, ps), s}
    case Finished{p}:
      p

# at most f more words (each word takes a char at least)
def words.go(f: Nat, st: St, +ns: List<&2, String>) -> Prefix:
  match f:
    case 0n:
      words.end(st)
    case 1n+g:
      words.go(g, words.step(st, ns), ns)

# read the words of s
def words(+s: String, ns: List<&2, String>) -> Prefix:
  words.go(1n+String.length(s), Reading{s, Nil{}, Nil{}}, ns)

def prefix.at(b: Bool, r: String, ns: List<&2, String>, s: String) -> Prefix:
  match b:
    case True{}:
      words(r, ns)
    case False{}:
      Read{Nil{}, Nil{}, s}

def prefix.word(p: Cut, ns: List<&2, String>, s: String) -> Prefix:
  match p:
    case Cut{w, r}:
      prefix.at(same(folded(w), "/b"), r, ns, s)

# The `/b` prefix of a message s, with ns the preset names: s starts with
# `/b` (folded) then a space or its end; otherwise no prefix and the
# message is s
def prefix(+s: String, ns: List<&2, String>) -> Prefix:
  prefix.word(word(s), ns, s)
