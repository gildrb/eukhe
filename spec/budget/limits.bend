# limits (spec): what the laws of area limits (laws/limits.bend) speak
# of, over the types of bend/limits.bend and bend/budget.bend. A spec: the
# shipped code never calls it.
#
# S1: each of a run's five dimensions (money, tokens, time, tool calls,
#     model requests) takes a limit and its source: what the principal
#     set for the run; else the last `/b` preset, in the order typed, that
#     gives the dimension; else, with limits on, the principal's profile
#     for the kind, else the limits profile; else unlimited, until
#     finished: a dimension left unset is unlimited, its source until
#     finished (default) (B1, B15, B16).
# S2: the limits profile gives a number to time and model requests of
#     every run and to tool calls of a run paid by a plan or an API key;
#     never to money or tokens (B15).
# S3: a plan run wraps up at the first quota window whose last reading
#     is at or past 1000 - reserve permille used (B18).
# S4: with limits off, a window is told of when its reading reaches that
#     line, once, until a reading below it: a label stays told of while
#     no window of it reads below the line (B23).
# S5: a run's limits hold its first request when the reservation of B1
#     on an account holding exactly those limits grants it; a dimension
#     without a number takes no part: the limits hold the request as the
#     same limits with that dimension a limit of 0 hold the request asking
#     nothing of it (B17).
# S6: renewal: in each bounded dimension what is free plus what the run
#     used (spent since its start, held, lent) is the limit, or the use
#     when it passed the limit (B19).
# S7: the `/b` prefix, read word by word: a message whose first word does
#     not fold to `/b` is untouched; after it, each preset name its place
#     and each key=value pair its key and value (folded, `,` as `.`) in
#     order, an empty value or a key given before refused with the word as
#     typed, up to the first other word, from which on the message is the
#     rest verbatim (B20).

import Base
import ../../bend/budget.bend as B
import ../../bend/limits.bend as L
import ./ledger.bend as S

# Fill (S1)
# ---------

# the limit of dimension d in l
def dim(d: B.Dim, l: L.Lims) -> L.Val:
  match d l:
    case B.Cost{} L.Lims{c, k, m, n, r}:
      c
    case B.Tok{} L.Lims{c, k, m, n, r}:
      k
    case B.Time{} L.Lims{c, k, m, n, r}:
      m
    case B.Calls{} L.Lims{c, k, m, n, r}:
      n
    case B.Reqs{} L.Lims{c, k, m, n, r}:
      r

# the source of dimension d in x
def src(d: B.Dim, x: L.Srcs) -> L.Src:
  match d x:
    case B.Cost{} L.Srcs{c, k, m, n, r}:
      c
    case B.Tok{} L.Srcs{c, k, m, n, r}:
      k
    case B.Time{} L.Srcs{c, k, m, n, r}:
      m
    case B.Calls{} L.Srcs{c, k, m, n, r}:
      n
    case B.Reqs{} L.Srcs{c, k, m, n, r}:
      r

# dimension d of a run's filled limits: its limit and its source
def filled(+d: B.Dim, f: L.Filled) -> L.Pick:
  match f:
    case L.Filled{l, x}:
      L.Pick{dim(d, l), src(d, x)}

# v gives a limit: a number or unlimited
def given(v: L.Val) -> Bool:
  match v:
    case L.Unset{}:
      False{}
    case L.At{n}:
      True{}
    case L.Unlimited{}:
      True{}

# the limit and the place of the first of ps (the first at place i) that
# gives d
# the same pick one place further on
def bump(p: L.Pick) -> L.Pick:
  match p:
    case L.Pick{v, L.Preset{j}}:
      L.Pick{v, L.Preset{1n+j}}
    case L.Pick{v, L.UntilFinished{}}:
      L.Pick{v, L.UntilFinished{}}
    case L.Pick{v, L.Set{}}:
      L.Pick{v, L.Set{}}
    case L.Pick{v, L.LimitsProfile{}}:
      L.Pick{v, L.LimitsProfile{}}
    case L.Pick{v, L.Profile{}}:
      L.Pick{v, L.Profile{}}

def last.at(later: Maybe<&2, L.Pick>, hit: Bool, v: L.Val) -> Maybe<&2, L.Pick>:
  match later:
    case Some{p}:
      Some{bump(p)}
    case None{}:
      match hit:
        case True{}:
          Some{L.Pick{v, L.Preset{0n}}}
        case False{}:
          None{}

# the last preset of ps that gives d, with its place in ps: one after the
# first gives it unless none does
def last(+d: B.Dim, ps: List<&2, L.Lims>) -> Maybe<&2, L.Pick>:
  match ps:
    case Nil{}:
      None{}
    case Con{+h, t}:
      last.at(last(d, t), given(dim(d, h)), dim(d, h))

# with limits on and nothing else given: the limits profile's number,
# else until finished
def table(v: L.Val) -> L.Pick:
  match v:
    case L.Unset{}:
      L.Pick{L.Unlimited{}, L.UntilFinished{}}
    case L.At{n}:
      L.Pick{L.At{n}, L.LimitsProfile{}}
    case L.Unlimited{}:
      L.Pick{L.Unlimited{}, L.UntilFinished{}}

# the tag of v: 0 unset, 1 a number, 2 unlimited
def tag(v: L.Val) -> Nat:
  match v:
    case L.Unset{}:
      0n
    case L.At{n}:
      1n
    case L.Unlimited{}:
      2n

# the number of v (0 when it has none) and whether it has one
def num(v: L.Val) -> Nat:
  match v:
    case L.Unset{}:
      0n
    case L.At{n}:
      n
    case L.Unlimited{}:
      0n

def is_at(v: L.Val) -> Bool:
  match v:
    case L.Unset{}:
      False{}
    case L.At{n}:
      True{}
    case L.Unlimited{}:
      False{}

# the deadline a renewal sets: now plus a time limit, else the deadline
# as it was
def deadline(v: L.Val, now: Nat, u: Nat) -> Nat:
  match v:
    case L.Unset{}:
      u
    case L.At{m}:
      Nat.add(now, m)
    case L.Unlimited{}:
      u

# Plan share (S3, S4)
# -------------------

def succ(m: Maybe<&2, Nat>) -> Maybe<&2, Nat>:
  match m:
    case None{}:
      None{}
    case Some{i}:
      Some{1n+i}

# the place of the first of us at or past line
def over.at(hit: Bool, rest: Maybe<&2, Nat>) -> Maybe<&2, Nat>:
  match hit:
    case True{}:
      Some{0n}
    case False{}:
      succ(rest)

def over(us: List<&2, Nat>, +line: Nat) -> Maybe<&2, Nat>:
  match us:
    case Nil{}:
      None{}
    case Con{u, t}:
      over.at(Nat.is_le(line, u), over(t, line))

# a and b are the same text
def same(a: String, b: String) -> Bool:
  match a b:
    case SNil{} SNil{}:
      True{}
    case SNil{} SCon{y, v}:
      False{}
    case SCon{x, u} SNil{}:
      False{}
    case SCon{Chr{p}, u} SCon{Chr{q}, v}:
      Bool.and(U32.is_eq(p, q), same(u, v))

# a text of ls is s
def among(+s: String, ls: List<&2, String>) -> Bool:
  match ls:
    case Nil{}:
      False{}
    case Con{h, t}:
      Bool.or(same(s, h), among(s, t))

def now(t: L.Told) -> List<&2, Nat>:
  match t:
    case L.Told{n, l}:
      n

def told(t: L.Told) -> List<&2, String>:
  match t:
    case L.Told{n, l}:
      l

def label(w: L.Win) -> String:
  match w:
    case L.Win{l, u}:
      l

def used(w: L.Win) -> Nat:
  match w:
    case L.Win{l, u}:
      u

# the labels of ws
def labels(ws: List<&2, L.Win>) -> List<&2, String>:
  match ws:
    case Nil{}:
      Nil{}
    case Con{w, t}:
      label(w) <> labels(t)

# no two windows of ws share a label
def distinct(ws: List<&2, L.Win>) -> Bool:
  match ws:
    case Nil{}:
      True{}
    case Con{w, +t}:
      Bool.and(Bool.not(among(label(w), labels(t))), distinct(t))

def shift(xs: List<&2, Nat>) -> List<&2, Nat>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{h, t}:
      (1n+h) <> shift(t)

def fresh.at(hit: Bool, rest: List<&2, Nat>) -> List<&2, Nat>:
  match hit:
    case True{}:
      0n <> rest
    case False{}:
      rest

# the places of the windows of ws at or past line whose label is not in
# told
def fresh(ws: List<&2, L.Win>, +line: Nat, +told: List<&2, String>) -> List<&2, Nat>:
  match ws:
    case Nil{}:
      Nil{}
    case Con{+w, t}:
      fresh.at(Bool.and(Nat.is_le(line, used(w)), Bool.not(among(label(w), told))), shift(fresh(t, line, told)))

# a window of ws below line has label s
def below(+s: String, ws: List<&2, L.Win>, +line: Nat) -> Bool:
  match ws:
    case Nil{}:
      False{}
    case Con{+w, t}:
      Bool.or(Bool.and(same(s, label(w)), Nat.is_lt(used(w), line)), below(s, t, line))

# a window of ws at or past line has label s
def reached(+s: String, ws: List<&2, L.Win>, +line: Nat) -> Bool:
  match ws:
    case Nil{}:
      False{}
    case Con{+w, t}:
      Bool.or(Bool.and(same(s, label(w)), Nat.is_le(line, used(w))), reached(s, t, line))

# label s is told of after the readings ws: a window of it is at or past
# line, or it was told of and no window of it read below line (S4)
def told_after(+s: String, +ws: List<&2, L.Win>, +line: Nat, told: List<&2, String>) -> Bool:
  Bool.or(reached(s, ws, line), Bool.and(among(s, told), Bool.not(below(s, ws, line))))

# Floor (S5)
# ----------

# every dimension of l is a number
def bounded(l: L.Lims) -> Bool:
  match l:
    case L.Lims{c, k, m, n, r}:
      Bool.and(is_at(c), Bool.and(is_at(k), Bool.and(is_at(m), Bool.and(is_at(n), is_at(r)))))

# an account holding exactly limits l, with nothing spent, at time 0
def fresh_acct(l: L.Lims) -> B.Acct:
  match l:
    case L.Lims{c, k, m, n, r}:
      B.Acct{B.Amt{num(c), num(k), num(n), num(r)}, B.zero(), B.zero(), B.zero(), Nil{}, num(m)}

# x when b holds, else 0
def keep_if(b: Bool, x: Nat) -> Nat:
  match b:
    case True{}:
      x
    case False{}:
      0n

# l with every dimension a number: its own, 0 for one without
def closed(l: L.Lims) -> L.Lims:
  match l:
    case L.Lims{c, k, m, n, r}:
      L.Lims{L.At{num(c)}, L.At{num(k)}, L.At{num(m)}, L.At{num(n)}, L.At{num(r)}}

# ask a in the dimensions limits l give a number, 0 in the others
def only(l: L.Lims, a: B.Ask) -> B.Ask:
  match l a:
    case L.Lims{c, k, m, n, r} B.Ask{B.Amt{xc, xk, xn, xr}, xm}:
      B.Ask{B.Amt{keep_if(is_at(c), xc), keep_if(is_at(k), xk), keep_if(is_at(n), xn), keep_if(is_at(r), xr)}, keep_if(is_at(m), xm)}

# the dimension a reservation was refused for, if it was
def short(g: B.Grant) -> Maybe<&2, B.Dim>:
  match g:
    case B.Granted{i, c, a, lo}:
      None{}
    case B.Refused{w, p}:
      match w:
        case B.Short{d}:
          Some{d}
        case B.Held{}:
          None{}
        case B.Stopped{}:
          None{}

def dim_is(a: B.Dim, b: B.Dim) -> Bool:
  match a b:
    case B.Cost{} B.Cost{}:
      True{}
    case B.Tok{} B.Tok{}:
      True{}
    case B.Time{} B.Time{}:
      True{}
    case B.Calls{} B.Calls{}:
      True{}
    case B.Reqs{} B.Reqs{}:
      True{}
    case _ _:
      False{}

# m names dimension d
def names(+d: B.Dim, m: Maybe<&2, B.Dim>) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{e}:
      dim_is(d, e)

# Renewal (S6)
# ------------

# what a run used of account a in spent dimension d since mark: spent
# since mark, held, lent
def use(+d: B.Dim, mark: B.Amt, a: B.Acct) -> Nat:
  match a:
    case B.Acct{f, s, l, o, hs, u}:
      Nat.add(Nat.sub(S.at(d, s), S.at(d, mark)), Nat.add(S.held(d, hs), S.at(d, l)))

# d is a spent dimension (time is not)
def spent_dim(d: B.Dim) -> Bool:
  match d:
    case B.Cost{}:
      True{}
    case B.Tok{}:
      True{}
    case B.Time{}:
      False{}
    case B.Calls{}:
      True{}
    case B.Reqs{}:
      True{}

# Prefix (S7)
# -----------

def fold.space(sp: Bool, c: Char) -> Char:
  match sp:
    case True{}:
      ' '
    case False{}:
      c

def fold.wide(lo: Bool, hi: Bool, +x: U32, c: Char) -> Char:
  match lo hi:
    case True{} True{}:
      Chr{U32.sub(x, 65248)}
    case True{} False{}:
      fold.space(U32.is_eq(x, 12288), c)
    case False{} True{}:
      fold.space(U32.is_eq(x, 12288), c)
    case False{} False{}:
      fold.space(U32.is_eq(x, 12288), c)

# the char c reads as (NFKC of the full-width forms): U+FF01..U+FF5E as
# U+0021..U+007E, the ideographic space U+3000 as a space, any other char
# as itself
def fold(c: Char) -> Char:
  match c:
    case Chr{+x}:
      fold.wide(U32.is_le(65281, x), U32.is_le(x, 65374), x, Chr{x})

# the code point of c
def code(c: Char) -> Nat:
  match c:
    case Chr{x}:
      U32.to_nat(x)

def folded(s: String) -> String:
  match s:
    case SNil{}:
      SNil{}
    case SCon{c, t}:
      SCon{fold(c), folded(t)}

def white(+n: Nat) -> Bool:
  Bool.or(Nat.is_eq(n, 32n), Bool.or(Nat.is_eq(n, 9n), Bool.or(Nat.is_eq(n, 10n), Nat.is_eq(n, 13n))))

# c reads as a space: space, tab, line feed, carriage return (folded)
def space(c: Char) -> Bool:
  white(code(fold(c)))

# every char of s is a space (s may be empty)
def spaces(s: String) -> Bool:
  match s:
    case SNil{}:
      True{}
    case SCon{c, t}:
      Bool.and(space(c), spaces(t))

# no char of s is a space (s may be empty)
def dense(s: String) -> Bool:
  match s:
    case SNil{}:
      True{}
    case SCon{c, t}:
      Bool.and(Bool.not(space(c)), dense(t))

# a gap between words: one space or more
def gap(s: String) -> Bool:
  match s:
    case SNil{}:
      False{}
    case SCon{c, t}:
      Bool.and(space(c), spaces(t))

# a word: one char or more, none a space
def solid(s: String) -> Bool:
  match s:
    case SNil{}:
      False{}
    case SCon{c, t}:
      Bool.and(Bool.not(space(c)), dense(t))

def lead.at(sp: Bool, c: Char, after: String) -> String:
  match sp:
    case True{}:
      SNil{}
    case False{}:
      SCon{c, after}

# the chars of s before its first space
def lead(s: String) -> String:
  match s:
    case SNil{}:
      SNil{}
    case SCon{+c, t}:
      lead.at(space(c), c, lead(t))

# s opens with `/b` (folded), then a space or its end
def opens(s: String) -> Bool:
  same(folded(lead(s)), "/b")

# the chars a b read as `/b`
def opener(a: Char, b: Char) -> Bool:
  same(folded(SCon{a, SCon{b, SNil{}}}), "/b")

# A word of a `/b` message and the gap before it
type Item is Data:
  Item{gap: String, word: String}

# the words of a `/b` message after its opener, each after its gap, then
# the trailing text t
def spell(xs: List<&2, Item>, t: String) -> String:
  match xs:
    case Nil{}:
      t
    case Con{x, rest}:
      match x:
        case Item{g, w}:
          String.append(g, String.append(w, spell(rest, t)))

def items.at(x: Item, more: Bool) -> Bool:
  match x:
    case Item{g, w}:
      Bool.and(gap(g), Bool.and(solid(w), more))

# every gap of xs is one space or more, every word one char or more
# without a space
def items(xs: List<&2, Item>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{x, rest}:
      items.at(x, items(rest))

def first(hit: Bool, i: Nat, after: Maybe<&2, Nat>) -> Maybe<&2, Nat>:
  match hit:
    case True{}:
      Some{i}
    case False{}:
      after

# the place of the first name of ns (the first at place i) that is w
def named(+w: String, ns: List<&2, String>, +i: Nat) -> Maybe<&2, Nat>:
  match ns:
    case Nil{}:
      None{}
    case Con{n, t}:
      first(same(w, n), i, named(w, t, 1n+i))

def cut.cons(c: Char, m: Maybe<&2, L.Cut>) -> Maybe<&2, L.Cut>:
  match m:
    case None{}:
      None{}
    case Some{L.Cut{a, b}}:
      Some{L.Cut{SCon{c, a}, b}}

def cut.at(eq: Bool, c: Char, t: String, after: Maybe<&2, L.Cut>) -> Maybe<&2, L.Cut>:
  match eq:
    case True{}:
      Some{L.Cut{SNil{}, t}}
    case False{}:
      cut.cons(c, after)

# the chars of s before its first `=` (folded) and those after it, if it
# has one
def eq_cut(s: String) -> Maybe<&2, L.Cut>:
  match s:
    case SNil{}:
      None{}
    case SCon{+c, +t}:
      cut.at(Nat.is_eq(code(fold(c)), 61n), c, t, eq_cut(t))

def key.at(hit: Bool, k: L.Key, after: Maybe<&2, L.Key>) -> Maybe<&2, L.Key>:
  match hit:
    case True{}:
      Some{k}
    case False{}:
      after

# the key a pair's folded key word names
def key(+k: String) -> Maybe<&2, L.Key>:
  key.at(same(k, "cost"), L.KCost{}, key.at(same(k, "tokens"), L.KTok{}, key.at(same(k, "time"), L.KTime{}, key.at(same(k, "calls"), L.KCalls{}, key.at(same(k, "requests"), L.KReqs{}, None{})))))

def key_tag(k: L.Key) -> Nat:
  match k:
    case L.KCost{}:
      0n
    case L.KTok{}:
      1n
    case L.KTime{}:
      2n
    case L.KCalls{}:
      3n
    case L.KReqs{}:
      4n

def kv_key(p: L.KV) -> L.Key:
  match p:
    case L.KV{k, v}:
      k

# a pair of ps has key k
def keyed(+k: L.Key, ps: List<&2, L.KV>) -> Bool:
  match ps:
    case Nil{}:
      False{}
    case Con{p, t}:
      Bool.or(Nat.is_eq(key_tag(kv_key(p)), key_tag(k)), keyed(k, t))

def point(comma: Bool, c: Char) -> Char:
  match comma:
    case True{}:
      '.'
    case False{}:
      fold(c)

# a pair's value as read: folded, a comma as a point
def decimal(s: String) -> String:
  match s:
    case SNil{}:
      SNil{}
    case SCon{+c, t}:
      SCon{point(Nat.is_eq(code(fold(c)), 44n), c), decimal(t)}

def word_kind.pair(bad: Bool, k: L.Key, v: String) -> L.Wd:
  match bad:
    case True{}:
      L.WBad{}
    case False{}:
      L.WPair{L.KV{k, decimal(v)}}

def word_kind.key(m: Maybe<&2, L.Key>, +v: String, seen: List<&2, L.KV>) -> L.Wd:
  match m:
    case None{}:
      L.WEnd{}
    case Some{+k}:
      word_kind.pair(Bool.or(String.is_empty(v), keyed(k, seen)), k, v)

def word_kind.kv(m: Maybe<&2, L.Cut>, seen: List<&2, L.KV>) -> L.Wd:
  match m:
    case None{}:
      L.WEnd{}
    case Some{L.Cut{k, v}}:
      word_kind.key(key(folded(k)), v, seen)

def word_kind.at(m: Maybe<&2, Nat>, w: String, seen: List<&2, L.KV>) -> L.Wd:
  match m:
    case Some{i}:
      L.WPreset{i}
    case None{}:
      word_kind.kv(eq_cut(w), seen)

# what word w of a `/b` prefix is, after the pairs seen: a preset name
# (folded) of ns, its place; else a known key (folded) before its first
# `=`, a pair, refused when its value is empty or its key was seen; else
# the word that ends the prefix
def word_kind(+w: String, ns: List<&2, String>, seen: List<&2, L.KV>) -> L.Wd:
  word_kind.at(named(folded(w), ns, 0n), w, seen)

# the pairs seen after word kind k
def after(k: L.Wd, seen: List<&2, L.KV>) -> List<&2, L.KV>:
  match k:
    case L.WPreset{i}:
      seen
    case L.WPair{p}:
      List.append(&2, L.KV, seen, [p])
    case L.WBad{}:
      seen
    case L.WEnd{}:
      seen

def with_preset(i: Nat, p: L.Prefix) -> L.Prefix:
  match p:
    case L.Read{ks, ps, r}:
      L.Read{i <> ks, ps, r}
    case L.Refused{w}:
      L.Refused{w}

def with_pair(kv: L.KV, p: L.Prefix) -> L.Prefix:
  match p:
    case L.Read{ks, ps, r}:
      L.Read{ks, kv <> ps, r}
    case L.Refused{w}:
      L.Refused{w}

def prefix_of.at(k: L.Wd, w: String, more: String, later: L.Prefix) -> L.Prefix:
  match k:
    case L.WPreset{i}:
      with_preset(i, later)
    case L.WPair{p}:
      with_pair(p, later)
    case L.WBad{}:
      L.Refused{w}
    case L.WEnd{}:
      L.Read{Nil{}, Nil{}, String.append(w, more)}

# what the words xs after a `/b` opener, then the trailing spaces t, read
# as, after the pairs seen: word by word, each preset's place and each
# pair in order, up to the first word that ends the prefix, which with all
# after it (gaps and t included) is the rest; a refused word as typed
def prefix_of(xs: List<&2, Item>, +t: String, +ns: List<&2, String>, +seen: List<&2, L.KV>) -> L.Prefix:
  match xs:
    case Nil{}:
      L.Read{Nil{}, Nil{}, ""}
    case Con{x, +rest}:
      match x:
        case Item{g, +w}:
          prefix_of.at(word_kind(w, ns, seen), w, spell(rest, t), prefix_of(rest, t, ns, after(word_kind(w, ns, seen), seen)))
