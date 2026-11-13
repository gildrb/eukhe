# limits (spec): what the laws of area limits (laws/limits.bend) speak
# of, over the types of bend/limits.bend and bend/budget.bend. A spec: the
# shipped code never calls it.
#
# S1: each of a run's five dimensions (money, tokens, time, tool calls,
#     model requests) takes a limit and its source: what the principal
#     set for the run; else the last `/b` preset, in the order typed, that
#     gives the dimension; else, with limits on, the principal's profile
#     for the kind, else the limits profile; else unlimited, until
#     finished (B15, B16).
# S2: the limits profile gives a number to time and model requests of
#     every run and to tool calls of a run paid by a plan or an API key;
#     never to money or tokens (B15).
# S3: a plan run wraps up at the first quota window whose last reading
#     is at or past 1000 - reserve permille used (B18).
# S4: with limits off, a window is told of when its reading reaches that
#     line, once, until a reading below it (B23).
# S5: a run's limits hold its first request when the reservation of B1
#     on an account holding exactly those limits grants it (B17).
# S6: renewal: in each bounded dimension what is free plus what the run
#     used (spent since its start, held, lent) is the limit, or the use
#     when it passed the limit (B19).

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
