# rebase (spec): the three-way rebase of a stale edit, restated without
# the rebase code (bend/rebase.bend): every copy of a window is listed and
# counted, where the code scans and stops at the second; rule 1 compares
# each edit with the one before, where the code carries a floor. The laws
# of area rebase (laws/rebase.bend) state that the code refines it. A
# spec: the shipped code never calls it.
#
# Lines are ids (equal ids: equal lines); an edit replaces the base lines
# [start, end) with its lines.
# S1: the edits are sorted and apart: each has start <= end <= the lines
#     there are, and, after the first, start > the previous start and
#     start >= the previous end; else Invalid at the first that breaks it.
# S2: a head with the same lines as the base takes the edits unchanged.
# S3: the window of an edit [s, t) with k lines of context: up to k lines
#     before s, the lines [s, t), up to k lines from t; anchored at the
#     file's start when k > s, at its end when t + k passes the lines.
#     A copy of a window in x is a place j (0 to the lines of x) where the
#     window's lines start the lines of x from j.
# S4: an edit tries the contexts k from 0 (from 1 for an insertion) to
#     ctx() = 8: no copy in the head, or its only copy not where the
#     anchors put it (an anchored start at 0, an anchored end at the last
#     line) -> Moved; exactly one copy in the base, where the anchors put
#     it, and exactly one in the head -> the edit lands at the head's copy
#     moved by the lines before s in the window, as long as it was, with
#     its lines; else the next context; past ctx() -> Ambiguous.
# S5: the first edit that fails refuses all (its index); the landed edits
#     obey S1 against the head, else Crossed at the first that does not.

import Base
import ../../bend/rebase.bend as R

# the most lines of context on each side
def ctx() -> Nat:
  8n

# Lines
# -----

# a and b are the same lines
def same(a: List<&2, Nat>, b: List<&2, Nat>) -> Bool:
  match a b:
    case Nil{} Nil{}:
      True{}
    case Nil{} Con{y, ys}:
      False{}
    case Con{x, xs} Nil{}:
      False{}
    case Con{x, xs} Con{y, ys}:
      Bool.and(Nat.is_eq(x, y), same(xs, ys))

# w is a prefix of y
def starts(w: List<&2, Nat>, y: List<&2, Nat>) -> Bool:
  match w y:
    case Nil{} _:
      True{}
    case Con{a, wt} Nil{}:
      False{}
    case Con{a, wt} Con{c, yt}:
      Bool.and(Nat.is_eq(a, c), starts(wt, yt))

def put(b: Bool, +j: Nat, r: List<&2, Nat>) -> List<&2, Nat>:
  match b:
    case True{}:
      j <> r
    case False{}:
      r

# every copy of w in x, x being the lines from j on
def copies.go(x: List<&2, Nat>, +w: List<&2, Nat>, +j: Nat) -> List<&2, Nat>:
  match x:
    case Nil{}:
      put(starts(w, Nil{}), j, Nil{})
    case Con{+c, +t}:
      put(starts(w, Con{c, t}), j, copies.go(t, w, 1n+j))

# S3: every copy of w in x
def copies(x: List<&2, Nat>, +w: List<&2, Nat>) -> List<&2, Nat>:
  copies.go(x, w, 0n)

# x holds two copies or more
def two(x: List<&2, Nat>) -> Bool:
  match x:
    case Nil{}:
      False{}
    case Con{a, r}:
      match r:
        case Nil{}:
          False{}
        case Con{c, rr}:
          True{}

# the lines [s, t) of x: what an edit replaces
def region(+x: List<&2, Nat>, e: R.Edit) -> List<&2, Nat>:
  match e:
    case R.Edit{+s, t, ls}:
      List.take(&2, Nat, List.drop(&2, Nat, x, s), Nat.sub(t, s))

# S1: sorted and apart
# --------------------

def after(p: Maybe<&2, R.Edit>, +s: Nat) -> Bool:
  match p:
    case None{}:
      True{}
    case Some{q}:
      match q:
        case R.Edit{ps, pe, pl}:
          Bool.and(Nat.is_lt(ps, s), Nat.is_le(pe, s))

def ok(e: R.Edit, p: Maybe<&2, R.Edit>, +n: Nat) -> Bool:
  match e:
    case R.Edit{+s, +t, ls}:
      Bool.and(Bool.and(Nat.is_le(s, t), Nat.is_le(t, n)), after(p, s))

def bad.of(b: Bool, +i: Nat, rest: Maybe<&2, Nat>) -> Maybe<&2, Nat>:
  match b:
    case True{}:
      rest
    case False{}:
      Some{i}

# the first edit of es (numbered from i, after p) that breaks S1
def bad.go(es: List<&2, R.Edit>, p: Maybe<&2, R.Edit>, +n: Nat, +i: Nat) -> Maybe<&2, Nat>:
  match es:
    case Nil{}:
      None{}
    case Con{+e, rest}:
      bad.of(ok(e, p, n), i, bad.go(rest, Some{e}, n, 1n+i))

def bad(es: List<&2, R.Edit>, +n: Nat) -> Maybe<&2, Nat>:
  bad.go(es, None{}, n, 0n)

def none(m: Maybe<&2, Nat>) -> Bool:
  match m:
    case None{}:
      True{}
    case Some{i}:
      False{}

# es obeys S1 against n lines
def valid(es: List<&2, R.Edit>, +n: Nat) -> Bool:
  none(bad(es, n))

# S3, S4: windows and contexts
# ----------------------------

# the window of [s, t) of b with k lines of context
def window(+b: List<&2, Nat>, +s: Nat, +t: Nat, +k: Nat) -> R.Win:
  +lo = Nat.sub(s, k)
  +lc = List.take(&2, Nat, List.drop(&2, Nat, b, lo), Nat.sub(s, lo))
  +rg = List.take(&2, Nat, List.drop(&2, Nat, b, s), Nat.sub(t, s))
  +rc = List.take(&2, Nat, List.drop(&2, Nat, b, t), k)
  R.Win{Nat.is_lt(s, k), List.append(&2, Nat, lc, List.append(&2, Nat, rg, rc)), Nat.is_lt(List.length(&2, Nat, b), Nat.add(t, k)), List.length(&2, Nat, lc), List.length(&2, Nat, rg)}

def lines(w: R.Win) -> List<&2, Nat>:
  match w:
    case R.Win{la, ls, ha, off, len}:
      ls

def at_start(la: Bool, +j: Nat) -> Bool:
  match la:
    case True{}:
      Nat.is_eq(j, 0n)
    case False{}:
      True{}

def at_end(ha: Bool, +j: Nat, +wl: Nat, +xl: Nat) -> Bool:
  match ha:
    case True{}:
      Nat.is_eq(Nat.add(j, wl), xl)
    case False{}:
      True{}

# the copy at j of wl lines in xl lines is where the anchors put it
def sits(la: Bool, ha: Bool, +j: Nat, +wl: Nat, +xl: Nat) -> Bool:
  Bool.and(at_start(la, j), at_end(ha, j, wl, xl))

def step.pick(ok: Bool, f: R.Edit, next: Unit -> R.Land) -> R.Land:
  match ok:
    case True{}:
      R.Lands{f}
    case False{}:
      next(Unit{})

def step.base(cb: List<&2, Nat>, la: Bool, ha: Bool, +wl: Nat, +bl: Nat, f: R.Edit, next: Unit -> R.Land) -> R.Land:
  match cb:
    case Nil{}:
      next(Unit{})
    case Con{x, more}:
      match more:
        case Nil{}:
          step.pick(sits(la, ha, x, wl, bl), f, next)
        case Con{y, rest}:
          next(Unit{})

def step.one(ok: Bool, cb: List<&2, Nat>, la: Bool, ha: Bool, +wl: Nat, +bl: Nat, f: R.Edit, +i: Nat, next: Unit -> R.Land) -> R.Land:
  match ok:
    case True{}:
      step.base(cb, la, ha, wl, bl, f, next)
    case False{}:
      R.Fails{R.Moved{i}}

# S4: one context's verdict from the copies in the head (ch) and the base
# (cb) of a window of wl lines anchored by la and ha, in a head of hl
# lines and a base of bl lines
def step(ch: List<&2, Nat>, cb: List<&2, Nat>, +la: Bool, +ha: Bool, +wl: Nat, +hl: Nat, +bl: Nat, +off: Nat, +len: Nat, ls: List<&2, Nat>, +i: Nat, next: Unit -> R.Land) -> R.Land:
  match ch:
    case Nil{}:
      R.Fails{R.Moved{i}}
    case Con{+j, more}:
      match more:
        case Nil{}:
          step.one(sits(la, ha, j, wl, hl), cb, la, ha, wl, bl, R.Edit{Nat.add(j, off), Nat.add(Nat.add(j, off), len), ls}, i, next)
        case Con{y, rest}:
          next(Unit{})

def step.win(w: R.Win, +b: List<&2, Nat>, +h: List<&2, Nat>, ls: List<&2, Nat>, +i: Nat, next: Unit -> R.Land) -> R.Land:
  match w:
    case R.Win{+la, +lw, +ha, off, len}:
      step(copies(h, lw), copies(b, lw), la, ha, List.length(&2, Nat, lw), List.length(&2, Nat, h), List.length(&2, Nat, b), off, len, ls, i, next)

# the edit [s, t) with lines ls carried onto h from context k, fuel
# contexts left
def land.go(fuel: Nat, +b: List<&2, Nat>, +h: List<&2, Nat>, +s: Nat, +t: Nat, +ls: List<&2, Nat>, +k: Nat, +i: Nat) -> R.Land:
  match fuel:
    case 0n:
      R.Fails{R.Ambiguous{i}}
    case 1n+p:
      step.win(window(b, s, t, k), b, h, ls, i, u => land.go(p, b, h, s, t, ls, 1n+k, i))

def first.of(ins: Bool) -> Nat:
  match ins:
    case True{}:
      1n
    case False{}:
      0n

# the first context of [s, t): 1 for an insertion, else 0
def first(+s: Nat, +t: Nat) -> Nat:
  first.of(Nat.is_eq(s, t))

def land(+b: List<&2, Nat>, +h: List<&2, Nat>, e: R.Edit, +i: Nat) -> R.Land:
  match e:
    case R.Edit{+s, +t, ls}:
      land.go(Nat.sub(1n+ctx(), first(s, t)), b, h, s, t, ls, first(s, t), i)

# S5: all of them
# ---------------

def land_all.of(l: R.Land, r: R.Outcome) -> R.Outcome:
  match l:
    case R.Lands{f}:
      match r:
        case R.Rebased{fs}:
          R.Rebased{f <> fs}
        case R.Conflict{w}:
          R.Conflict{w}
    case R.Fails{w}:
      R.Conflict{w}

def land_all(es: List<&2, R.Edit>, +b: List<&2, Nat>, +h: List<&2, Nat>, +i: Nat) -> R.Outcome:
  match es:
    case Nil{}:
      R.Rebased{Nil{}}
    case Con{e, rest}:
      land_all.of(land(b, h, e, i), land_all(rest, b, h, 1n+i))

def crossed.of(c: Maybe<&2, Nat>, fs: List<&2, R.Edit>) -> R.Outcome:
  match c:
    case None{}:
      R.Rebased{fs}
    case Some{i}:
      R.Conflict{R.Crossed{i}}

def crossed(o: R.Outcome, +m: Nat) -> R.Outcome:
  match o:
    case R.Rebased{+fs}:
      crossed.of(bad(fs, m), fs)
    case R.Conflict{w}:
      R.Conflict{w}

def rebase.of(c: Maybe<&2, Nat>, eq: Bool, +b: List<&2, Nat>, +h: List<&2, Nat>, +es: List<&2, R.Edit>) -> R.Outcome:
  match c:
    case Some{i}:
      R.Conflict{R.Invalid{i}}
    case None{}:
      match eq:
        case True{}:
          R.Rebased{es}
        case False{}:
          crossed(land_all(es, b, h, 0n), List.length(&2, Nat, h))

# the edits es against base b carried onto head h, or why not
def rebase(+b: List<&2, Nat>, +h: List<&2, Nat>, +es: List<&2, R.Edit>) -> R.Outcome:
  rebase.of(bad(es, List.length(&2, Nat, b)), same(b, h), b, h, es)

# Terms of the laws
# -----------------

# the places h holds the window an edit is first looked for by
def held(+b: List<&2, Nat>, +h: List<&2, Nat>, e: R.Edit) -> List<&2, Nat>:
  match e:
    case R.Edit{+s, +t, ls}:
      copies(h, lines(window(b, s, t, first(s, t))))

def many.go(fuel: Nat, +b: List<&2, Nat>, +h: List<&2, Nat>, +s: Nat, +t: Nat, +k: Nat) -> Bool:
  match fuel:
    case 0n:
      True{}
    case 1n+p:
      Bool.and(two(copies(h, lines(window(b, s, t, k)))), many.go(p, b, h, s, t, 1n+k))

# h holds two copies or more of every window of e the contexts allow
def many(+b: List<&2, Nat>, +h: List<&2, Nat>, e: R.Edit) -> Bool:
  match e:
    case R.Edit{+s, +t, ls}:
      many.go(Nat.sub(1n+ctx(), first(s, t)), b, h, s, t, first(s, t))

def edit_lines(e: R.Edit) -> List<&2, Nat>:
  match e:
    case R.Edit{s, t, ls}:
      ls

def pairs(+b: List<&2, Nat>, +h: List<&2, Nat>, es: List<&2, R.Edit>, fs: List<&2, R.Edit>) -> Bool:
  match es fs:
    case Nil{} Nil{}:
      True{}
    case Nil{} Con{f, ft}:
      False{}
    case Con{e, et} Nil{}:
      False{}
    case Con{+e, et} Con{+f, ft}:
      Bool.and(Bool.and(same(edit_lines(f), edit_lines(e)), same(region(h, f), region(b, e))), pairs(b, h, et, ft))

# fs replays es: one edit for each, sorted and apart within h, each putting
# the same lines in place of the head lines that are the base lines its
# edit replaced
def replays(+b: List<&2, Nat>, +h: List<&2, Nat>, es: List<&2, R.Edit>, +fs: List<&2, R.Edit>) -> Bool:
  Bool.and(valid(fs, List.length(&2, Nat, h)), pairs(b, h, es, fs))

def is_conflict(o: R.Outcome) -> Bool:
  match o:
    case R.Rebased{fs}:
      False{}
    case R.Conflict{w}:
      True{}
