# rebase: the three-way rebase of a stale edit (Rust: eukhe-bend
# rules/rebase.rs; asked by eukhe-docs rebase.rs for the hashline
# patcher's `rebase_stale`). The session wrote edits against the base (the
# snapshot its tag names); the file is now the head. Each edit is carried
# onto the head, or the whole rebase is refused with the exact reason:
# nothing lands in part.
#
# Lines are ids: Rust interns each distinct line text to one Nat, so two
# lines are equal exactly when their ids are. An edit replaces the base
# lines [start, end) with its lines.
#
# The rule, in order:
# 1. the edits are sorted and apart: each within the base (start <= end <=
#    the base's length), starting after the one before (start > the last
#    start) and not inside it (start >= the last end); else Invalid{i},
#    i the first edit that breaks it;
# 2. a head that is the base takes the edits unchanged;
# 3. each edit is found in the head through its window: its own lines with
#    k lines of base context on each side (cut at the file's ends; a side
#    that reaches the first or the last line is anchored there, as if the
#    file's start and end were lines too). k starts at 0 (at 1 for an
#    insertion, whose own lines are none) and grows to ctx() = 8. At each k:
#    the head holds no copy of the window -> Moved{i} (the head changed
#    the edit's lines or the context it was found by); the base and the
#    head each hold exactly one copy -> the edit lands at the head's copy,
#    its lines kept; otherwise (two copies or more in either) k grows, and
#    past ctx() the edit is Ambiguous{i}: an alignment with more than one
#    match is refused, never guessed;
# 4. the landed edits must again be sorted and apart in the head; else
#    Crossed{i}, i the first that is not.
# TooLarge{} is the entry's (bend/ffi_rebase.bend) answer past its work
# bound; the rule never answers it.
#
# Cost: rule 3 scans the base and the head once per edit and context, a
# scan stopping at the second copy; bend/ffi_rebase.bend bounds the edits
# times the lines.
# Pure: no IO, no @unsafe.

import Base

# An edit: the base lines [start, end) become lines
type Edit is Data:
  Edit{start: Nat, end: Nat, lines: List<&2, Nat>}

# Why a rebase is refused (`at`: the index of the edit, from 0)
type Why is Data:
  Invalid{at: Nat}
  Moved{at: Nat}
  Ambiguous{at: Nat}
  Crossed{at: Nat}
  TooLarge{}

# The answer: the edits against the head, or the refusal
type Outcome is Data:
  Rebased{edits: List<&2, Edit>}
  Conflict{why: Why}

# One edit carried onto the head, or why not
type Land is Data:
  Lands{edit: Edit}
  Fails{why: Why}

# Where a window occurs: nowhere, at one place, at two places or more
type Hits is Data:
  HNone{}
  HOne{at: Nat}
  HMany{}

# A window of an edit: anchored at the file's start (la), its lines,
# anchored at the file's end (ha), where the edit's own lines start in it
# (off) and how many they are (len)
type Win is Data:
  Win{la: Bool, lines: List<&2, Nat>, ha: Bool, off: Nat, len: Nat}

# the most lines of context on each side of an edit
def ctx() -> Nat:
  8n

# yes() when c, else no(); only the branch taken runs
def when(-R: Type, c: Bool, yes: Unit -> R, no: Unit -> R) -> R:
  match c:
    case True{}:
      yes(Unit{})
    case False{}:
      no(Unit{})

# Rule 1: sorted and apart
# ------------------------

def floor.of(ins: Bool, +t: Nat) -> Nat:
  match ins:
    case True{}:
      1n+t
    case False{}:
      t

# the least start the edit after one of (s, t) may have: past an
# insertion's start, at or past a replacement's end
def floor(+s: Nat, +t: Nat) -> Nat:
  floor.of(Nat.is_eq(s, t), t)

def check.at(ok: Bool, +i: Nat, rest: Maybe<&2, Nat>) -> Maybe<&2, Nat>:
  match ok:
    case True{}:
      rest
    case False{}:
      Some{i}

# the first edit of es (numbered from i) that is not within n lines, at
# or past the floor f
def check.go(es: List<&2, Edit>, +n: Nat, +f: Nat, +i: Nat) -> Maybe<&2, Nat>:
  match es:
    case Nil{}:
      None{}
    case Con{e, rest}:
      match e:
        case Edit{+s, +t, ls}:
          check.at(Bool.and(Nat.is_le(f, s), Bool.and(Nat.is_le(s, t), Nat.is_le(t, n))), i, check.go(rest, n, floor(s, t), 1n+i))

# the first edit of es that breaks rule 1 against n lines
def check(es: List<&2, Edit>, +n: Nat) -> Maybe<&2, Nat>:
  check.go(es, n, 0n, 0n)

# Rule 2: the same lines
# ----------------------

# a and b hold the same lines
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

# Rule 3: windows
# ---------------

# the lines w start y; stops at the first difference
def fits(w: List<&2, Nat>, y: List<&2, Nat>) -> Bool:
  match w y:
    case Nil{} Nil{}:
      True{}
    case Nil{} Con{c, ct}:
      True{}
    case Con{a, wt} Nil{}:
      False{}
    case Con{a, wt} Con{c, yt}:
      when(Bool, Nat.is_eq(a, c), u => fits(wt, yt), u => False{})

# a second copy after the one at acc, else go on
def seen(acc: Maybe<&2, Nat>, go: Unit -> Hits) -> Hits:
  match acc:
    case None{}:
      go(Unit{})
    case Some{a}:
      HMany{}

def found(acc: Maybe<&2, Nat>) -> Hits:
  match acc:
    case None{}:
      HNone{}
    case Some{a}:
      HOne{a}

# the copies of w in x at j and after (x is the line j on), after the copy
# at acc; stops at the second copy
def scan(x: List<&2, Nat>, +w: List<&2, Nat>, +j: Nat, +acc: Maybe<&2, Nat>) -> Hits:
  match x:
    case Nil{}:
      when(Hits, fits(w, Nil{}), u => seen(acc, v => HOne{j}), u => found(acc))
    case Con{+c, +t}:
      when(Hits, fits(w, Con{c, t}), u => seen(acc, v => scan(t, w, 1n+j, Some{j})), u => scan(t, w, 1n+j, acc))

# a copy of wl lines at j of xl lines sits at the start when anchored
# there (la), at the end when anchored there (ha)
def placed(la: Bool, ha: Bool, +j: Nat, +wl: Nat, +xl: Nat) -> Bool:
  Bool.and(Bool.or(Bool.not(la), Nat.is_eq(j, 0n)), Bool.or(Bool.not(ha), Nat.is_eq(Nat.add(j, wl), xl)))

def keep(ok: Bool, +j: Nat) -> Hits:
  match ok:
    case True{}:
      HOne{j}
    case False{}:
      HNone{}

def anchor(r: Hits, la: Bool, ha: Bool, +wl: Nat, +xl: Nat) -> Hits:
  match r:
    case HNone{}:
      HNone{}
    case HOne{+j}:
      keep(placed(la, ha, j, wl, xl), j)
    case HMany{}:
      HMany{}

# the copies of a window's lines w in x: the file's start and end never
# stand in for lines, so a window is found once only when its lines occur
# once; that copy must then sit where the anchors (la, ha) put it
def hits(+x: List<&2, Nat>, la: Bool, +w: List<&2, Nat>, ha: Bool) -> Hits:
  anchor(scan(x, w, 0n, None{}), la, ha, List.length(&2, Nat, w), List.length(&2, Nat, x))

# the window of the edit [s, t) of b with k lines of context on each side
def window(+b: List<&2, Nat>, +s: Nat, +t: Nat, +k: Nat) -> Win:
  +lo = Nat.sub(s, k)
  +lc = List.take(&2, Nat, List.drop(&2, Nat, b, lo), Nat.sub(s, lo))
  +rg = List.take(&2, Nat, List.drop(&2, Nat, b, s), Nat.sub(t, s))
  +rc = List.take(&2, Nat, List.drop(&2, Nat, b, t), k)
  Win{Nat.is_lt(s, k), List.append(&2, Nat, lc, List.append(&2, Nat, rg, rc)), Nat.is_lt(List.length(&2, Nat, b), Nat.add(t, k)), List.length(&2, Nat, lc), List.length(&2, Nat, rg)}

# one context's verdict from the copies in the head (ch) and the base (cb)
def land.at(ch: Hits, cb: Hits, +off: Nat, +len: Nat, ls: List<&2, Nat>, +i: Nat, next: Unit -> Land) -> Land:
  match ch:
    case HNone{}:
      Fails{Moved{i}}
    case HOne{+j}:
      match cb:
        case HOne{x}:
          Lands{Edit{Nat.add(j, off), Nat.add(Nat.add(j, off), len), ls}}
        case HNone{}:
          next(Unit{})
        case HMany{}:
          next(Unit{})
    case HMany{}:
      next(Unit{})

def land.win(w: Win, +b: List<&2, Nat>, +h: List<&2, Nat>, ls: List<&2, Nat>, +i: Nat, next: Unit -> Land) -> Land:
  match w:
    case Win{+la, +lw, +ha, off, len}:
      land.at(hits(h, la, lw, ha), hits(b, la, lw, ha), off, len, ls, i, next)

# the edit [s, t) with lines ls carried onto h from context k on, with
# fuel contexts left
def land.go(fuel: Nat, +b: List<&2, Nat>, +h: List<&2, Nat>, +s: Nat, +t: Nat, +ls: List<&2, Nat>, +k: Nat, +i: Nat) -> Land:
  match fuel:
    case 0n:
      Fails{Ambiguous{i}}
    case 1n+p:
      land.win(window(b, s, t, k), b, h, ls, i, u => land.go(p, b, h, s, t, ls, 1n+k, i))

def first.of(ins: Bool) -> Nat:
  match ins:
    case True{}:
      1n
    case False{}:
      0n

# the first context: 0, or 1 for an insertion
def first(+s: Nat, +t: Nat) -> Nat:
  first.of(Nat.is_eq(s, t))

# the edit e (the i-th) carried from b onto h
def land(+b: List<&2, Nat>, +h: List<&2, Nat>, e: Edit, +i: Nat) -> Land:
  match e:
    case Edit{+s, +t, ls}:
      land.go(Nat.sub(1n+ctx(), first(s, t)), b, h, s, t, ls, first(s, t), i)

def land_all.at(l: Land, r: Outcome) -> Outcome:
  match l:
    case Lands{f}:
      match r:
        case Rebased{fs}:
          Rebased{f <> fs}
        case Conflict{w}:
          Conflict{w}
    case Fails{w}:
      Conflict{w}

# every edit of es (numbered from i) carried from b onto h; the first
# that fails refuses them all
def land_all(es: List<&2, Edit>, +b: List<&2, Nat>, +h: List<&2, Nat>, +i: Nat) -> Outcome:
  match es:
    case Nil{}:
      Rebased{Nil{}}
    case Con{e, rest}:
      land_all.at(land(b, h, e, i), land_all(rest, b, h, 1n+i))

# Rule 4 and the whole rebase
# ---------------------------

def crossed.at(c: Maybe<&2, Nat>, fs: List<&2, Edit>) -> Outcome:
  match c:
    case None{}:
      Rebased{fs}
    case Some{i}:
      Conflict{Crossed{i}}

def crossed(o: Outcome, +m: Nat) -> Outcome:
  match o:
    case Rebased{+fs}:
      crossed.at(check(fs, m), fs)
    case Conflict{w}:
      Conflict{w}

def rebase.at(c: Maybe<&2, Nat>, eq: Bool, +b: List<&2, Nat>, +h: List<&2, Nat>, +es: List<&2, Edit>) -> Outcome:
  match c:
    case Some{i}:
      Conflict{Invalid{i}}
    case None{}:
      match eq:
        case True{}:
          Rebased{es}
        case False{}:
          crossed(land_all(es, b, h, 0n), List.length(&2, Nat, h))

# the edits es against base b carried onto head h, or why not
def rebase(+b: List<&2, Nat>, +h: List<&2, Nat>, +es: List<&2, Edit>) -> Outcome:
  rebase.at(check(es, List.length(&2, Nat, b)), same(b, h), b, h, es)
