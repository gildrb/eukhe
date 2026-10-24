# doc_search: the rules of what grep searched, of grep's pages and of the
# matches a page keeps (crates/eukhe-docs/src/grep/mod.rs). They run as the
# compiled core through bend/ffi_doc_search.bend: grep's walk is its
# stepper (one entry at a time, between the file reads), the page and the
# match limit its calls. The glob's pages (bend/doc_glob.bend) are the
# pages here.
#
# Grep: the walk meets a list of entries, in walk order. An entry is a
# file the search opens (with its number of matches in the part searched,
# and whether it is over the size limit) or an entry it skips (a binary
# file, a file that does not open, an excluded directory, a symlink, a
# walk error). The search keeps at most P matches of a file and at most
# REM matches in all; when REM gets to 0, it opens no more files. Each
# entry ends in exactly one class; a file with more matches than it kept
# is cut. The matching files are paged: K files after the first S. A file
# of a line-ranged root fetches enough matches to reach the last line its
# ranges select.
#
# Pages: a page of a list is the K items after the first S. When an item
# follows the page, the continuation is S + K.
#
# The match limit: at most L matches of the page, taken one per file per
# round, in file order.

import Base

# Pages
# -----

# the K items after the first S
def page(ps: List<&2, Nat>, s: Nat, k: Nat) -> List<&2, Nat>:
  List.take(&2, Nat, List.drop(&2, Nat, ps, s), k)

def next.put(after: List<&2, Nat>, c: Nat) -> Maybe<&2, Nat>:
  match after:
    case Nil{}:
      None{}
    case h <> t:
      Some{c}

# the continuation of the page: S + K when an item follows the page
def next(ps: List<&2, Nat>, +s: Nat, k: Nat) -> Maybe<&2, Nat>:
  match k:
    case 0n:
      None{}
    case 1n+j:
      +c = Nat.add(s, 1n+j)
      next.put(List.drop(&2, Nat, ps, c), c)

# the numbers 0 to t - 1, from i on: the matching files of a search, in
# walk order
def upto.go(t: Nat, +i: Nat) -> List<&2, Nat>:
  match t:
    case 0n:
      Nil{}
    case 1n+u:
      i <> upto.go(u, 1n+i)

def upto(t: Nat) -> List<&2, Nat>:
  upto.go(t, 0n)

# the skip is past the end of a list that is not empty
def past(ps: List<&2, Nat>, s: Nat) -> Bool:
  match ps:
    case Nil{}:
      False{}
    case h <> t:
      List.is_empty(&2, Nat, List.drop(&2, Nat, h <> t, s))

# grep's continuation: a scope of one file (multi False) has none
def grep.next(multi: Bool, ps: List<&2, Nat>, +s: Nat, k: Nat) -> Maybe<&2, Nat>:
  match multi:
    case True{}:
      next(ps, s, k)
    case False{}:
      None{}

# grep's skip past the end: a scope of one file has no skip
def grep.past(multi: Bool, ps: List<&2, Nat>, s: Nat) -> Bool:
  match multi:
    case True{}:
      past(ps, s)
    case False{}:
      False{}

# Grep's scope
# ------------

# matches kept of a file when the scope can hold several files
def multi_cap() -> Nat:
  20n

# matches kept when the scope is one file
def single_cap() -> Nat:
  200n

# files on a page when no match limit is asked
def files_page() -> Nat:
  20n

# the scope of a search: several files (multi), the matches a file keeps
# (P), the matching files skipped (S) and shown (K) on a page
type Scope is Data:
  Scope{multi: Bool, p: Nat, s: Nat, k: Nat}

def scope.of(multi: Bool, skip: Nat, k: Nat) -> Scope:
  match multi:
    case True{}:
      Scope{True{}, multi_cap(), skip, k}
    case False{}:
      Scope{False{}, single_cap(), 0n, k}

# a page of the match limit and one more file, else files_page()
def scope.k(lim: Maybe<&2, Nat>) -> Nat:
  match lim:
    case None{}:
      files_page()
    case Some{l}:
      1n+l

# the scope of a path of `roots` roots, `dirs` of them directories, with
# the skip asked and the match limit asked (None: no limit): several files
# when there is more than one root or a directory root; one file keeps no
# skip
def scope(roots: Nat, dirs: Nat, skip: Nat, lim: Maybe<&2, Nat>) -> Scope:
  scope.of(Bool.or(Nat.is_lt(1n, roots), Nat.is_lt(0n, dirs)), skip, scope.k(lim))

# Grep
# ----

type Reason is Data:
  Binary{}       # a NUL byte is in it
  Unreadable{}   # it does not open
  Excluded{}     # node_modules or .git: the walk does not go in
  Link{}         # a symlink: the walk does not follow it
  Broken{}       # the walk could not read a directory

type Form is Data:
  Opened{hits: Nat, big: Bool}   # a file it opens: the matches in the part it searches; over the size limit
  Skip{why: Reason}

type Ent is Data:
  Ent{id: Nat, form: Form}

type Class is Data:
  NoMatch{}
  Shown{}
  PagedOut{}
  Unsearched{}
  Skipped{why: Reason}

# what became of one entry: its class, whether matches were cut, and
# whether only a part of it was searched
type Out is Data:
  Out{id: Nat, cls: Class, cut: Bool, partial: Bool}

# the walk finds these reasons only when it opens the file
def Reason.opened(r: Reason) -> Bool:
  match r:
    case Binary{}:
      True{}
    case Unreadable{}:
      True{}
    case Excluded{}:
      False{}
    case Link{}:
      False{}
    case Broken{}:
      False{}

# whether the matching file number n is on the page
def onpage(+n: Nat, +s: Nat, k: Nat) -> Bool:
  Bool.and(Nat.is_le(s, n), Nat.is_lt(n, Nat.add(s, k)))

def page.cls(on: Bool) -> Class:
  match on:
    case True{}:
      Shown{}
    case False{}:
      PagedOut{}

def hit.cls(h: Nat, +s: Nat, +k: Nat, +n: Nat) -> Class:
  match h:
    case 0n:
      NoMatch{}
    case 1n+g:
      page.cls(onpage(n, s, k))

def stop.cls(+why: Reason, opened: Bool) -> Class:
  match opened:
    case True{}:
      Unsearched{}
    case False{}:
      Skipped{why}

def skip.cls(+why: Reason, rem: Nat) -> Class:
  match rem:
    case 0n:
      stop.cls(why, Reason.opened(why))
    case 1n+r:
      Skipped{why}

# the class of an entry, with REM matches left and n matching files
# before it
def out(e: Ent, +p: Nat, +s: Nat, +k: Nat, +rem: Nat, +n: Nat) -> Out:
  match e:
    case Ent{i, f}:
      match f:
        case Opened{+h, big}:
          match rem:
            case 0n:
              Out{i, Unsearched{}, False{}, False{}}
            case 1n+r:
              Out{i, hit.cls(h, s, k, n), Nat.is_lt(Nat.min(p, 1n+r), h), big}
        case Skip{why}:
          Out{i, skip.cls(why, rem), False{}, False{}}

# the matches left after the entry
def left(e: Ent, +p: Nat, +rem: Nat) -> Nat:
  match e:
    case Ent{i, f}:
      match f:
        case Opened{+h, big}:
          Nat.sub(rem, Nat.min(h, Nat.min(p, rem)))
        case Skip{why}:
          rem

def seen.put(h: Nat, +n: Nat) -> Nat:
  match h:
    case 0n:
      n
    case 1n+g:
      1n+n

# the matching files after the entry
def seen(e: Ent, rem: Nat, +n: Nat) -> Nat:
  match e:
    case Ent{i, f}:
      match f:
        case Opened{h, big}:
          match rem:
            case 0n:
              n
            case 1n+r:
              seen.put(h, n)
        case Skip{why}:
          n

# a search: P matches a file at most, page K files after the first S,
# REM matches in all, n matching files before
def run(es: List<&2, Ent>, +p: Nat, +s: Nat, +k: Nat, +rem: Nat, +n: Nat) -> List<&2, Out>:
  match es:
    case Nil{}:
      Nil{}
    case +e <> rest:
      out(e, p, s, k, rem, n) <> run(rest, p, s, k, left(e, p, rem), seen(e, rem, n))

# the matches an entry keeps, with REM left: at most P of a file, at most
# REM in all (left(e, p, rem) is rem less these)
def kept(e: Ent, +p: Nat, +rem: Nat) -> Nat:
  match e:
    case Ent{i, f}:
      match f:
        case Opened{h, big}:
          Nat.min(h, Nat.min(p, rem))
        case Skip{why}:
          0n

# the matches each entry keeps, in walk order
def keeps(es: List<&2, Ent>, +p: Nat, +rem: Nat) -> List<&2, Nat>:
  match es:
    case Nil{}:
      Nil{}
    case +e <> rest:
      kept(e, p, rem) <> keeps(rest, p, left(e, p, rem))

# Line ranges
# -----------

# a range of lines a root selects: from its start, to its end or open
type Range is Data:
  Range{start: Nat, stop: Maybe<&2, Nat>}

# the last line a range needs: its end, or `base` lines from its start
def reach(r: Range, +base: Nat) -> Nat:
  match r:
    case Range{a, z}:
      match z:
        case None{}:
          Nat.add(Nat.sub(a, 1n), base)
        case Some{e}:
          e

# the last line any of the ranges needs; 0 for none
def reach.top(rs: List<&2, Range>, +base: Nat) -> Nat:
  match rs:
    case Nil{}:
      0n
    case r <> t:
      Nat.max(reach(r, base), reach.top(t, base))

# the matches the search fetches from a file, P a file at most and REM in
# all left: one more than the file can keep (so a cut shows); a file of
# line-ranged roots: enough to reach the last line they need (a file of
# MAXB bytes has no more lines than that), and never fewer than P + 1
def fetch(rs: List<&2, Range>, +p: Nat, +rem: Nat, +maxb: Nat) -> Nat:
  match rs:
    case Nil{}:
      1n+Nat.min(p, rem)
    case r <> t:
      Nat.max(1n+p, Nat.min(reach.top(r <> t, 1n+p), 1n+maxb))

# Accounts and notices
# --------------------

# how many entries of each class, and how many searched only in part
type Count is Data:
  Count{no_match: Nat, shown: Nat, paged_out: Nat, not_searched: Nat, binary: Nat, unreadable: Nat, excluded: Nat, symlink: Nat, walk_error: Nat, partial: Nat}

def Count.zero() -> Count:
  Count{0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n}

def sum(xs: List<&2, Nat>) -> Nat:
  match xs:
    case Nil{}:
      0n
    case x <> rest:
      Nat.add(x, sum(rest))

# the entries the classes hold together
def Count.total(c: Count) -> Nat:
  match c:
    case Count{a, b, d, e, f, g, h, i, j, pa}:
      sum([a, b, d, e, f, g, h, i, j])

def Count.part(pa: Bool, c: Count) -> Count:
  match pa:
    case False{}:
      c
    case True{}:
      match c:
        case Count{a, b, d, e, f, g, h, i, j, q}:
          Count{a, b, d, e, f, g, h, i, j, 1n+q}

def Count.add(c: Count, x: Class) -> Count:
  match c:
    case Count{a, b, d, e, f, g, h, i, j, pa}:
      match x:
        case NoMatch{}:
          Count{1n+a, b, d, e, f, g, h, i, j, pa}
        case Shown{}:
          Count{a, 1n+b, d, e, f, g, h, i, j, pa}
        case PagedOut{}:
          Count{a, b, 1n+d, e, f, g, h, i, j, pa}
        case Unsearched{}:
          Count{a, b, d, 1n+e, f, g, h, i, j, pa}
        case Skipped{w}:
          match w:
            case Binary{}:
              Count{a, b, d, e, 1n+f, g, h, i, j, pa}
            case Unreadable{}:
              Count{a, b, d, e, f, 1n+g, h, i, j, pa}
            case Excluded{}:
              Count{a, b, d, e, f, g, 1n+h, i, j, pa}
            case Link{}:
              Count{a, b, d, e, f, g, h, 1n+i, j, pa}
            case Broken{}:
              Count{a, b, d, e, f, g, h, i, 1n+j, pa}

# the count of a result
def account(os: List<&2, Out>) -> Count:
  match os:
    case Nil{}:
      Count.zero()
    case o <> rest:
      match o:
        case Out{i, c, t, pa}:
          Count.part(pa, Count.add(account(rest), c))

# a notice of a class of entries the search left out or searched in part
type Note is Data:
  NSkip{why: Reason}
  NPartial{}
  NUnsearched{}

def Note.count(c: Count, n: Note) -> Nat:
  match c:
    case Count{a, b, d, e, f, g, h, i, j, pa}:
      match n:
        case NSkip{w}:
          match w:
            case Binary{}:
              f
            case Unreadable{}:
              g
            case Excluded{}:
              h
            case Link{}:
              i
            case Broken{}:
              j
        case NPartial{}:
          pa
        case NUnsearched{}:
          e

def Reason.same(a: Reason, b: Reason) -> Bool:
  match a b:
    case Binary{} Binary{}:
      True{}
    case Unreadable{} Unreadable{}:
      True{}
    case Excluded{} Excluded{}:
      True{}
    case Link{} Link{}:
      True{}
    case Broken{} Broken{}:
      True{}
    case x y:
      False{}

def Note.cls(n: Note, c: Class, pa: Bool) -> Bool:
  match n:
    case NSkip{w}:
      match c:
        case Skipped{v}:
          Reason.same(w, v)
        case x:
          False{}
    case NPartial{}:
      pa
    case NUnsearched{}:
      match c:
        case Unsearched{}:
          True{}
        case x:
          False{}

# whether the entry is one the notice reports
def Note.of(o: Out, n: Note) -> Bool:
  match o:
    case Out{i, c, t, pa}:
      Note.cls(n, c, pa)

# whether the result has the notice: an entry it reports is there
def noted(+n: Note, os: List<&2, Out>) -> Bool:
  match os:
    case Nil{}:
      False{}
    case +o <> rest:
      Bool.or(Note.of(o, n), noted(n, rest))

def cut.put(i: Nat, c: Class, t: Bool, rest: List<&2, Nat>) -> List<&2, Nat>:
  match c:
    case Shown{}:
      match t:
        case True{}:
          i <> rest
        case False{}:
          rest
    case x:
      rest

# the shown files whose matches were cut: one notice each
def cuts(os: List<&2, Out>) -> List<&2, Nat>:
  match os:
    case Nil{}:
      Nil{}
    case o <> rest:
      match o:
        case Out{i, c, t, pa}:
          cut.put(i, c, t, cuts(rest))

def mem(+n: Nat, xs: List<&2, Nat>) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case x <> rest:
      Bool.or(Nat.is_eq(x, n), mem(n, rest))

# no item twice
def nodup(xs: List<&2, Nat>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case +x <> +rest:
      Bool.and(Bool.not(mem(x, rest)), nodup(rest))

# The match limit
# ---------------

# whether a file gives a match: it has one in this round and the budget
# is not spent
def rr.bit(has: Bool, b: Nat) -> Nat:
  match has:
    case True{}:
      match b:
        case 0n:
          0n
        case 1n+c:
          1n
    case False{}:
      0n

# round r: each file with more than r matches gives one, in file order,
# while the budget b lasts
def rr.give(cs: List<&2, Nat>, +r: Nat, +b: Nat) -> List<&2, Nat>:
  match cs:
    case Nil{}:
      Nil{}
    case c <> t:
      +g = rr.bit(Nat.is_lt(r, c), b)
      g <> rr.give(t, r, Nat.sub(b, g))

def rr.zeros(cs: List<&2, Nat>) -> List<&2, Nat>:
  match cs:
    case Nil{}:
      Nil{}
    case c <> t:
      0n <> rr.zeros(t)

# two lists of counts, file by file
def rr.add(xs: List<&2, Nat>, ys: List<&2, Nat>) -> List<&2, Nat>:
  match xs:
    case Nil{}:
      Nil{}
    case x <> xt:
      match ys:
        case Nil{}:
          Nil{}
        case y <> yt:
          Nat.add(x, y) <> rr.add(xt, yt)

# the most matches of a file
def rr.top(cs: List<&2, Nat>) -> Nat:
  match cs:
    case Nil{}:
      0n
    case c <> t:
      Nat.max(c, rr.top(t))

# rounds r, r + 1, ... (f of them) with budget b
def rr.go(f: Nat, +cs: List<&2, Nat>, +r: Nat, +b: Nat) -> List<&2, Nat>:
  match f:
    case 0n:
      rr.zeros(cs)
    case 1n+g:
      match b:
        case 0n:
          rr.zeros(cs)
        case 1n+c:
          +gs = rr.give(cs, r, 1n+c)
          rr.add(gs, rr.go(g, cs, 1n+r, Nat.sub(1n+c, sum(gs))))

# the matches each file of the page keeps under a limit of L: one per
# file per round, in file order, L in all (a round past the most matches
# of a file gives none)
def rr(+cs: List<&2, Nat>, l: Nat) -> List<&2, Nat>:
  rr.go(rr.top(cs), cs, 0n, l)

# whether the limit cuts matches: the page has more than L
def rr.cut(cs: List<&2, Nat>, l: Nat) -> Bool:
  Nat.is_lt(l, sum(cs))
