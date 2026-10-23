# doc_search: the models of what grep searched and of the pages of grep
# and glob (crates/eukhe-docs/src/grep/mod.rs, crates/eukhe-docs/src/glob.rs).
#
# Grep: the walk meets a list of entries, in walk order. An entry is a
# file the search opens (with its number of matches in the part searched,
# and whether it is over the size limit) or an entry it skips (a binary
# file, a file that does not open, an excluded directory, a symlink, a
# walk error). The search keeps at most P matches of a file and at most
# REM matches in all; when REM gets to 0, it opens no more files. Each
# entry ends in exactly one class; a file with more matches than it kept
# is cut. The matching files are paged: K files after the first S.
#
# Pages: a page of a list is the K items after the first S. When an item
# follows the page, the continuation is S + K.
#
# Glob: the paths, newest first and then by name, are paged.
#
# The bridges (bridge/bridge_doc_search.bend,
# crates/eukhe-docs/src/grep/bridge_accounts.rs and
# crates/eukhe-docs/src/glob/bridge.rs) run the real code on generated
# trees and compare.

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

# the matching files, in walk order
def hits(os: List<&2, Out>) -> List<&2, Nat>:
  match os:
    case Nil{}:
      Nil{}
    case o <> rest:
      match o:
        case Out{i, c, t, pa}:
          match c:
            case NoMatch{}:
              hits(rest)
            case Shown{}:
              i <> hits(rest)
            case PagedOut{}:
              i <> hits(rest)
            case Unsearched{}:
              hits(rest)
            case Skipped{w}:
              hits(rest)

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

# Glob
# ----

# a path the glob matches: its name and when it changed
type Path is Data:
  Path{id: Nat, mtime: Nat}

# a ranks before b: newer, or as new and a smaller name
def ranks(a: Path, b: Path) -> Bool:
  match a b:
    case Path{+i, +m} Path{+j, +n}:
      Bool.or(Nat.is_gt(m, n), Bool.and(Nat.is_eq(m, n), Nat.is_le(i, j)))

def ids(ps: List<&2, Path>) -> List<&2, Nat>:
  match ps:
    case Nil{}:
      Nil{}
    case p <> rest:
      match p:
        case Path{i, m}:
          i <> ids(rest)

# the names, newest first
def ranked(ps: List<&2, Path>) -> List<&2, Nat>:
  ids(List.sort(~Path, ~ranks, ps))

# the page size of a limit: 200 at most
def glob.size(k: Nat) -> Nat:
  Nat.min(k, 200n)
