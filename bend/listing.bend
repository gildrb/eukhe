# listing: the real rule of how the sessions directory is listed
# (crates/eukhe-core/src/durable/discovery.rs `list_sessions`): which
# entry is a session candidate, under which id (`scan`), and, once the
# Rust read the cwds and times of the candidates, the listed rows in
# order, newest first (`rows`). The model it refines is the Listing
# section of bend/staging.bend; the compiled core runs it through
# bend/ffi_staging.bend.

import Base
import ./staging.bend as Sg

# what an entry of the sessions directory is to the listing
type Pick is Data:
  PSkip{}               # no session
  PStore{id: String}    # a storage, listed under its name
  PLegacy{id: String}   # a legacy file not imported, listed under its stem

# s is a hidden name
def hidden(s: String) -> Bool:
  match s:
    case SNil{}:
      False{}
    case SCon{c, t}:
      Sg.ch.is(c, 46)

def pick.dir(main: Bool, hid: Bool, s: String) -> Pick:
  match main:
    case True{}:
      match hid:
        case True{}:
          PSkip{}
        case False{}:
          PStore{s}
    case False{}:
      PSkip{}

def pick.legacy(gone: Bool, s: String) -> Pick:
  match gone:
    case True{}:
      PSkip{}
    case False{}:
      PLegacy{s}

# a legacy file whose stem is empty, "." or "..", or the name of an entry,
# is no session of its own: its storage directory exists (or it has none)
def pick.stem(m: Maybe<&2, String>, all: List<&2, Sg.Seen>) -> Pick:
  match m:
    case None{}:
      PSkip{}
    case Some{+st}:
      pick.legacy(Bool.or(Bool.or(String.is_empty(st), Bool.or(Sg.same(st, "."), Sg.same(st, ".."))), Sg.has_name(st, all)), st)

def pick.utf(k: Sg.Form, +s: String, all: List<&2, Sg.Seen>) -> Pick:
  match k:
    case Sg.KDir{main}:
      pick.dir(main, hidden(s), s)
    case Sg.KFile{}:
      pick.stem(Sg.unsuffix(".jsonl", s), all)
    case Sg.KOther{}:
      PSkip{}

# what the entry e of the sessions directory listing all is to the listing
def pick(e: Sg.Seen, all: List<&2, Sg.Seen>) -> Pick:
  match e:
    case Sg.Seen{n, k}:
      match n:
        case Sg.Utf{s}:
          pick.utf(k, s, all)
        case Sg.Raw{}:
          PSkip{}

def scan.go(es: List<&2, Sg.Seen>, +all: List<&2, Sg.Seen>) -> List<&2, Pick>:
  match es:
    case Nil{}:
      Nil{}
    case e <> rest:
      pick(e, all) <> scan.go(rest, all)

# what each entry of the sessions directory listing is, in order
def scan(+es: List<&2, Sg.Seen>) -> List<&2, Pick>:
  scan.go(es, es)

# an entry of the sessions directory, with what the Rust read of it: its
# cwd (None: it does not read) and the modification times of its files
# (a storage: every file in it; a legacy file: the file); an entry the
# scan skips needs neither
type Obs is Data:
  Obs{seen: Sg.Seen, cwd: Maybe<&2, String>, times: List<&2, Sg.Time>}

# a listed session: the place of its entry in the request, what it is,
# and its recency
type Row is Data:
  Row{at: Nat, pick: Pick, time: Sg.Time}

def Pick.id(p: Pick) -> String:
  match p:
    case PSkip{}:
      ""
    case PStore{s}:
      s
    case PLegacy{s}:
      s

# a Nat list strictly before another, item by item (a prefix first)
def lex(a: List<&2, Nat>, b: List<&2, Nat>) -> Bool:
  match a b:
    case Nil{} Nil{}:
      False{}
    case Nil{} Con{y, v}:
      True{}
    case Con{x, u} Nil{}:
      False{}
    case Con{+x, u} Con{+y, v}:
      Bool.or(Nat.is_lt(x, y), Bool.and(Nat.is_eq(x, y), lex(u, v)))

def tkey(t: Sg.Time) -> List<&2, Nat>:
  match t:
    case Sg.Time{s, n}:
      [s, n]

def code(c: Char) -> Nat:
  match c:
    case Chr{x}:
      U32.to_nat(x)

# the char codes of s: text order is their order (Rust's str order)
def codes(s: String) -> List<&2, Nat>:
  match s:
    case SNil{}:
      Nil{}
    case SCon{c, t}:
      code(c) <> codes(t)

def later.pick(b: Bool, a: Sg.Time, c: Sg.Time) -> Sg.Time:
  match b:
    case True{}:
      c
    case False{}:
      a

# the later of a and b
def later(+a: Sg.Time, +b: Sg.Time) -> Sg.Time:
  later.pick(lex(tkey(a), tkey(b)), a, b)

# the newest of t and the times ts
def newest(ts: List<&2, Sg.Time>, t: Sg.Time) -> Sg.Time:
  match ts:
    case Nil{}:
      t
    case u <> rest:
      newest(rest, later(t, u))

def cwd_ok(m: Maybe<&2, String>) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{s}:
      Bool.not(String.is_empty(s))

def row.times(p: Pick, i: Nat, ts: List<&2, Sg.Time>) -> Maybe<&2, Row>:
  match ts:
    case Nil{}:
      None{}
    case t <> rest:
      Some{Row{i, p, newest(rest, t)}}

def row.cwd(ok: Bool, p: Pick, i: Nat, ts: List<&2, Sg.Time>) -> Maybe<&2, Row>:
  match ok:
    case True{}:
      row.times(p, i, ts)
    case False{}:
      None{}

def row.pick(p: Pick, i: Nat, ok: Bool, ts: List<&2, Sg.Time>) -> Maybe<&2, Row>:
  match p:
    case PSkip{}:
      None{}
    case PStore{s}:
      row.cwd(ok, PStore{s}, i, ts)
    case PLegacy{s}:
      row.cwd(ok, PLegacy{s}, i, ts)

# the row of the entry o at place i: a session candidate whose cwd reads
# (not empty) and that has a file
def row(o: Obs, all: List<&2, Sg.Seen>, i: Nat) -> Maybe<&2, Row>:
  match o:
    case Obs{e, c, ts}:
      row.pick(pick(e, all), i, cwd_ok(c), ts)

def row.put(m: Maybe<&2, Row>, rest: List<&2, Row>) -> List<&2, Row>:
  match m:
    case None{}:
      rest
    case Some{r}:
      r <> rest

def rows.go(os: List<&2, Obs>, +all: List<&2, Sg.Seen>, +i: Nat) -> List<&2, Row>:
  match os:
    case Nil{}:
      Nil{}
    case o <> rest:
      row.put(row(o, all, i), rows.go(rest, all, 1n+i))

def seens(os: List<&2, Obs>) -> List<&2, Sg.Seen>:
  match os:
    case Nil{}:
      Nil{}
    case o <> rest:
      match o:
        case Obs{e, c, ts}:
          e <> seens(rest)

def before.id(lt: Bool, gt: Bool, ia: Nat, ib: Nat) -> Bool:
  match lt:
    case True{}:
      True{}
    case False{}:
      match gt:
        case True{}:
          False{}
        case False{}:
          Nat.is_lt(ia, ib)

def before.go(newer: Bool, older: Bool, pa: Pick, pb: Pick, ia: Nat, ib: Nat) -> Bool:
  match newer:
    case True{}:
      True{}
    case False{}:
      match older:
        case True{}:
          False{}
        case False{}:
          +ka = codes(Pick.id(pa))
          +kb = codes(Pick.id(pb))
          before.id(lex(ka, kb), lex(kb, ka), ia, ib)

# a is listed before b: newer first, then by id, then by place
def before(a: Row, b: Row) -> Bool:
  match a b:
    case Row{ia, pa, ta} Row{ib, pb, tb}:
      +ka = tkey(ta)
      +kb = tkey(tb)
      before.go(lex(kb, ka), lex(ka, kb), pa, pb, ia, ib)

# x goes before the head of ys (or ys is empty)
def ins.head(+x: Row, ys: List<&2, Row>) -> Bool:
  match ys:
    case Nil{}:
      True{}
    case y <> rest:
      before(x, y)

# x put into the ordered ys; here: x goes before the head of ys
def ins(ys: List<&2, Row>, +x: Row, here: Bool) -> List<&2, Row>:
  match ys:
    case Nil{}:
      [x]
    case y <> +rest:
      match here:
        case True{}:
          x <> y <> rest
        case False{}:
          y <> ins(rest, x, ins.head(x, rest))

def sort.put(+x: Row, +s: List<&2, Row>) -> List<&2, Row>:
  ins(s, x, ins.head(x, s))

# the rows in listing order
def sort(xs: List<&2, Row>) -> List<&2, Row>:
  match xs:
    case Nil{}:
      Nil{}
    case x <> rest:
      sort.put(x, sort(rest))

# the listed sessions of the sessions directory, newest first
def rows(+os: List<&2, Obs>) -> List<&2, Row>:
  sort(rows.go(os, seens(os), 0n))
