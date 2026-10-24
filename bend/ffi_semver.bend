# ffi_semver: the release-version rule of the compiled Bend core
# (bend/semver.bend) behind one entry, `ffi`. A request names its question
# and carries its texts (crates/eukhe-bend/WIRE.md is the grammar):
#
#   tag 0  release   the workspace version (String),
#                    the repository's tags (List<String>)
#                    -> 0                     the workspace version is no version
#                       1                     it is X.Y.(1+z), no series start
#                       2, next, newer tags   the next release X.Y.P is not
#                                             newer than these version tags
#                       3, version, tag, title   the release
#   tag 1  series    the workspace version, a release version (Strings)
#                    -> 0  the release is no version
#                       1  it is not of the workspace's series (or the
#                          workspace version is no version)
#                       2  it is a version of the workspace's series
#
# The model reads a number in unary (O(its value)): a request whose texts
# hold a run of more than digits() digits (a workspace or release version,
# or a tag `eukhe-v...`; other tags name no version and are never read)
# answers the error form, never a slow or stopped evaluation. Malformed
# input answers the wire's error form, never a default. laws/semver.bend
# (section entry) states this file's laws; PROOF.bend proves them. Pure:
# no IO, no @unsafe.

import Base
import ./wire.bend as W
import ./semver.bend as Sv

# A request of the entry
type Req is Data:
  QRelease{cargo: String, tags: List<&2, String>}
  QSeries{workspace: String, release: String}

# The bound
# ---------

# the most digits in a row a read text may hold: a 6-digit number reads
# in about 20 ms (the model is unary), and no eukhe version comes near it
def digits() -> Nat:
  6n

def digit.of(y: Sv.Sym) -> Bool:
  match y:
    case Sv.Digit{d}:
      True{}
    case Sv.Dot{}:
      False{}
    case Sv.Other{}:
      False{}

# c is a decimal digit
def digit(c: Char) -> Bool:
  digit.of(Sv.Sym.of(c))

# s starts with n digits
def lead(n: Nat, s: String) -> Bool:
  match n:
    case 0n:
      True{}
    case 1n+m:
      match s:
        case SNil{}:
          False{}
        case SCon{c, t}:
          Bool.and(digit(c), lead(m, t))

# some run of s holds more than digits() digits
def long(s: String) -> Bool:
  match s:
    case SNil{}:
      False{}
    case SCon{+c, +t}:
      Bool.or(lead(1n+digits(), SCon{c, t}), long(t))

# no run of s holds more than digits() digits
def short(s: String) -> Bool:
  Bool.not(long(s))

def short.tag.of(m: Maybe<&2, String>) -> Bool:
  match m:
    case None{}:
      True{}
    case Some{r}:
      short(r)

# a tag the model never reads (no `eukhe-v`), or a short one
def short.tag(t: String) -> Bool:
  short.tag.of(Sv.Tag.strip(t))

def short.tags(ts: List<&2, String>) -> Bool:
  match ts:
    case Nil{}:
      True{}
    case t <> r:
      Bool.and(short.tag(t), short.tags(r))

# every text of the request the model reads is short
def short.req(q: Req) -> Bool:
  match q:
    case QRelease{c, ts}:
      Bool.and(short(c), short.tags(ts))
    case QSeries{w, r}:
      Bool.and(short(w), short(r))

# Requests
# --------

def get_release.tags(c: String, r: W.Dec<List<&2, String>>) -> W.Dec<Req>:
  match r:
    case W.Got{ts, s}:
      W.Got{QRelease{c, ts}, s}
    case W.Bad{}:
      W.Bad{}

def get_release(r: W.Dec<String>) -> W.Dec<Req>:
  match r:
    case W.Got{c, s}:
      get_release.tags(c, W.get_list(~String, ~W.get_str, s))
    case W.Bad{}:
      W.Bad{}

def get_series.release(w: String, r: W.Dec<String>) -> W.Dec<Req>:
  match r:
    case W.Got{v, s}:
      W.Got{QSeries{w, v}, s}
    case W.Bad{}:
      W.Bad{}

def get_series(r: W.Dec<String>) -> W.Dec<Req>:
  match r:
    case W.Got{w, s}:
      get_series.release(w, W.get_str(s))
    case W.Bad{}:
      W.Bad{}

def get_req.tag(t: Nat, s: String) -> W.Dec<Req>:
  match t:
    case 0n:
      get_release(W.get_str(s))
    case 1n:
      get_series(W.get_str(s))
    case 2n+u:
      W.Bad{}

def get_req.start(r: W.Dec<Nat>) -> W.Dec<Req>:
  match r:
    case W.Got{t, s}:
      get_req.tag(t, s)
    case W.Bad{}:
      W.Bad{}

def get_req(s: String) -> W.Dec<Req>:
  get_req.start(W.get_nat(s))

# Replies
# -------

# the version tags among ts that the release n is not newer than, in order
def newer.keep(old: Bool, t: String, rest: List<&2, String>) -> List<&2, String>:
  match old:
    case True{}:
      rest
    case False{}:
      t <> rest

def newer(+n: Sv.Ver, ts: List<&2, String>) -> List<&2, String>:
  match ts:
    case Nil{}:
      Nil{}
    case +t <> r:
      newer.keep(Sv.Rel.older(n, Sv.Tag.ver(t)), t, newer(n, r))

# a release: its version, its tag and its title
def put_rel(+v: Sv.Ver, rest: String) -> String:
  W.put_str(Sv.Ver.show(v), W.put_str(Sv.Tag.of(v), W.put_str(Sv.Rel.title(v), rest)))

# no release from the workspace version X.Y.c: why
def release.patch(a: Nat, b: Nat, c: Nat, +ts: List<&2, String>) -> String:
  match c:
    case 0n:
      +n = Sv.Rel.next(Sv.Ver{a, b, 0n}, ts)
      W.put_nat(2n, W.put_str(Sv.Ver.show(n), W.put_list(~String, ~W.put_str, newer(n, ts), "")))
    case 1n+z:
      W.put_nat(1n, "")

# no release: why (m: the workspace version read)
def release.miss(m: Maybe<&2, Sv.Ver>, +ts: List<&2, String>) -> String:
  match m:
    case None{}:
      W.put_nat(0n, "")
    case Some{v}:
      match v:
        case Sv.Ver{a, b, c}:
          release.patch(a, b, c, ts)

def release.put(r: Maybe<&2, Sv.Ver>, c: String, +ts: List<&2, String>) -> String:
  match r:
    case Some{v}:
      W.put_nat(3n, put_rel(v, ""))
    case None{}:
      release.miss(Sv.Ver.parse(c), ts)

def series.in(b: Bool) -> Nat:
  match b:
    case True{}:
      2n
    case False{}:
      1n

def series.of(r: Maybe<&2, Sv.Ver>, w: Maybe<&2, Sv.Ver>) -> Nat:
  match r:
    case None{}:
      0n
    case Some{v}:
      match w:
        case None{}:
          1n
        case Some{s}:
          series.in(Sv.Ver.in_series(s, v))

# the reply of a request: the model's decision, encoded
def answer(q: Req) -> String:
  match q:
    case QRelease{+c, +ts}:
      release.put(Sv.Rel.release(c, ts), c, ts)
    case QSeries{w, r}:
      W.put_nat(series.of(Sv.Ver.parse(r), Sv.Ver.parse(w)), "")

def ffi.short(+q: Req, ok: Bool) -> String:
  match ok:
    case True{}:
      answer(q)
    case False{}:
      W.err("semver: a version number of more than 6 digits")

def ffi.done(+q: Req, end: Bool) -> String:
  match end:
    case True{}:
      ffi.short(q, short.req(q))
    case False{}:
      W.err("semver: input left after the request")

def ffi.got(r: W.Dec<Req>) -> String:
  match r:
    case W.Got{q, +s}:
      ffi.done(q, W.end(s))
    case W.Bad{}:
      W.err("semver: malformed request")

# the entry: decode the request, answer the model's decision
def ffi(input: String) -> String:
  ffi.got(get_req(input))
