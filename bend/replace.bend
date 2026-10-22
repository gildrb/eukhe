# replace: the model of the launcher's replacement verdict (docs/daemon.md
# D1): which daemon a client start keeps or replaces. The Rust code
# crates/eukhe-tui/src/daemon_build.rs (`relation`, `replacement_verdict`)
# calls this model through the compiled Bend core.
#
# A build is its rank and its build id (the hello `runtime.buildId`). A
# rank is a list of numbers in lexicographic order; the empty rank (a
# version that does not parse) is below every other rank. `rank` reads the
# version X.Y.Z as [X, Y, 1, Z] and the version X.Y.Z-<suffix> (a dev or an
# older-scheme build) as [X, Y, 0, Z], so such a build ranks below the
# releases of its series X.Y. X, Y and Z are numbers written as semver.bend
# writes them (decimal, no leading zero) with at most 14 digits: a number
# of 15 digits or more is past the range of the compiled core's numbers
# (2^48 - 1, about 2.8 * 10^14), and its version does not parse; neither
# does a text of more than 64 chars (no version is that long), so Rust
# sends only the first 65 chars of a version (law replace_rank_cut).
#
# A client start meets the running daemon (or none). Builds with equal ids
# are the same build. Else the daemon is older (its rank is lower), newer
# (its rank is higher) or another build (equal ranks). Only an interactive
# start replaces a daemon, and only an older one; a background client
# (the dashboard, the gateway, ACP, a reconnect) keeps every daemon. A
# start with no daemon starts the client's build, which is no replacement.
#
# Every comparison of two numbers is one native compare (`Nat.cmp`): the
# daemon's hello controls its version, so no step walks a number.

import Base
import ./semver.bend as Sv

type Caller is Data:
  Interactive{}
  Background{}

# how the daemon's build relates to the client's build
type Rel is Data:
  Same{}
  Older{}
  Newer{}
  Other{}

type Verdict is Data:
  Replace{}
  Keep{rel: Rel}

type Build is Data:
  Build{rank: List<&2, Nat>, id: String}

type Start is Data:
  Start{build: Build, caller: Caller}

def Build.rank(b: Build) -> List<&2, Nat>:
  match b:
    case Build{r, i}:
      r

# The rank of a version
# ---------------------

# the digit is 0
def zero(d: Sv.Dig) -> Bool:
  match d:
    case Sv.D0{}:
      True{}
    case Sv.D1{}:
      False{}
    case Sv.D2{}:
      False{}
    case Sv.D3{}:
      False{}
    case Sv.D4{}:
      False{}
    case Sv.D5{}:
      False{}
    case Sv.D6{}:
      False{}
    case Sv.D7{}:
      False{}
    case Sv.D8{}:
      False{}
    case Sv.D9{}:
      False{}

# the most significant digit of the digits d <> rest (last digit first)
def top(rest: List<&2, Sv.Dig>, d: Sv.Dig) -> Sv.Dig:
  match rest:
    case Nil{}:
      d
    case r <> rr:
      top(rr, r)

# the digits (last digit first) are written as semver.bend writes a number:
# one digit, or a most significant digit that is not 0
def canon(ds: List<&2, Sv.Dig>) -> Bool:
  match ds:
    case Nil{}:
      False{}
    case d <> rest:
      match rest:
        case Nil{}:
          True{}
        case r <> rr:
          Bool.not(zero(top(rr, r)))

# the value of digits, last digit first (at most 14: below 10^14)
def fval(ds: List<&2, Sv.Dig>) -> Nat:
  match ds:
    case Nil{}:
      0n
    case d <> rest:
      Nat.add(Sv.Dig.val(d), Nat.mul(fval(rest), 10n))

def field.put(ok: Bool, ds: List<&2, Sv.Dig>) -> Maybe<&2, Nat>:
  match ok:
    case True{}:
      Some{fval(ds)}
    case False{}:
      None{}

# the number of a field's digits (last digit first): written as
# semver.bend writes it, with at most 14 digits; else none. The digits
# are counted before any is read.
def field(+ds: List<&2, Sv.Dig>) -> Maybe<&2, Nat>:
  field.put(Bool.and(Nat.is_le(List.length(&2, Sv.Dig, ds), 14n), canon(ds)), ds)

def rank.of3(a: Maybe<&2, Nat>, b: Maybe<&2, Nat>, c: Maybe<&2, Nat>, t: Nat) -> List<&2, Nat>:
  match a b c:
    case Some{x} Some{y} Some{z}:
      [x, y, t, z]
    case Some{x} Some{y} None{}:
      Nil{}
    case Some{x} None{} _:
      Nil{}
    case None{} _ _:
      Nil{}

# three fields, last first
def rank.fields(m: Maybe<&2, List<&2, List<&2, Sv.Dig>>>, t: Nat) -> List<&2, Nat>:
  match m:
    case None{}:
      Nil{}
    case Some{fs}:
      match fs:
        case Nil{}:
          Nil{}
        case c <> Nil{}:
          Nil{}
        case c <> b <> Nil{}:
          Nil{}
        case c <> b <> a <> Nil{}:
          rank.of3(field(a), field(b), field(c), t)
        case c <> b <> a <> d <> more:
          Nil{}

def core.at(dash: Bool, c: Char, rest: String) -> String:
  match dash:
    case True{}:
      SNil{}
    case False{}:
      SCon{c, rest}

# the text before the first '-'
def core(s: String) -> String:
  match s:
    case SNil{}:
      SNil{}
    case SCon{+c, r}:
      core.at(Char.is_eq(c, '-'), c, core(r))

def tier.at(dash: Bool, rest: Nat) -> Nat:
  match dash:
    case True{}:
      0n
    case False{}:
      rest

# 0 when the text has a '-' (a prerelease), else 1 (a release)
def tier(s: String) -> Nat:
  match s:
    case SNil{}:
      1n
    case SCon{c, r}:
      tier.at(Char.is_eq(c, '-'), tier(r))

def rank.cap(short: Bool, +s: String) -> List<&2, Nat>:
  match short:
    case True{}:
      rank.fields(Sv.Ver.fields(Sv.Sym.list(core(s)), Nil{}, Nil{}), tier(s))
    case False{}:
      Nil{}

# the rank of a version (the hello `appVersion`): a text of more than 64
# chars has none, so the first 65 chars of a text decide its rank
def rank(+s: String) -> List<&2, Nat>:
  rank.cap(Nat.is_le(String.length(s), 64n), s)

# a build of version v and build id i
def Build.of(v: String, i: String) -> Build:
  Build{rank(v), i}

# The order
# ---------

def lex.put(c: Cmp, t: Bool) -> Bool:
  match c:
    case LT{}:
      True{}
    case EQ{}:
      t
    case GT{}:
      False{}

# x before y, else (x equal to y) the order of the rest, t: one native
# compare
def lex(x: Nat, y: Nat, t: Bool) -> Bool:
  lex.put(Nat.cmp(x, y), t)

# rank xs is lower than rank ys
def lt(xs: List<&2, Nat>, ys: List<&2, Nat>) -> Bool:
  match xs ys:
    case Nil{} Nil{}:
      False{}
    case Nil{} y <> yr:
      True{}
    case x <> xr Nil{}:
      False{}
    case x <> xr y <> yr:
      lex(x, y, lt(xr, yr))

# The verdict
# -----------

def rel.put(same: Bool, older: Bool, newer: Bool) -> Rel:
  match same:
    case True{}:
      Same{}
    case False{}:
      match older:
        case True{}:
          Older{}
        case False{}:
          match newer:
            case True{}:
              Newer{}
            case False{}:
              Other{}

# how the daemon d relates to the client c
def relation(c: Build, d: Build) -> Rel:
  match c d:
    case Build{+rc, ic} Build{+rd, id}:
      rel.put(String.eq(ic, id), lt(rd, rc), lt(rc, rd))

def verdict.put(r: Rel, k: Caller) -> Verdict:
  match r:
    case Same{}:
      Keep{Same{}}
    case Older{}:
      match k:
        case Interactive{}:
          Replace{}
        case Background{}:
          Keep{Older{}}
    case Newer{}:
      Keep{Newer{}}
    case Other{}:
      Keep{Other{}}

# the verdict of a start of client c by caller k on the daemon d
def verdict(c: Build, d: Build, k: Caller) -> Verdict:
  verdict.put(relation(c, d), k)

# Client starts
# -------------

def after.put(v: Verdict, c: Build, d: Build) -> Build:
  match v:
    case Replace{}:
      c
    case Keep{r}:
      d

# the daemon after a start (none running: the client's build starts)
def after(s: Start, d: Maybe<&2, Build>) -> Build:
  match s:
    case Start{+c, k}:
      match d:
        case None{}:
          c
        case Some{+b}:
          after.put(verdict(c, b, k), c, b)

def replaces.put(v: Verdict) -> Nat:
  match v:
    case Replace{}:
      1n
    case Keep{r}:
      0n

# 1 when the start replaces the daemon d
def replaces(s: Start, d: Maybe<&2, Build>) -> Nat:
  match s:
    case Start{+c, k}:
      match d:
        case None{}:
          0n
        case Some{+b}:
          replaces.put(verdict(c, b, k))

# the running daemon after each start
def trace.go(ss: List<&2, Start>, d: Maybe<&2, Build>) -> List<&2, Build>:
  match ss:
    case Nil{}:
      Nil{}
    case s <> rest:
      +n = after(s, d)
      n <> trace.go(rest, Some{n})

def daemons(ss: List<&2, Start>) -> List<&2, Build>:
  trace.go(ss, None{})

# the replacements
def replaced.go(ss: List<&2, Start>, +d: Maybe<&2, Build>) -> Nat:
  match ss:
    case Nil{}:
      0n
    case +s <> rest:
      Nat.add(replaces(s, d), replaced.go(rest, Some{after(s, d)}))

def replaced(ss: List<&2, Start>) -> Nat:
  replaced.go(ss, None{})

# The laws' terms
# ---------------

# b ranks below no build of seen
def not_below(seen: List<&2, Build>, +b: Build) -> Bool:
  match seen:
    case Nil{}:
      True{}
    case e <> t:
      Bool.and(Bool.not(lt(Build.rank(b), Build.rank(e))), not_below(t, b))

# no build ranks below a build before it
def never_back.go(xs: List<&2, Build>, +seen: List<&2, Build>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case +x <> t:
      Bool.and(not_below(seen, x), never_back.go(t, x <> seen))

def never_back(xs: List<&2, Build>) -> Bool:
  never_back.go(xs, Nil{})

def ranks_eq(xs: List<&2, Nat>, ys: List<&2, Nat>) -> Bool:
  match xs ys:
    case Nil{} Nil{}:
      True{}
    case Nil{} y <> yr:
      False{}
    case x <> xr Nil{}:
      False{}
    case x <> xr y <> yr:
      Bool.and(Nat.is_eq(x, y), ranks_eq(xr, yr))

def build_eq(a: Build, b: Build) -> Bool:
  match a b:
    case Build{ra, ia} Build{rb, ib}:
      Bool.and(String.eq(ia, ib), ranks_eq(ra, rb))

# b is one of bs
def has(bs: List<&2, Build>, +b: Build) -> Bool:
  match bs:
    case Nil{}:
      False{}
    case e <> t:
      Bool.or(build_eq(e, b), has(t, b))

# every start's build is one of bs
def covers(+bs: List<&2, Build>, ss: List<&2, Start>) -> Bool:
  match ss:
    case Nil{}:
      True{}
    case s <> rest:
      match s:
        case Start{c, k}:
          Bool.and(has(bs, c), covers(bs, rest))
