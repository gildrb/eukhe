# replace: the model of the launcher's replacement verdict (docs/daemon.md
# D1): which daemon a client start keeps or replaces. The Rust code is
# crates/eukhe-tui/src/daemon_build.rs (`relation`, `replacement_verdict`);
# the bridge (bend/bridge_replace.bend, crates/eukhe-tui/src/daemon_build/
# bridge.rs) runs both on the same client starts.
#
# A build is its rank and its build id (the bridge numbers the ids). A
# rank is a list of numbers in lexicographic order; the empty rank (a
# version that does not parse) is below every other rank. The bridge reads
# the version X.Y.Z as [X, Y, 1, Z] and the version X.Y.Z-<suffix> (a dev
# or an older-scheme build) as [X, Y, 0, Z], so such a build ranks below
# the releases of its series X.Y.
#
# A client start meets the running daemon (or none). Builds with equal ids
# are the same build. Else the daemon is older (its rank is lower), newer
# (its rank is higher) or another build (equal ranks). Only an interactive
# start replaces a daemon, and only an older one; a background client
# (the dashboard, the gateway, ACP, a reconnect) keeps every daemon. A
# start with no daemon starts the client's build, which is no replacement.

import Base

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
  Build{rank: List<&2, Nat>, id: Nat}

type Start is Data:
  Start{build: Build, caller: Caller}

def Build.rank(b: Build) -> List<&2, Nat>:
  match b:
    case Build{r, i}:
      r

# The order
# ---------

# x before y, else (x equal to y) the order of the rest, t
def lex(x: Nat, y: Nat, t: Bool) -> Bool:
  match x y:
    case 0n 0n:
      t
    case 0n 1n+q:
      True{}
    case 1n+p 0n:
      False{}
    case 1n+p 1n+q:
      lex(p, q, t)

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
      rel.put(Nat.is_eq(ic, id), lt(rd, rc), lt(rc, rd))

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
      Bool.and(Nat.is_eq(ia, ib), ranks_eq(ra, rb))

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
