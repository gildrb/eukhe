# tools: the model of the tool surface.
#
# 1. The roster. A session starts with a fixed roster of tools. Tools
#    that come later (MCP servers, skills, extensions) join the dynamic
#    set behind the `dyn` tool; the roster sent with each request never
#    changes, so the prompt cache stays valid.
# 2. The schema. Every tool schema has the intent parameter `i` (id 0)
#    and a version of at least 1.
# 3. A path. An internal URL's path is a list of segments under the root
#    of its scheme. `..` goes up one; a path that goes above its root is
#    rejected, never clamped.
# 4. The shell step. A shell script runs step by step. A step has a set
#    of effects: every effect of every part of it (its command, each
#    redirection, each path it names; every command an external script
#    holds); a step has the secret effect only when a part of it names a
#    path that is or holds a secret. Every step runs unasked, but a step
#    a part of which writes an own path (eukhe's own config and
#    credentials, the session record, a protected file of a check): it is
#    refused, and the script stops at it: it and no later step runs
#    (`verdict`, `script`).
#
# A recursive scan takes the test of its first item as a parameter (Bend
# matches only parameters); `*.at` computes that test.

import Base

def elem(xs: List<&2, Nat>, +x: Nat) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case y <> rest:
      Bool.or(Nat.is_eq(y, x), elem(rest, x))

# 1. The roster
# -------------

type Ev is Data:
  Join{t: Nat}   # a tool appears (an MCP server, a skill, an extension)
  Quit{t: Nat}   # a tool goes away
  Turn{}         # a request is sent

# A session: the roster, the dynamic tools, the rosters sent so far
# (newest first; a step puts in front, so it never copies a list)
type Sess is Data:
  Sess{roster: List<&2, Nat>, dyn: List<&2, Nat>, sent: List<&2, List<&2, Nat>>}

def Sess.roster(s: Sess) -> List<&2, Nat>:
  match s:
    case Sess{r, d, x}:
      r

def Sess.dyn(s: Sess) -> List<&2, Nat>:
  match s:
    case Sess{r, d, x}:
      d

def Sess.sent(s: Sess) -> List<&2, List<&2, Nat>>:
  match s:
    case Sess{r, d, x}:
      x

# the first item of xs is t
def is.at(+xs: List<&2, Nat>, +t: Nat) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case y <> rest:
      Nat.is_eq(y, t)

# remove every copy of t; hit is is.at(xs, t)
def drop.go(xs: List<&2, Nat>, +t: Nat, hit: Bool) -> List<&2, Nat>:
  match xs:
    case Nil{}:
      Nil{}
    case y <> +rest:
      match hit:
        case True{}:
          drop.go(rest, t, is.at(rest, t))
        case False{}:
          y <> drop.go(rest, t, is.at(rest, t))

def drop(+xs: List<&2, Nat>, +t: Nat) -> List<&2, Nat>:
  drop.go(xs, t, is.at(xs, t))

def step(s: Sess, e: Ev) -> Sess:
  match s:
    case Sess{+r, d, x}:
      match e:
        case Join{t}:
          Sess{r, t <> d, x}
        case Quit{t}:
          Sess{r, drop(d, t), x}
        case Turn{}:
          Sess{r, d, r <> x}

def run(es: List<&2, Ev>, s: Sess) -> Sess:
  match es:
    case Nil{}:
      s
    case e <> rest:
      run(rest, step(s, e))

# two lists of tool ids are equal
def ids.eq(xs: List<&2, Nat>, ys: List<&2, Nat>) -> Bool:
  match xs:
    case Nil{}:
      match ys:
        case Nil{}:
          True{}
        case y <> yr:
          False{}
    case x <> xr:
      match ys:
        case Nil{}:
          False{}
        case y <> yr:
          Bool.and(Nat.is_eq(x, y), ids.eq(xr, yr))

# every roster of xs is r
def all_eq(xs: List<&2, List<&2, Nat>>, +r: List<&2, Nat>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case x <> rest:
      Bool.and(ids.eq(x, r), all_eq(rest, r))

# a call through `dyn` reaches tool t
def dyn_call(+s: Sess, +t: Nat) -> Bool:
  elem(Sess.dyn(s), t)

# 2. The schema
# -------------

type Schema is Data:
  Schema{params: List<&2, Nat>, version: Nat}

# the intent parameter
def intent() -> Nat:
  0n

def add_intent(has: Bool, +ps: List<&2, Nat>) -> List<&2, Nat>:
  match has:
    case True{}:
      ps
    case False{}:
      intent() <> ps

# the schema a tool declares, as the harness sends it
def build(s: Schema) -> Schema:
  match s:
    case Schema{+ps, v}:
      Schema{add_intent(elem(ps, intent()), ps), Nat.max(v, 1n)}

def Schema.params(s: Schema) -> List<&2, Nat>:
  match s:
    case Schema{p, v}:
      p

def Schema.version(s: Schema) -> Nat:
  match s:
    case Schema{p, v}:
      v

# 3. A path
# ---------

type Seg is Data:
  Name{n: Nat}
  Up{}
  Here{}

# the path under the root after segs, from the names so far (deepest
# first); None when a segment goes above the root
def walk(segs: List<&2, Seg>, at: List<&2, Nat>) -> Maybe<&2, List<&2, Nat>>:
  match segs:
    case Nil{}:
      Some{at}
    case s <> rest:
      match s:
        case Name{n}:
          walk(rest, n <> at)
        case Here{}:
          walk(rest, at)
        case Up{}:
          match at:
            case Nil{}:
              None{}
            case a <> above:
              walk(rest, above)

def resolve(segs: List<&2, Seg>) -> Maybe<&2, List<&2, Nat>>:
  walk(segs, Nil{})

# the depth of segs after each segment stays at least -d: segs never go
# more than d levels above where they start
def stays(segs: List<&2, Seg>, d: Nat) -> Bool:
  match segs:
    case Nil{}:
      True{}
    case s <> rest:
      match s:
        case Name{n}:
          stays(rest, 1n+d)
        case Here{}:
          stays(rest, d)
        case Up{}:
          match d:
            case 0n:
              False{}
            case 1n+e:
              stays(rest, e)

# 4. The shell step
# -----------------

# Effect codes: 0 read, 1 write, 2 exec, 3 net, 4 outside, 5 protected,
# 6 secret. A step: its id and its effects.
type Step is Data:
  Step{id: Nat, effs: List<&2, Nat>}

# the effects of a step made of parts: every effect of every part
def join(ps: List<&2, List<&2, Nat>>) -> List<&2, Nat>:
  match ps:
    case Nil{}:
      Nil{}
    case p <> rest:
      List.append(&2, Nat, p, join(rest))

# A part of a step: its own effect codes (the command's from the table,
# a redirection's from its target's class) and whether it names a path
# that is or holds a secret (an operand, an option value or a redirection
# target; the working directory only for a command that reads it because
# it names no path of its own). Only a named secret path gives the secret
# effect (6): the table and a class give the other codes.
type Part is Data:
  Part{own: List<&2, Nat>, secret: Bool}

def Part.secret(p: Part) -> Bool:
  match p:
    case Part{o, s}:
      s

# c, unless drop
def plain.add(drop: Bool, c: Nat, acc: List<&2, Nat>) -> List<&2, Nat>:
  match drop:
    case True{}:
      acc
    case False{}:
      c <> acc

# the codes of cs that are not secret (6)
def plain(cs: List<&2, Nat>) -> List<&2, Nat>:
  match cs:
    case Nil{}:
      Nil{}
    case +c <> rest:
      plain.add(Nat.is_eq(c, 6n), c, plain(rest))

# the effects of a part: its own codes, and secret when it names a secret
# path
def part.effs(p: Part) -> List<&2, Nat>:
  match p:
    case Part{o, s}:
      match s:
        case True{}:
          6n <> plain(o)
        case False{}:
          plain(o)

def parts.effs(ps: List<&2, Part>) -> List<&2, List<&2, Nat>>:
  match ps:
    case Nil{}:
      Nil{}
    case p <> rest:
      part.effs(p) <> parts.effs(rest)

# some part names a path that is or holds a secret
def parts.secret(ps: List<&2, Part>) -> Bool:
  match ps:
    case Nil{}:
      False{}
    case p <> rest:
      Bool.or(Part.secret(p), parts.secret(rest))

# A part of a step as its verdict reads it: its own effect codes, whether
# it names a path that is or holds a secret, and whether it writes an own
# path (eukhe's own config and credentials, the session record, a
# protected file of a check)
type Piece is Data:
  Piece{own: List<&2, Nat>, secret: Bool, mine: Bool}

# the part's effects: those of the same part without the own fact
def piece.effs(p: Piece) -> List<&2, Nat>:
  match p:
    case Piece{o, s, m}:
      part.effs(Part{o, s})

# the effects of a step made of pieces: every effect of every piece
def pieces.effs(ps: List<&2, Piece>) -> List<&2, Nat>:
  match ps:
    case Nil{}:
      Nil{}
    case p <> rest:
      List.append(&2, Nat, piece.effs(p), pieces.effs(rest))

# some piece writes an own path
def pieces.mine(ps: List<&2, Piece>) -> Bool:
  match ps:
    case Nil{}:
      False{}
    case p <> rest:
      match p:
        case Piece{o, s, m}:
          Bool.or(m, pieces.mine(rest))

# What becomes of a step: it runs, or it is refused (it writes an own path)
type Verdict is Data:
  Runs{}
  Refused{}

def verdict.of(mine: Bool) -> Verdict:
  match mine:
    case True{}:
      Refused{}
    case False{}:
      Runs{}

# the verdict of a step made of pieces: refused exactly when a piece
# writes an own path
def verdict(ps: List<&2, Piece>) -> Verdict:
  verdict.of(pieces.mine(ps))

# A step of a script as it is about to run: its id, its effects, and
# whether it writes an own path
type Planned is Data:
  Planned{id: Nat, effs: List<&2, Nat>, mine: Bool}

# the step with id i made of pieces ps
def plan(i: Nat, +ps: List<&2, Piece>) -> Planned:
  Planned{i, pieces.effs(ps), pieces.mine(ps)}

# How a script ended
type Halt is Data:
  AllRan{}           # every step ran
  StoppedAt{at: Nat} # step `at` writes an own path: it and later steps did not run

# How a script ran: the steps that ran, in order, and how it ended
type Did is Data:
  Did{ran: List<&2, Step>, end: Halt}

def did.add(s: Step, d: Did) -> Did:
  match d:
    case Did{ss, e}:
      Did{s <> ss, e}

# run a script: each step runs in order, until a step that writes an own
# path; that one and every later step do not run. A step is a pipeline,
# whose stages start together: one stage that writes an own path keeps
# them all from running. The model of the loop Rust runs
# (crates/eukhe-shell/src/run.rs); no entry runs it.
def script(ss: List<&2, Planned>) -> Did:
  match ss:
    case Nil{}:
      Did{Nil{}, AllRan{}}
    case s <> rest:
      match s:
        case Planned{i, e, m}:
          match m:
            case True{}:
              Did{Nil{}, StoppedAt{i}}
            case False{}:
              did.add(Step{i, e}, script(rest))
