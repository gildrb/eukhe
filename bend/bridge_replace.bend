# bridge_replace: runs the model of the launcher's replacement verdict
# (bend/replace.bend) on an events file and prints what it did, line for
# line as the Rust bridge test prints `daemon_build::replacement_verdict`
# (crates/eukhe-tui/src/daemon_build/bridge.rs,
# `the_replacement_verdict_runs_as_its_model`). Build it with
#
#   bend bend/bridge_replace.bend -o <out>
#
# and run `<out> <events>`. An events file has one event per line:
#
#   s V I C        a client start: version V (the hello `appVersion`), build
#                  id I (a number), caller C (`i` interactive, `b`
#                  background)
#
# Then it prints, for each start,
#
#   W R I          the verdict W (`start` when no daemon ran, `replace`,
#                  `same`, `older`, `newer`, `other`) and the rank R
#                  (`-` for none, else its numbers joined by dots) and the
#                  id I of the daemon after the start
#
# and at the end `r N`, the replacements.
#
# A version X.Y.Z (semver.bend's version: decimal numbers without leading
# zeros) ranks [X, Y, 1, Z]; a version X.Y.Z-<suffix> ranks [X, Y, 0, Z];
# any other text has no rank (the empty rank).

import Base
import ./semver.bend as Sv
import ./replace.bend as Rp

def tok.nat(s: String) -> Nat:
  Maybe.default(&2, Nat, Nat.read(s), 0n)

def tok.at(ws: List<&2, String>, k: Nat) -> String:
  Maybe.default(&2, String, List.get(&2, String, ws, k), "")

def before_dash(s: String) -> String:
  match s:
    case SNil{}:
      SNil{}
    case SCon{'-', r}:
      SNil{}
    case SCon{c, r}:
      SCon{c, before_dash(r)}

def has_dash(s: String) -> Bool:
  match s:
    case SNil{}:
      False{}
    case SCon{'-', r}:
      True{}
    case SCon{c, r}:
      has_dash(r)

def tier(dash: Bool) -> Nat:
  match dash:
    case True{}:
      0n
    case False{}:
      1n

def rank.of(v: Maybe<&2, Sv.Ver>, dash: Bool) -> List<&2, Nat>:
  match v:
    case None{}:
      Nil{}
    case Some{w}:
      match w:
        case Sv.Ver{a, b, c}:
          [a, b, tier(dash), c]

def rank(+s: String) -> List<&2, Nat>:
  rank.of(Sv.Ver.parse(before_dash(s)), has_dash(s))

def caller(s: String) -> Rp.Caller:
  match s:
    case SCon{'i', r}:
      Rp.Interactive{}
    case r:
      Rp.Background{}

def show.nums(xs: List<&2, Nat>) -> String:
  match xs:
    case Nil{}:
      ""
    case x <> rest:
      match rest:
        case Nil{}:
          Nat.show(x)
        case y <> more:
          String.concat([Nat.show(x), ".", show.nums(y <> more)])

def show.rank(xs: List<&2, Nat>) -> String:
  match xs:
    case Nil{}:
      "-"
    case x <> rest:
      show.nums(x <> rest)

def show.build(b: Rp.Build) -> String:
  match b:
    case Rp.Build{r, i}:
      String.concat([show.rank(r), " ", Nat.show(i)])

def show.verdict(v: Rp.Verdict) -> String:
  match v:
    case Rp.Replace{}:
      "replace"
    case Rp.Keep{r}:
      match r:
        case Rp.Same{}:
          "same"
        case Rp.Older{}:
          "older"
        case Rp.Newer{}:
          "newer"
        case Rp.Other{}:
          "other"

# the verdict of a start on the daemon before it
def show.start(s: Rp.Start, d: Maybe<&2, Rp.Build>) -> String:
  match s:
    case Rp.Start{c, k}:
      match d:
        case None{}:
          "start"
        case Some{b}:
          show.verdict(Rp.verdict(c, b, k))

# each start beside the daemon after it
def show.trace(ss: List<&2, Rp.Start>, ds: List<&2, Rp.Build>, d: Maybe<&2, Rp.Build>) -> String:
  match ss ds:
    case s <> rest +b <> more:
      String.concat([show.start(s, d), " ", show.build(b), "\n", show.trace(rest, more, Some{b})])
    case _ _:
      ""

def start.of(h: String, +ws: List<&2, String>) -> Maybe<&2, Rp.Start>:
  match h:
    case SCon{'s', x}:
      Some{Rp.Start{Rp.Build{rank(tok.at(ws, 1n)), tok.nat(tok.at(ws, 2n))}, caller(tok.at(ws, 3n))}}
    case x:
      None{}

def starts.put(m: Maybe<&2, Rp.Start>, rest: List<&2, Rp.Start>) -> List<&2, Rp.Start>:
  match m:
    case None{}:
      rest
    case Some{s}:
      s <> rest

def starts(ls: List<&2, String>) -> List<&2, Rp.Start>:
  match ls:
    case Nil{}:
      Nil{}
    case l <> rest:
      +ws = String.split(l, ' ')
      starts.put(start.of(tok.at(ws, 0n), ws), starts(rest))

def report(+ss: List<&2, Rp.Start>) -> String:
  String.concat([show.trace(ss, Rp.daemons(ss), None{}), "r ", Nat.show(Rp.replaced(ss)), "\n"])

def read.done(r: Result<&1, &1, U32 & String, String>) -> String:
  match r:
    case Done{text}:
      text
    case Fail{e}:
      ""

def read.file(m: File & Result<&1, &1, U32 & String, String>) -> IO(String):
  (f, r) = m
  do IO<String>:
    Unit <- File.close(f)
    IO.pure(String, read.done(r))

def scenario(args: List<String>) -> IO(String):
  match args:
    case Nil{}:
      IO.die(String, 2, "usage: bridge_replace <events>")
    case prog <> rest:
      match rest:
        case Nil{}:
          IO.die(String, 2, "usage: bridge_replace <events>")
        case path <> more:
          do IO<String>:
            f : File <- IO.try(File, File.open(path, "r"))
            m : File & Result<&1, &1, U32 & String, String> <- File.read(f, 1073741824)
            read.file(m)

def main() -> IO(Unit):
  do IO<Unit>:
    args : List<String> <- IO.args()
    text : String <- scenario(args)
    IO.write(report(starts(String.lines(text))))
