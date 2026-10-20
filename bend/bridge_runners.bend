# bridge_runners: runs the model of the runners of code (bend/runners.bend)
# on an events file and prints what it did, line for line as the Rust
# bridge test prints the real session
# (crates/eukhe-core/src/durable/runner/tests.rs). Build it with
#
#   bend bend/bridge_runners.bend -o <out>
#
# and run `<out> <events>`. An events file has one event per line:
#
#   r C            print the registry of a session with chat memory (C 1)
#                  or without it (C 0)
#   a E E ...      the auto set: the effect codes that run unasked
#   p P            who answers: 0 no client, 1 a client that gives no
#                  answer, 2 a client that denies, 3 a client that approves
#   g              one `ipython` call under the auto set and the asker
#
# `r` prints one line per tool, in install order:
#
#   NAME caps E E ... gate none|step|call
#
# and `g` prints
#
#   asked 0|1      the call asked the client
#   end ran|denied|unanswered

import Base
import ./runners.bend as Rn

# Reading
# -------

def tok.nat(s: String) -> Nat:
  Maybe.default(&2, Nat, Nat.read(s), 0n)

def tok.at(ws: List<&2, String>, k: Nat) -> String:
  Maybe.default(&2, String, List.get(&2, String, ws, k), "")

# every word as a number
def nats(ws: List<&2, String>) -> List<&2, Nat>:
  match ws:
    case Nil{}:
      Nil{}
    case w <> rest:
      tok.nat(w) <> nats(rest)

# the words after the first, as numbers
def args(ws: List<&2, String>) -> List<&2, Nat>:
  match ws:
    case Nil{}:
      Nil{}
    case w <> rest:
      nats(rest)

def asker(n: Nat) -> Rn.Asker:
  match n:
    case 0n:
      Rn.NoClient{}
    case 1n+a:
      match a:
        case 0n:
          Rn.Silent{}
        case 1n+b:
          match b:
            case 0n:
              Rn.Says{False{}}
            case 1n+c:
              Rn.Says{True{}}

# Writing
# -------

def show.caps(cs: List<&2, Nat>) -> String:
  match cs:
    case Nil{}:
      ""
    case c <> rest:
      String.concat([" ", Nat.show(c), show.caps(rest)])

def show.gate(g: Rn.Gate) -> String:
  match g:
    case Rn.Ungated{}:
      "none"
    case Rn.EachStep{}:
      "step"
    case Rn.EachCall{}:
      "call"

def show.tools(ts: List<&2, Rn.Tool>) -> String:
  match ts:
    case Nil{}:
      ""
    case t <> rest:
      match t:
        case Rn.Tool{n, c, g}:
          String.concat([n, " caps", show.caps(c), " gate ", show.gate(g), "\n", show.tools(rest)])

def show.bool(b: Bool) -> String:
  match b:
    case True{}:
      "1"
    case False{}:
      "0"

def show.end(e: Rn.End) -> String:
  match e:
    case Rn.Ran{h}:
      "ran"
    case Rn.Refused{w}:
      match w:
        case Rn.Denied{}:
          "denied"
        case Rn.Unanswered{}:
          "unanswered"

def show.out(o: Rn.Out) -> String:
  match o:
    case Rn.Out{a, e}:
      String.concat(["asked ", show.bool(a), "\nend ", show.end(e), "\n"])

# the caps of `ipython` in the registry (none when it is missing)
def ipython.caps(m: Maybe<&2, Rn.Tool>) -> List<&2, Nat>:
  match m:
    case None{}:
      Nil{}
    case Some{t}:
      Rn.Tool.caps(t)

# What the events set up
# ----------------------

type St is Data:
  St{auto: List<&2, Nat>, asker: Rn.Asker, out: String}

# one line; h is its first word, ws all its words
def line(h: String, +ws: List<&2, String>, s: St) -> St:
  match h:
    case SCon{'r', r}:
      match s:
        case St{a, k, o}:
          St{a, k, String.append(o, show.tools(Rn.registry(Nat.is_eq(tok.nat(tok.at(ws, 1n)), 1n))))}
    case SCon{'a', r}:
      match s:
        case St{a, k, o}:
          St{args(ws), k, o}
    case SCon{'p', r}:
      match s:
        case St{a, k, o}:
          St{a, asker(tok.nat(tok.at(ws, 1n))), o}
    case SCon{'g', r}:
      match s:
        case St{+a, +k, o}:
          St{a, k, String.append(o, show.out(Rn.cell(ipython.caps(Rn.find(Rn.registry(False{}), "ipython")), a, k)))}
    case r:
      s

def setup(ls: List<&2, String>, s: St) -> St:
  match ls:
    case Nil{}:
      s
    case l <> rest:
      +ws = String.split(l, ' ')
      setup(rest, line(tok.at(ws, 0n), ws, s))

def St.out(s: St) -> String:
  match s:
    case St{a, k, o}:
      o

def go(text: String) -> String:
  St.out(setup(String.lines(text), St{Nil{}, Rn.NoClient{}, ""}))

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
      IO.die(String, 2, "usage: bridge_runners <events>")
    case prog <> rest:
      match rest:
        case Nil{}:
          IO.die(String, 2, "usage: bridge_runners <events>")
        case path <> more:
          do IO<String>:
            f : File <- IO.try(File, File.open(path, "r"))
            m : File & Result<&1, &1, U32 & String, String> <- File.read(f, 1073741824)
            read.file(m)

def main() -> IO(Unit):
  do IO<Unit>:
    args : List<String> <- IO.args()
    text : String <- scenario(args)
    IO.write(go(text))
