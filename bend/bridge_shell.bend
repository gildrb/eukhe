# bridge_shell: runs the model of the approval gate (bend/tools.bend,
# part 4, `exec`) on an events file and prints what it did, line for line
# as the Rust bridge test prints the shell
# (crates/eukhe-shell/src/run/tests.rs, `the_gate_runs_as_its_model`).
# Build it with
#
#   bend bend/bridge_shell.bend -o <out>
#
# and run `<out> <events>`. An events file has one event per line:
#
#   s I E          a step of the script: id I, effect code E (0 read,
#                  1 write, 2 exec, 3 net), in script order
#   a E E ...      the auto set: the effect codes that run unasked
#   y B B ...      the user's answers to the gated steps, in order
#                  (1 approve, 0 deny); none left is a denial
#
# Then it prints
#
#   x I:E I:E ...  the steps that ran, in order
#   e fin          every step ran
#   e deny I       the user denied step I (or did not answer)

import Base
import ./tools.bend as Tl

# Reading
# -------

def tok.nat(s: String) -> Nat:
  Maybe.default(&2, Nat, Nat.read(s), 0n)

def tok.at(ws: List<&2, String>, k: Nat) -> String:
  Maybe.default(&2, String, List.get(&2, String, ws, k), "")

def arg(+ws: List<&2, String>, k: Nat) -> Nat:
  tok.nat(tok.at(ws, k))

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

def yes(n: Nat) -> Bool:
  match n:
    case 0n:
      False{}
    case 1n+m:
      True{}

def bools(ns: List<&2, Nat>) -> List<&2, Bool>:
  match ns:
    case Nil{}:
      Nil{}
    case n <> rest:
      yes(n) <> bools(rest)

def eff(n: Nat) -> Tl.Eff:
  match n:
    case 0n:
      Tl.Read{}
    case 1n+a:
      match a:
        case 0n:
          Tl.Write{}
        case 1n+b:
          match b:
            case 0n:
              Tl.Exec{}
            case 1n+c:
              Tl.Net{}

# What the events set up
# ----------------------

type St is Data:
  St{steps: List<&2, Tl.Step>, auto: List<&2, Nat>, answers: List<&2, Bool>}

# one line; h is its first word, ws all its words. Steps are kept newest
# first.
def line(h: String, +ws: List<&2, String>, +s: St) -> St:
  match h:
    case SCon{'s', r}:
      match s:
        case St{ss, a, y}:
          St{Tl.Step{arg(ws, 1n), eff(arg(ws, 2n))} <> ss, a, y}
    case SCon{'a', r}:
      match s:
        case St{ss, a, y}:
          St{ss, args(ws), y}
    case SCon{'y', r}:
      match s:
        case St{ss, a, y}:
          St{ss, a, bools(args(ws))}
    case r:
      s

def setup(ls: List<&2, String>, +s: St) -> St:
  match ls:
    case Nil{}:
      s
    case l <> rest:
      +ws = String.split(l, ' ')
      setup(rest, line(tok.at(ws, 0n), ws, s))

# Writing
# -------

def show.steps(ss: List<&2, Tl.Step>) -> String:
  match ss:
    case Nil{}:
      ""
    case +s <> rest:
      String.concat([" ", Nat.show(Tl.Step.id(s)), ":", Nat.show(Tl.Step.code(s)), show.steps(rest)])

def show.end(e: Tl.End) -> String:
  match e:
    case Tl.Finished{}:
      "e fin\n"
    case Tl.Denied{i}:
      String.concat(["e deny ", Nat.show(i), "\n"])

def show.ran(+r: Tl.Ran) -> String:
  String.concat(["x", show.steps(Tl.Ran.steps(r)), "\n", show.end(Tl.Ran.end(r))])

def run(s: St) -> String:
  match s:
    case St{ss, a, y}:
      show.ran(Tl.exec(List.reverse(&2, Tl.Step, ss), a, y))

def go(text: String) -> String:
  run(setup(String.lines(text), St{Nil{}, Nil{}, Nil{}}))

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
      IO.die(String, 2, "usage: bridge_shell <events>")
    case prog <> rest:
      match rest:
        case Nil{}:
          IO.die(String, 2, "usage: bridge_shell <events>")
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
