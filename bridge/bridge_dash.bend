# bridge_dash: runs the model of the dashboard's pairing gate
# (bend/dash.bend) on an events file and prints what it did, line for
# line as the Rust bridge test prints the dashboard
# (crates/eukhe-dashboard/src/pairing.rs, `the_gate_pairs_as_its_model`).
# Build it with
#
#   bend bridge/bridge_dash.bend -o <out>
#
# and run `<out> <events>`. An events file has one event per line:
#
#   r              a rotation: the next token is current
#   o C T          connection C opens and presents token T (tokens are
#                  numbered as they are made; 0 is the first)
#   m C            connection C opens and presents no token
#   f C            connection C sends a frame (a daemon command)
#
# and it prints one line per event:
#
#   rot            the rotation
#   p C / j C      C paired / was rejected
#   x C            C's frame ran
#   u C            C's frame was refused (C closes)
#   z C            C is not open: the frame reached nothing

import Base
import ../bend/dash.bend as Da

# Reading
# -------

def tok.nat(s: String) -> Nat:
  Maybe.default(&2, Nat, Nat.read(s), 0n)

def tok.at(ws: List<&2, String>, k: Nat) -> String:
  Maybe.default(&2, String, List.get(&2, String, ws, k), "")

def arg(+ws: List<&2, String>, k: Nat) -> Nat:
  tok.nat(tok.at(ws, k))

# one line; h is its first word, ws all its words. Events are kept
# newest first.
def line(h: String, +ws: List<&2, String>, evs: List<&2, Da.Ev>) -> List<&2, Da.Ev>:
  match h:
    case SCon{'r', r}:
      Da.Rotate{} <> evs
    case SCon{'o', r}:
      Da.Open{arg(ws, 1n), Some{arg(ws, 2n)}} <> evs
    case SCon{'m', r}:
      Da.Open{arg(ws, 1n), None{}} <> evs
    case SCon{'f', r}:
      Da.Frame{arg(ws, 1n)} <> evs
    case r:
      evs

def setup(ls: List<&2, String>, evs: List<&2, Da.Ev>) -> List<&2, Da.Ev>:
  match ls:
    case Nil{}:
      evs
    case l <> rest:
      +ws = String.split(l, ' ')
      setup(rest, line(tok.at(ws, 0n), ws, evs))

# Writing
# -------

def show.one(o: Da.Out) -> String:
  match o:
    case Da.Rotated{}:
      "rot\n"
    case Da.Paired{c}:
      String.concat(["p ", Nat.show(c), "\n"])
    case Da.Rejected{c}:
      String.concat(["j ", Nat.show(c), "\n"])
    case Da.Ran{c}:
      String.concat(["x ", Nat.show(c), "\n"])
    case Da.Refused{c}:
      String.concat(["u ", Nat.show(c), "\n"])
    case Da.Closed{c}:
      String.concat(["z ", Nat.show(c), "\n"])

def show.all(os: List<&2, Da.Out>) -> String:
  match os:
    case Nil{}:
      ""
    case o <> rest:
      String.append(show.one(o), show.all(rest))

def go(text: String) -> String:
  show.all(Da.run(List.reverse(&2, Da.Ev, setup(String.lines(text), Nil{})), Da.init()))

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
      IO.die(String, 2, "usage: bridge_dash <events>")
    case prog <> rest:
      match rest:
        case Nil{}:
          IO.die(String, 2, "usage: bridge_dash <events>")
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
