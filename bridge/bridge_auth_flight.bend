# bridge_auth_flight: runs the refresh-flight model on a scenario file and
# prints what it did, line for line as the Rust bridge test
# (crates/eukhe-core/src/auth/flight/bridge.rs) prints the Rust state
# machine. Build it with
#
#   bend bridge/bridge_auth_flight.bend -o <out>
#
# and run `<out> <scenario>`. A scenario has one event per line:
#
#   9       a new world (no caller; the store holds credential 0, expired)
#   0       a caller arrives
#   1 k b   caller k takes its next step; at a fetch, b = 1 succeeds
#   2       a peer stores a fresh credential
#   3       the stored credential expires
#
# After each event it prints `f=<fetches> s=c<n><+|-> c=<legs>`: the
# stored credential (+ fresh, - expired), then each caller's leg, joined
# by commas: L load, B board, C<f> check, F<f> fetch, S<f>:c<n> store,
# N<f>:<out> land, W<f> wait, D:<out> done; an out is c<n> (a credential)
# or e<n> (a failed fetch).

import Base
import ../bend/auth_flight.bend as F

# Reading
# -------

def tok.nat(s: String) -> Nat:
  Maybe.default(&2, Nat, Nat.read(s), 0n)

def tok.at(ws: List<&2, String>, k: Nat) -> String:
  Maybe.default(&2, String, List.get(&2, String, ws, k), "")

def tok.bool(n: Nat) -> Bool:
  match n:
    case 0n:
      False{}
    case 1n+p:
      True{}

# Writing
# -------

def show.out(o: F.Out) -> String:
  match o:
    case F.Ok{c}:
      String.append("c", Nat.show(c))
    case F.Err{e}:
      String.append("e", Nat.show(e))

def show.leg(l: F.Leg) -> String:
  match l:
    case F.Load{}:
      "L"
    case F.Board{}:
      "B"
    case F.Check{f}:
      String.append("C", Nat.show(f))
    case F.Fetch{f}:
      String.append("F", Nat.show(f))
    case F.Store{f, c}:
      String.concat(["S", Nat.show(f), ":c", Nat.show(c)])
    case F.Land{f, o}:
      String.concat(["N", Nat.show(f), ":", show.out(o)])
    case F.Waiting{f}:
      String.append("W", Nat.show(f))
    case F.Served{v, o}:
      String.append("D:", show.out(o))

def show.legs(ls: List<&2, F.Leg>) -> List<&2, String>:
  match ls:
    case Nil{}:
      Nil{}
    case l <> t:
      show.leg(l) <> show.legs(t)

def show.fresh(b: Bool) -> String:
  match b:
    case True{}:
      "+"
    case False{}:
      "-"

def show.state(s: F.St) -> String:
  match s:
    case F.St{w, cs}:
      match w:
        case F.W{sto, fl, ld, n}:
          match sto:
            case F.Sto{c, fresh}:
              String.concat(["f=", Nat.show(n), " s=c", Nat.show(c), show.fresh(fresh), " c=", String.join(show.legs(cs), ","), "\n"])

# what one line did: the state after it, and its output
type Out is Data:
  Out{s: F.St, text: String}

def Out.s(o: Out) -> F.St:
  match o:
    case Out{s, t}:
      s

def Out.text(o: Out) -> String:
  match o:
    case Out{s, t}:
      t

def out(+s: F.St) -> Out:
  Out{s, show.state(s)}

# Running
# -------

def apply(k: Nat, +ws: List<&2, String>, +s: F.St) -> Out:
  match k:
    case 0n:
      out(F.step(s, F.Arrive{}))
    case 1n:
      out(F.step(s, F.Step{tok.nat(tok.at(ws, 1n)), tok.bool(tok.nat(tok.at(ws, 2n)))}))
    case 2n:
      out(F.step(s, F.Peer{}))
    case 3n:
      out(F.step(s, F.Expire{}))
    case 9n:
      Out{F.St.new(), "new\n"}
    case _:
      Out{s, ""}

# the output of each line of the scenario
def go(ls: List<&2, String>, +s: F.St) -> String:
  match ls:
    case Nil{}:
      ""
    case l <> rest:
      +ws = String.split(l, ' ')
      +o = apply(Maybe.default(&2, Nat, Nat.read(tok.at(ws, 0n)), 8n), ws, s)
      String.append(Out.text(o), go(rest, Out.s(o)))

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
      IO.die(String, 2, "usage: bridge_auth_flight <scenario>")
    case prog <> rest:
      match rest:
        case Nil{}:
          IO.die(String, 2, "usage: bridge_auth_flight <scenario>")
        case path <> more:
          do IO<String>:
            f : File <- IO.try(File, File.open(path, "r"))
            m : File & Result<&1, &1, U32 & String, String> <- File.read(f, 1073741824)
            read.file(m)

def main() -> IO(Unit):
  do IO<Unit>:
    args : List<String> <- IO.args()
    text : String <- scenario(args)
    IO.write(go(String.lines(text), F.St.new()))
