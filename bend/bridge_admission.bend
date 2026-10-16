# bridge_admission: runs the admission model on a scenario file and
# prints what it did, line for line as the Rust bridge test
# (crates/eukhe-core/src/admission/bridge.rs) prints the Rust controller.
# Build it with
#
#   bend bend/bridge_admission.bend -o <out>
#
# and run `<out> <scenario>`. A scenario has one op per line; a limit of
# 0 is unlimited, a class 0 interactive and 1 background:
#
#   9 limit queue   a new controller (tickets count from 0 again)
#   0 class         admit a request
#   1 k             ticket k's waiter polls
#   2 k             ticket k's permit drops
#   3 k             ticket k's waiter drops
#   4 limit queue   set the limits
#
# After each op it prints `<r> n=<snapshot> iq=<tickets> b=<tickets>
# bq=<tickets> g=<tickets> x=<tickets>`: r is the admit's outcome (g
# granted, q queued, r rejected) or the poll's (1 ready, 0 pending), else
# `-`; the snapshot is the interactive slots held, interactive waiters,
# background slots held, background waiters; then the interactive queue,
# the background slots held, the background queue, the granted waiters
# not collected yet and the preempted permits not dropped yet.

import Base
import ./admission.bend as A

# Reading
# -------

def tok.nat(s: String) -> Nat:
  Maybe.default(&2, Nat, Nat.read(s), 0n)

def tok.at(ws: List<&2, String>, k: Nat) -> String:
  Maybe.default(&2, String, List.get(&2, String, ws, k), "")

def tok.cls(n: Nat) -> A.Cls:
  match n:
    case 0n:
      A.Ia{}
    case 1n+p:
      A.Bg{}

def tok.lim(n: Nat) -> A.Lim:
  match n:
    case 0n:
      A.Unl{}
    case 1n+p:
      A.Cap{p}

# Writing
# -------

# which tickets a list shows
type Sel is Data:
  SIq{}
  SB{}
  SBq{}
  SG{}
  SX{}

def sel(s: Sel, t: A.Tk) -> Bool:
  match s t:
    case SIq{} A.Tk{A.Ia{}, A.Queued{}}:
      True{}
    case SB{} A.Tk{A.Bg{}, A.Granted{}}:
      True{}
    case SB{} A.Tk{A.Bg{}, A.Held{}}:
      True{}
    case SBq{} A.Tk{A.Bg{}, A.Queued{}}:
      True{}
    case SG{} A.Tk{c, A.Granted{}}:
      True{}
    case SX{} A.Tk{c, A.Preempted{}}:
      True{}
    case _ _:
      False{}

def show.put(b: Bool, +k: Nat, rest: List<&2, String>) -> List<&2, String>:
  match b:
    case True{}:
      Nat.show(k) <> rest
    case False{}:
      rest

def show.go(ts: List<&2, A.Tk>, +s: Sel, +k: Nat) -> List<&2, String>:
  match ts:
    case Nil{}:
      Nil{}
    case t <> r:
      show.put(sel(s, t), k, show.go(r, s, 1n+k))

def show.sel(+ts: List<&2, A.Tk>, s: Sel) -> String:
  String.join(show.go(ts, s, 0n), ",")

def show.state(+s: A.St) -> String:
  +ts = A.St.ts(s)
  String.concat([" n=", Nat.show(A.cnt(A.Holding{}, A.Ia{}, ts)), ",", Nat.show(A.cnt(A.Waiting{}, A.Ia{}, ts)), ",", Nat.show(A.cnt(A.Holding{}, A.Bg{}, ts)), ",", Nat.show(A.cnt(A.Waiting{}, A.Bg{}, ts)), " iq=", show.sel(ts, SIq{}), " b=", show.sel(ts, SB{}), " bq=", show.sel(ts, SBq{}), " g=", show.sel(ts, SG{}), " x=", show.sel(ts, SX{}), "\n"])

# an admit's outcome: the new ticket's status
def show.admit(m: Maybe<&2, A.Tk>) -> String:
  match m:
    case Some{A.Tk{c, A.Held{}}}:
      "g"
    case Some{A.Tk{c, A.Queued{}}}:
      "q"
    case _:
      "r"

# a poll's outcome: the ticket was granted
def show.collect(m: Maybe<&2, A.Tk>) -> String:
  match m:
    case Some{A.Tk{c, A.Granted{}}}:
      "1"
    case _:
      "0"

# what one line did: the controller after it, and its output
type Out is Data:
  Out{s: A.St, text: String}

def Out.s(o: Out) -> A.St:
  match o:
    case Out{s, t}:
      s

def Out.text(o: Out) -> String:
  match o:
    case Out{s, t}:
      t

def out(r: String, +s: A.St) -> Out:
  Out{s, String.append(r, show.state(s))}

# Running
# -------

def apply(k: Nat, +ws: List<&2, String>, +s: A.St) -> Out:
  match k:
    case 0n:
      +s2 = A.step(s, A.Admit{tok.cls(tok.nat(tok.at(ws, 1n)))})
      out(show.admit(List.last(&2, A.Tk, A.St.ts(s2))), s2)
    case 1n:
      +t = tok.nat(tok.at(ws, 1n))
      out(show.collect(A.status(s, t)), A.step(s, A.Collect{t}))
    case 2n:
      out("-", A.step(s, A.Release{tok.nat(tok.at(ws, 1n))}))
    case 3n:
      out("-", A.step(s, A.Leave{tok.nat(tok.at(ws, 1n))}))
    case 4n:
      out("-", A.step(s, A.Limit{tok.lim(tok.nat(tok.at(ws, 1n))), tok.nat(tok.at(ws, 2n))}))
    case 9n:
      Out{A.St.new(tok.lim(tok.nat(tok.at(ws, 1n))), tok.nat(tok.at(ws, 2n))), String.concat(["new ", tok.at(ws, 1n), " ", tok.at(ws, 2n), "\n"])}
    case _:
      Out{s, ""}

# the output of each line of the scenario
def go(ls: List<&2, String>, +s: A.St) -> String:
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
      IO.die(String, 2, "usage: bridge_admission <scenario>")
    case prog <> rest:
      match rest:
        case Nil{}:
          IO.die(String, 2, "usage: bridge_admission <scenario>")
        case path <> more:
          do IO<String>:
            f : File <- IO.try(File, File.open(path, "r"))
            m : File & Result<&1, &1, U32 & String, String> <- File.read(f, 1073741824)
            read.file(m)

def main() -> IO(Unit):
  do IO<Unit>:
    args : List<String> <- IO.args()
    text : String <- scenario(args)
    IO.write(go(String.lines(text), A.St.new(A.Unl{}, 0n)))
