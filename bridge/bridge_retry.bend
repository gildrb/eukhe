# bridge_retry: runs the idle model (bend/retry.bend `idle`) on an events
# file and prints what it decided, line for line as the Rust bridge test
# (crates/eukhe-durable/src/harness/generation/retry_bridge.rs) prints
# the real timer loop of `StreamIdle::within` on paused tokio. What stays
# here is the interleaving only: every decision of the loop (armed, stall
# or sleep at each fire) runs as the compiled model
# (bend/ffi_retry_idle.bend, laws/retry_idle.bend, whose idle_wake_refines
# ties the loop of those decisions to `idle`); the bridge checks that
# tokio's timer, the provider events' stores and the select's order give
# that loop. The classifier, the wait, the failover walk and the stall run
# as bend/ffi_retry.bend, the deferred job as bend/run/decision.bend
# (bend/ffi_run.bend). Build it with
#
#   bend bridge/bridge_retry.bend -o <out>
#
# and run `<out> <events>`. An events file has one case per line:
#
#   i D G ...            the idle deadline: the deadline, then the gaps
#                        (ms) of the stream's events, each after the one
#                        before (the first after the deadline is armed);
#                        the last event ends the stream, and a stream
#                        with no event never ends by itself
#
# Then it prints, one line per case:
#
#   i stalled T | i done the stream stalled T ms after the deadline was
#                        armed, or its provider ended it

import Base
import ../bend/retry.bend as R

# Reading
# -------

def tok.nat(s: String) -> Nat:
  Maybe.default(&2, Nat, Nat.read(s), 0n)

def tok.at(ws: List<&2, String>, k: Nat) -> String:
  Maybe.default(&2, String, List.get(&2, String, ws, k), "")

def arg(+ws: List<&2, String>, k: Nat) -> Nat:
  tok.nat(tok.at(ws, k))

# the words after the first k
def after(ws: List<&2, String>, k: Nat) -> List<&2, String>:
  List.drop(&2, String, ws, k)

def nats(ws: List<&2, String>) -> List<&2, Nat>:
  match ws:
    case Nil{}:
      Nil{}
    case w <> rest:
      tok.nat(w) <> nats(rest)

# Writing
# -------

def show.idle(i: R.Idle) -> String:
  match i:
    case R.IdleStall{at}:
      String.concat(["i stalled ", Nat.show(at), "\n"])
    case R.IdleClose{at}:
      "i done\n"

# one case; h is its first word, ws all its words
def line(h: String, +ws: List<&2, String>) -> String:
  match h:
    case SCon{'i', r}:
      show.idle(R.idle(nats(after(ws, 2n)), arg(ws, 1n)))
    case r:
      ""

def go(ls: List<&2, String>) -> String:
  match ls:
    case Nil{}:
      ""
    case l <> rest:
      +ws = String.split(l, ' ')
      String.concat([line(tok.at(ws, 0n), ws), go(rest)])

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
      IO.die(String, 2, "usage: bridge_retry <events>")
    case prog <> rest:
      match rest:
        case Nil{}:
          IO.die(String, 2, "usage: bridge_retry <events>")
        case path <> more:
          do IO<String>:
            f : File <- IO.try(File, File.open(path, "r"))
            m : File & Result<&1, &1, U32 & String, String> <- File.read(f, 1073741824)
            read.file(m)

def main() -> IO(Unit):
  do IO<Unit>:
    args : List<String> <- IO.args()
    text : String <- scenario(args)
    IO.write(go(String.lines(text)))
