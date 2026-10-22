# bridge_retry: runs the model of the retry decisions (bend/retry.bend) on
# an events file and prints what it decided, line for line as the Rust
# bridge test prints the Rust code
# (crates/eukhe-durable/src/harness/generation/retry_bridge.rs for the d
# and i lines; the classifier, the wait, the failover walk and the stall
# run as the compiled model, bend/ffi_retry.bend). Build it with
#
#   bend bend/bridge_retry.bend -o <out>
#
# and run `<out> <events>`. An events file has one case per line; `-` is
# "none":
#
#   d F B G ...          the deferred job: fetch failures allowed, the
#                        time budget, then the replies, each `a` (the end
#                        of the turn), `lG` (still deferred; the next
#                        reply G+1 ms later) or `bR:G` (failed, R 1 when
#                        retryable; the next reply G+1 ms later)
#   i D G ...            the idle deadline: the deadline, then the gaps
#                        (ms) of the stream's events, each after the one
#                        before (the first after the deadline is armed);
#                        the last event ends the stream, and a stream
#                        with no event never ends by itself
#
# Then it prints, one line per case:
#
#   d ACT ACT ...        per reply: send, poll, cancel, settle or quit
#   i stalled T | i done the stream stalled T ms after the deadline was
#                        armed, or its provider ended it

import Base
import ./retry.bend as R

# Reading
# -------

def tok.nat(s: String) -> Nat:
  Maybe.default(&2, Nat, Nat.read(s), 0n)

def tok.at(ws: List<&2, String>, k: Nat) -> String:
  Maybe.default(&2, String, List.get(&2, String, ws, k), "")

def arg(+ws: List<&2, String>, k: Nat) -> Nat:
  tok.nat(tok.at(ws, k))

def flag(n: Nat) -> Bool:
  match n:
    case 0n:
      False{}
    case 1n+m:
      True{}

# the words after the first k
def after(ws: List<&2, String>, k: Nat) -> List<&2, String>:
  List.drop(&2, String, ws, k)

def got.broke(+parts: List<&2, String>) -> R.Got:
  R.Broke{flag(tok.nat(tok.at(parts, 0n))), tok.nat(tok.at(parts, 1n))}

def got.of(w: String) -> R.Got:
  match w:
    case SCon{'l', rest}:
      R.Later{tok.nat(rest)}
    case SCon{'b', rest}:
      got.broke(String.split(rest, ':'))
    case other:
      R.Answer{}

def nats(ws: List<&2, String>) -> List<&2, Nat>:
  match ws:
    case Nil{}:
      Nil{}
    case w <> rest:
      tok.nat(w) <> nats(rest)

def gots(ws: List<&2, String>) -> List<&2, R.Got>:
  match ws:
    case Nil{}:
      Nil{}
    case w <> rest:
      got.of(w) <> gots(rest)

# Writing
# -------

def show.act(a: R.Act) -> String:
  match a:
    case R.Send{}:
      "send"
    case R.Poll{}:
      "poll"
    case R.Cancel{}:
      "cancel"
    case R.Settle{}:
      "settle"
    case R.Quit{}:
      "quit"

def show.idle(i: R.Idle) -> String:
  match i:
    case R.IdleStall{at}:
      String.concat(["i stalled ", Nat.show(at), "\n"])
    case R.IdleClose{at}:
      "i done\n"

def acts(gs: List<&2, R.Got>, +fails: Nat, +budget: Nat, +job: R.Job) -> String:
  match gs:
    case Nil{}:
      ""
    case g <> rest:
      +st = R.step(fails, budget, job, g)
      String.concat([" ", show.act(R.Step.act(st)), acts(rest, fails, budget, R.Step.job(st))])

# one case; h is its first word, ws all its words
def line(h: String, +ws: List<&2, String>) -> String:
  match h:
    case SCon{'d', r}:
      String.concat(["d", acts(gots(after(ws, 3n)), arg(ws, 1n), arg(ws, 2n), R.NoJob{}), "\n"])
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
