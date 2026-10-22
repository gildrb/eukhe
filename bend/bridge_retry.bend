# bridge_retry: runs the model of the retry decisions (bend/retry.bend) on
# an events file and prints what it decided, line for line as the Rust
# bridge tests print the Rust code
# (crates/eukhe-core/src/durable/models/retry_bridge.rs for the c, w and f
# lines; crates/eukhe-durable/src/harness/generation/retry_bridge.rs for
# the s and i lines). Build it with
#
#   bend bend/bridge_retry.bend -o <out>
#
# and run `<out> <events>`. An events file has one case per line; `-` is
# "none":
#
#   c P L S K T          the classifier: parked, limit (0/1), status,
#                        kind code (0 refusal, 1 safety, 2 payment
#                        required, 3 overloaded, 4 rate limit, 5 server
#                        error, 6 auth, 7 permission, 8 invalid request,
#                        9 malformed response, 10 stream drop, 11 stream
#                        stalled, 12 stream repeating, 13 unknown), text
#                        (0/1)
#   w J S C              the wait: jitter, server wait, cap (0: none)
#   f N M B X A:W ...    the failover walk: chain length, max switches,
#                        base delay, max delay, then the failed attempts,
#                        oldest first, each its chain index and server
#                        wait
#   s I                  the stall: the idle deadline a stream stalled
#                        under
#   i D G ...            the idle deadline: the deadline, then the gaps
#                        (ms) of the stream's events, each after the one
#                        before (the first after the deadline is armed);
#                        the last event ends the stream, and a stream
#                        with no event never ends by itself
#
# Then it prints, one line per case:
#
#   c 1 | c 0            retried or not
#   w after MS | w refused S C
#   f none | f TO D      no switch, or the next provider's index and wait
#   s I                  the retry's idle deadline
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

def opt(+ws: List<&2, String>, k: Nat) -> Maybe<&2, Nat>:
  Nat.read(tok.at(ws, k))

def flag(n: Nat) -> Bool:
  match n:
    case 0n:
      False{}
    case 1n+m:
      True{}

def causes() -> List<&2, R.Cause>:
  [R.Refusal{}, R.Safety{}, R.PaymentRequired{}, R.Overloaded{}, R.RateLimit{}, R.ServerError{}, R.Auth{}, R.Permission{}, R.InvalidRequest{}, R.MalformedResponse{}, R.StreamDrop{}, R.StreamStalled{}, R.StreamRepeating{}, R.Unknown{}]

def cause.of(m: Maybe<&2, Nat>) -> Maybe<&2, R.Cause>:
  match m:
    case None{}:
      None{}
    case Some{n}:
      List.get(&2, R.Cause, causes(), n)

# the words after the first k
def after(ws: List<&2, String>, k: Nat) -> List<&2, String>:
  List.drop(&2, String, ws, k)

def tried.of(w: String) -> R.Tried:
  +parts = String.split(w, ':')
  R.Tried{tok.nat(tok.at(parts, 0n)), Nat.read(tok.at(parts, 1n))}

def trieds(ws: List<&2, String>) -> List<&2, R.Tried>:
  match ws:
    case Nil{}:
      Nil{}
    case w <> rest:
      tried.of(w) <> trieds(rest)

def nats(ws: List<&2, String>) -> List<&2, Nat>:
  match ws:
    case Nil{}:
      Nil{}
    case w <> rest:
      tok.nat(w) <> nats(rest)

# Writing
# -------

def show.bool(b: Bool) -> String:
  match b:
    case True{}:
      "1"
    case False{}:
      "0"

def show.delay(d: R.Delay) -> String:
  match d:
    case R.After{ms}:
      String.concat(["w after ", Nat.show(ms), "\n"])
    case R.Refused{server, cap}:
      String.concat(["w refused ", Nat.show(server), " ", Nat.show(cap), "\n"])

def show.switch(m: Maybe<&2, R.Switch>) -> String:
  match m:
    case None{}:
      "f none\n"
    case Some{s}:
      match s:
        case R.Switch{to, delay}:
          String.concat(["f ", Nat.show(to), " ", Nat.show(delay), "\n"])

def show.idle(i: R.Idle) -> String:
  match i:
    case R.IdleStall{at}:
      String.concat(["i stalled ", Nat.show(at), "\n"])
    case R.IdleClose{at}:
      "i done\n"

# one case; h is its first word, ws all its words
def line(h: String, +ws: List<&2, String>) -> String:
  match h:
    case SCon{'c', r}:
      String.concat(["c ", show.bool(R.retryable({R.Facts{flag(arg(ws, 1n)), flag(arg(ws, 2n)), opt(ws, 3n), cause.of(opt(ws, 4n)), flag(arg(ws, 5n))} : R.Facts})), "\n"])
    case SCon{'w', r}:
      show.delay(R.wait(arg(ws, 1n), opt(ws, 2n), arg(ws, 3n)))
    case SCon{'f', r}:
      show.switch(R.next(arg(ws, 1n), trieds(after(ws, 5n)), R.Policy{arg(ws, 2n), arg(ws, 3n), arg(ws, 4n)}))
    case SCon{'s', r}:
      String.concat(["s ", Nat.show(R.stall.next(arg(ws, 1n))), "\n"])
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
