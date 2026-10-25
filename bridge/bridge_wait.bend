# bridge_wait: runs the wait model (wait.bend) on a scenario file and
# prints what it did, line for line as the Rust bridge test prints the
# race (crates/eukhe-core/src/memory/service/race/bridge.rs). Each poll's
# end is the compiled core's (bend/ffi_wait.bend); the bridge checks the
# interleaving: how tokio's wakeups make up the polls. Build it with
#
#   bend bridge/bridge_wait.bend -o <out>
#
# and run `<out> <scenario>`. A scenario starts with `w <d>` (a deadline
# of d ticks) or `w -` (none), then one signal per line: `a` the event,
# `t` a tick, `c` the cancel. It prints `<i> <end>` for each end, i the
# signal's line (0: before any signal), end `arrived`, `expired` or
# `cancelled`.

import Base
import ../bend/wait.bend as W

def tok.at(ws: List<&2, String>, k: Nat) -> String:
  Maybe.default(&2, String, List.get(&2, String, ws, k), "")

def tok.head(s: String) -> Char:
  match s:
    case SNil{}:
      ' '
    case SCon{c, t}:
      c

# The wait
# --------

def wait.name(e: W.End) -> String:
  match e:
    case W.Arrived{}:
      "arrived"
    case W.Expired{}:
      "expired"
    case W.Cancelled{}:
      "cancelled"

def wait.show(+i: Nat, es: List<&2, W.End>) -> String:
  match es:
    case Nil{}:
      ""
    case e <> rest:
      String.concat([Nat.show(i), " ", wait.name(e), "\n", wait.show(i, rest)])

def wait.sig.of(arrive: Bool, cancel: Bool) -> W.Sig:
  match arrive:
    case True{}:
      W.Arrive{}
    case False{}:
      match cancel:
        case True{}:
          W.Cancel{}
        case False{}:
          W.Tick{}

def wait.sig(+c: Char) -> W.Sig:
  wait.sig.of(Char.is_eq(c, 'a'), Char.is_eq(c, 'c'))

def wait.go(ls: List<&2, String>, +i: Nat, +w: W.W) -> String:
  match ls:
    case Nil{}:
      ""
    case l <> rest:
      +s = wait.sig(tok.head(l))
      String.append(wait.show(i, W.out(w, s)), wait.go(rest, 1n+i, W.next(w, s)))

# the deadline, and the state the wait starts in
def wait.start(d: Maybe<&2, Nat>) -> W.W:
  match d:
    case None{}:
      W.Open{None{}}
    case Some{n}:
      match n:
        case 0n:
          W.Over{}
        case 1n+m:
          W.Open{Some{m}}

def wait.first(d: Maybe<&2, Nat>) -> String:
  match d:
    case None{}:
      ""
    case Some{n}:
      match n:
        case 0n:
          "0 expired\n"
        case 1n+m:
          ""

# Running
# -------

def run.wait(+d: Maybe<&2, Nat>, rest: List<&2, String>) -> String:
  String.append(wait.first(d), wait.go(rest, 1n, wait.start(d)))

def run(ls: List<&2, String>) -> String:
  match ls:
    case Nil{}:
      ""
    case l <> rest:
      +ws = String.split(l, ' ')
      run.wait(Nat.read(tok.at(ws, 1n)), rest)

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
      IO.die(String, 2, "usage: bridge_wait <scenario>")
    case prog <> rest:
      match rest:
        case Nil{}:
          IO.die(String, 2, "usage: bridge_wait <scenario>")
        case path <> more:
          do IO<String>:
            f : File <- IO.try(File, File.open(path, "r"))
            m : File & Result<&1, &1, U32 & String, String> <- File.read(f, 1073741824)
            read.file(m)

def main() -> IO(Unit):
  do IO<Unit>:
    args : List<String> <- IO.args()
    text : String <- scenario(args)
    IO.write(run(String.lines(text)))
