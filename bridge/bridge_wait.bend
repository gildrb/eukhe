# bridge_wait: runs the wait model (wait.bend) or the lease model
# (lease.bend) on a scenario file and prints what it did, line for line as
# the Rust bridge test prints the Rust code
# (crates/eukhe-core/src/memory/service/turn/bridge.rs). Build it with
#
#   bend bridge/bridge_wait.bend -o <out>
#
# and run `<out> <scenario>`. A wait scenario starts with `w <d>` (a
# deadline of d ticks) or `w -` (none), then one signal per line: `a` the
# event, `t` a tick, `c` the cancel. It prints `<i> <end>` for each end,
# i the signal's line (0: before any signal), end `arrived`, `expired` or
# `cancelled`.
#
# A lease scenario starts with `l`, then one event per line: `a <origin>`
# (an ask), `r <key>` (a release), `s <key>` (a stop), `c <origin>` (a
# crash). After each event it prints `h=<holder key or -> q=<waiter keys>`,
# a dead waiter's key followed by `!`.

import Base
import ../bend/wait.bend as W
import ../bend/lease.bend as L

def tok.at(ws: List<&2, String>, k: Nat) -> String:
  Maybe.default(&2, String, List.get(&2, String, ws, k), "")

def tok.nat(s: String) -> Nat:
  Maybe.default(&2, Nat, Nat.read(s), 0n)

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

# The lease
# ---------

def lease.waiter(w: L.Waiter) -> String:
  match w:
    case L.Waiter{k, o, l}:
      match l:
        case True{}:
          Nat.show(k)
        case False{}:
          String.append(Nat.show(k), "!")

def lease.queue(q: List<&2, L.Waiter>) -> String:
  match q:
    case Nil{}:
      ""
    case w <> t:
      match t:
        case Nil{}:
          lease.waiter(w)
        case h <> r:
          String.concat([lease.waiter(w), ",", lease.queue(h <> r)])

def lease.holder(h: Maybe<&2, L.Lease>) -> String:
  match h:
    case None{}:
      "-"
    case Some{x}:
      match x:
        case L.Lease{k, o}:
          Nat.show(k)

def lease.show(s: L.L) -> String:
  match s:
    case L.L{n, h, q}:
      String.concat(["h=", lease.holder(h), " q=", lease.queue(q), "\n"])

def lease.ev.of(ask: Bool, release: Bool, stop: Bool, n: Nat) -> L.Ev:
  match ask:
    case True{}:
      L.Ask{n}
    case False{}:
      match release:
        case True{}:
          L.Release{n}
        case False{}:
          match stop:
            case True{}:
              L.Stop{n}
            case False{}:
              L.Crash{n}

def lease.ev(+c: Char, n: Nat) -> L.Ev:
  lease.ev.of(Char.is_eq(c, 'a'), Char.is_eq(c, 'r'), Char.is_eq(c, 's'), n)

def lease.go(ls: List<&2, String>, +s: L.L) -> String:
  match ls:
    case Nil{}:
      ""
    case l <> rest:
      +ws = String.split(l, ' ')
      +next = L.step(s, lease.ev(tok.head(tok.at(ws, 0n)), tok.nat(tok.at(ws, 1n))))
      String.append(lease.show(next), lease.go(rest, next))

# Running
# -------

def run.kind(wait: Bool, +d: Maybe<&2, Nat>, rest: List<&2, String>) -> String:
  match wait:
    case True{}:
      String.append(wait.first(d), wait.go(rest, 1n, wait.start(d)))
    case False{}:
      lease.go(rest, L.L.empty())

def run(ls: List<&2, String>) -> String:
  match ls:
    case Nil{}:
      ""
    case l <> rest:
      +ws = String.split(l, ' ')
      run.kind(Char.is_eq(tok.head(tok.at(ws, 0n)), 'w'), Nat.read(tok.at(ws, 1n)), rest)

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
