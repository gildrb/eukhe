# bridge_progress: runs the work of a session (`work` in progress.bend)
# and the goal's progress check (`check`) on a scenario file and prints
# what they decided, line for line as the Rust bridge test prints the work
# ledger (`WorkLedger`) and `goal_check`
# (crates/eukhe-core/src/durable/goals/hooks/bridge.rs). Build it with
#
#   bend bridge/bridge_progress.bend -o <out>
#
# and run `<out> <scenario>`. A scenario has one event per line:
#
#   9 cap          the settings (first line): the cap of continuations in
#                  a row with no new work; no acts yet, no check yet
#   0 f1 .. fn     a goal continuation after the acts f1 .. fn of the run
#                  since the last one (none, one, or more)
#   1 f1 .. fn     the first continuation of a new run (a new input), after
#                  the acts f1 .. fn: it starts the count
#
# After each continuation it prints `w=<work> G<stalls>` (the goal goes
# on) or `w=<work> S<stalls>` (the goal stops; the next run starts the
# count again).

import Base
import ../bend/progress.bend as P

# Reading
# -------

def tok.nat(s: String) -> Nat:
  Maybe.default(&2, Nat, Nat.read(s), 0n)

def tok.at(ws: List<&2, String>, k: Nat) -> String:
  Maybe.default(&2, String, List.get(&2, String, ws, k), "")

def acts.go(ws: List<&2, String>) -> List<&2, Nat>:
  match ws:
    case Nil{}:
      Nil{}
    case w <> rest:
      tok.nat(w) <> acts.go(rest)

# the acts of a line: every word after the first
def acts(ws: List<&2, String>) -> List<&2, Nat>:
  match ws:
    case Nil{}:
      Nil{}
    case w <> rest:
      acts.go(rest)

# Writing
# -------

def show(+w: Nat, g: P.Goal) -> String:
  match g:
    case P.Go{n}:
      String.concat(["w=", Nat.show(w), " G", Nat.show(n), "\n"])
    case P.Stop{n}:
      String.concat(["w=", Nat.show(w), " S", Nat.show(n), "\n"])

# the count the next continuation starts from
def next(g: P.Goal) -> Nat:
  match g:
    case P.Go{n}:
      n
    case P.Stop{n}:
      0n

# Running
# -------

# what one line did: the cap, the acts so far, the count, and its output
type Out is Data:
  Out{cap: Nat, hist: List<&2, Nat>, s: Nat, text: String}

def Out.cap(o: Out) -> Nat:
  match o:
    case Out{c, h, s, t}:
      c

def Out.hist(o: Out) -> List<&2, Nat>:
  match o:
    case Out{c, h, s, t}:
      h

def Out.s(o: Out) -> Nat:
  match o:
    case Out{c, h, s, t}:
      s

def Out.text(o: Out) -> String:
  match o:
    case Out{c, h, s, t}:
      t

def out.check(+cap: Nat, +now: List<&2, Nat>, +g: P.Goal) -> Out:
  Out{cap, now, next(g), show(P.work(now), g)}

def apply(k: Nat, +ws: List<&2, String>, +cap: Nat, +hist: List<&2, Nat>, +s: Nat) -> Out:
  match k:
    case 0n:
      +seg = acts(ws)
      out.check(cap, List.append(&2, Nat, hist, seg), P.check(cap, s, P.grew(hist, seg)))
    case 1n:
      out.check(cap, List.append(&2, Nat, hist, acts(ws)), P.Go{0n})
    case 9n:
      Out{tok.nat(tok.at(ws, 1n)), Nil{}, 0n, ""}
    case _:
      Out{cap, hist, s, ""}

# the output of each line of the scenario
def go(ls: List<&2, String>, +cap: Nat, +hist: List<&2, Nat>, +s: Nat) -> String:
  match ls:
    case Nil{}:
      ""
    case l <> rest:
      +ws = String.split(l, ' ')
      +o = apply(Maybe.default(&2, Nat, Nat.read(tok.at(ws, 0n)), 8n), ws, cap, hist, s)
      String.append(Out.text(o), go(rest, Out.cap(o), Out.hist(o), Out.s(o)))

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
      IO.die(String, 2, "usage: bridge_progress <scenario>")
    case prog <> rest:
      match rest:
        case Nil{}:
          IO.die(String, 2, "usage: bridge_progress <scenario>")
        case path <> more:
          do IO<String>:
            f : File <- IO.try(File, File.open(path, "r"))
            m : File & Result<&1, &1, U32 & String, String> <- File.read(f, 1073741824)
            read.file(m)

def main() -> IO(Unit):
  do IO<Unit>:
    args : List<String> <- IO.args()
    text : String <- scenario(args)
    IO.write(go(String.lines(text), 1n, Nil{}, 0n))
