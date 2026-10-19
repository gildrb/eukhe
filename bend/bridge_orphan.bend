# bridge_orphan: runs the model of a lost supervisor's worker
# (bend/orphan.bend) on an events file and prints what it did, line for
# line as the Rust bridge test prints `supervisor_lost::exit_due` and
# `work_gate::orphan_exit` (crates/eukhe-daemon/src/supervision_bridge.rs,
# `the_orphan_exit_runs_as_its_model`). Build it with
#
#   bend bend/bridge_orphan.bend -o <out>
#
# and run `<out> <events>`. An events file holds one worker:
#
#   w N            the lost-exit window (ms)
#   s | e          a run starts | ends
#   q | d          an input is queued | drained
#   c | k          a compaction starts | ends
#   g N            the supervisor stays unreachable N ms more
#   b              the supervisor answers again
#
# Then it prints, at the end,
#
#   live           the worker did not exit
#   x H B A        it exited: H shut or handover, B the busy flag it
#                  recorded, A whether it aborted a run (1 or 0)

import Base
import ./orphan.bend as Or

def tok.nat(s: String) -> Nat:
  Maybe.default(&2, Nat, Nat.read(s), 0n)

def tok.at(ws: List<&2, String>, k: Nat) -> String:
  Maybe.default(&2, String, List.get(&2, String, ws, k), "")

def arg(+ws: List<&2, String>, k: Nat) -> Nat:
  tok.nat(tok.at(ws, k))

def bit(b: Bool) -> String:
  match b:
    case True{}:
      "1"
    case False{}:
      "0"

def show.exit(e: Or.Exit) -> String:
  match e:
    case Or.Shut{}:
      "shut"
    case Or.Handover{}:
      "handover"

def show(s: Or.St) -> String:
  match s:
    case Or.Live{w}:
      "live\n"
    case Or.Exited{d}:
      match d:
        case Or.Out{e, work, busy, aborted}:
          String.concat(["x ", show.exit(e), " ", bit(busy), " ", bit(aborted), "\n"])

# the window, then the events
type In is Data:
  In{window: Nat, evs: List<&2, Or.Ev>}

def ev(h: String, +ws: List<&2, String>) -> Maybe<&2, Or.Ev>:
  match h:
    case SCon{'s', r}:
      Some{Or.RunStart{}}
    case SCon{'e', r}:
      Some{Or.RunEnd{}}
    case SCon{'q', r}:
      Some{Or.Queue{}}
    case SCon{'d', r}:
      Some{Or.Drain{}}
    case SCon{'c', r}:
      Some{Or.CompactStart{}}
    case SCon{'k', r}:
      Some{Or.CompactEnd{}}
    case SCon{'g', r}:
      Some{Or.Gone{arg(ws, 1n)}}
    case SCon{'b', r}:
      Some{Or.Back{}}
    case r:
      None{}

def add.ev(m: Maybe<&2, Or.Ev>, evs: List<&2, Or.Ev>) -> List<&2, Or.Ev>:
  match m:
    case None{}:
      evs
    case Some{e}:
      List.append(&2, Or.Ev, evs, [e])

def window.of(h: String, +ws: List<&2, String>, w: Nat) -> Nat:
  match h:
    case SCon{'w', r}:
      arg(ws, 1n)
    case r:
      w

def setup(ls: List<&2, String>, i: In) -> In:
  match ls:
    case Nil{}:
      i
    case l <> rest:
      match i:
        case In{w, evs}:
          +ws = String.split(l, ' ')
          +h = tok.at(ws, 0n)
          setup(rest, In{window.of(h, ws, w), add.ev(ev(h, ws), evs)})

def run(i: In) -> String:
  match i:
    case In{+w, evs}:
      show(Or.run(w, evs))

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
      IO.die(String, 2, "usage: bridge_orphan <events>")
    case prog <> rest:
      match rest:
        case Nil{}:
          IO.die(String, 2, "usage: bridge_orphan <events>")
        case path <> more:
          do IO<String>:
            f : File <- IO.try(File, File.open(path, "r"))
            m : File & Result<&1, &1, U32 & String, String> <- File.read(f, 1073741824)
            read.file(m)

def main() -> IO(Unit):
  do IO<Unit>:
    args : List<String> <- IO.args()
    text : String <- scenario(args)
    IO.write(run(setup(String.lines(text), In{0n, Nil{}})))
