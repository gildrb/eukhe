# bridge_report: runs the child task's step (`step` in child.bend) on a
# scenario file and prints the state after each event, line for line as
# the Rust bridge test prints the task's own decisions
# (crates/eukhe-core/src/durable/children/task/bridge.rs). Build it with
#
#   bend bend/bridge_report.bend -o <out>
#
# and run `<out> <scenario>`. A scenario has one event per line:
#
#   0 k t   a task step; in the watch phase, a poll that read the child
#           busy with the new progress token t (k 0), answered without a
#           reply (1), answered with one (2), or failed (3)
#   1 m     the parent's run places submission m
#   2 m     the parent withdraws submission m
#   3       a parent abort
#   4       a parent close
#   5       a reopen
#   6 d     an abort of the task: a cancel (d 0) or a delete (d 1)
#
# After each it prints `<phase> <mark> <open>` and the inbox, newest
# first: phase W (watching), O<report><id> (owing the report, C completed,
# F failed, X cancelled, S stalled, U unreachable, under the id) or E
# (ended); mark - (none), c (cancel) or d (delete); open o or x (closing);
# then ` <id>:<fate>` per submission, fate q (queued), w (withdrawn) or p
# (placed).

import Base
import ./child.bend as C

# Reading
# -------

def tok.nat(s: String) -> Nat:
  Maybe.default(&2, Nat, Nat.read(s), 0n)

def tok.at(ws: List<&2, String>, k: Nat) -> String:
  Maybe.default(&2, String, List.get(&2, String, ws, k), "")

# Writing
# -------

def show.report(k: C.Report) -> String:
  match k:
    case C.Completed{}:
      "C"
    case C.Failed{}:
      "F"
    case C.Cancelled{}:
      "X"
    case C.Stalled{}:
      "S"
    case C.Unreachable{}:
      "U"

def show.ph(ph: C.Ph) -> String:
  match ph:
    case C.Watching{w}:
      "W"
    case C.Owing{k, n}:
      "O" ++ show.report(k) ++ Nat.show(n)
    case C.Ended{}:
      "E"

def show.mark(cut: Maybe<&2, Bool>) -> String:
  match cut:
    case None{}:
      "-"
    case Some{d}:
      match d:
        case True{}:
          "d"
        case False{}:
          "c"

def show.open(open: Bool) -> String:
  match open:
    case True{}:
      "o"
    case False{}:
      "x"

def show.fate(f: C.Fate) -> String:
  match f:
    case C.Queued{}:
      "q"
    case C.Withdrawn{}:
      "w"
    case C.Placed{}:
      "p"

def show.inbox(inbox: List<&2, C.Sub>) -> String:
  match inbox:
    case Nil{}:
      ""
    case s <> rest:
      match s:
        case C.Sub{i, f}:
          " " ++ Nat.show(i) ++ ":" ++ show.fate(f) ++ show.inbox(rest)

def show.st(s: C.St) -> String:
  match s:
    case C.St{ph, cut, open, inbox}:
      show.ph(ph) ++ " " ++ show.mark(cut) ++ " " ++ show.open(open) ++ show.inbox(inbox) ++ "\n"

# Running
# -------

def obs(k: Nat, t: Nat) -> C.Obs:
  match k:
    case 0n:
      C.Busy{Some{t}}
    case 1n+p:
      match p:
        case 0n:
          C.Answered{False{}}
        case 1n+q:
          match q:
            case 0n:
              C.Answered{True{}}
            case 1n+r:
              C.Broke{}

# what one line did: the state after it, and its output
type Out is Data:
  Out{s: C.St, text: String}

def Out.s(o: Out) -> C.St:
  match o:
    case Out{s, t}:
      s

def Out.text(o: Out) -> String:
  match o:
    case Out{s, t}:
      t

def out(+s: C.St) -> Out:
  Out{s, show.st(s)}

def apply(k: Nat, +ws: List<&2, String>, +cfg: C.Cfg, +s: C.St) -> Out:
  match k:
    case 0n:
      out(C.step(cfg, s, C.Poll{0n, obs(tok.nat(tok.at(ws, 1n)), tok.nat(tok.at(ws, 2n)))}))
    case 1n:
      out(C.step(cfg, s, C.Deliver{tok.nat(tok.at(ws, 1n))}))
    case 2n:
      out(C.step(cfg, s, C.Withdraw{tok.nat(tok.at(ws, 1n))}))
    case 3n:
      out(C.step(cfg, s, C.Abort{}))
    case 4n:
      out(C.step(cfg, s, C.Shut{}))
    case 5n:
      out(C.step(cfg, s, C.Reopen{}))
    case 6n:
      out(C.step(cfg, s, C.Cut{Nat.is_eq(tok.nat(tok.at(ws, 1n)), 1n)}))
    case _:
      Out{s, ""}

# the output of each line of the scenario
def go(ls: List<&2, String>, +cfg: C.Cfg, +s: C.St) -> String:
  match ls:
    case Nil{}:
      ""
    case l <> rest:
      +ws = String.split(l, ' ')
      +o = apply(Maybe.default(&2, Nat, Nat.read(tok.at(ws, 0n)), 8n), ws, cfg, s)
      String.append(Out.text(o), go(rest, cfg, Out.s(o)))

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
      IO.die(String, 2, "usage: bridge_report <scenario>")
    case prog <> rest:
      match rest:
        case Nil{}:
          IO.die(String, 2, "usage: bridge_report <scenario>")
        case path <> more:
          do IO<String>:
            f : File <- IO.try(File, File.open(path, "r"))
            m : File & Result<&1, &1, U32 & String, String> <- File.read(f, 1073741824)
            read.file(m)

def main() -> IO(Unit):
  do IO<Unit>:
    args : List<String> <- IO.args()
    text : String <- scenario(args)
    IO.write(go(String.lines(text), C.Cfg{100n, 5n}, C.St.init(C.Cfg{100n, 5n})))
