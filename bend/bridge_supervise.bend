# bridge_supervise: runs the model of the restart budget and of the
# timeouts (bend/supervise.bend) on an events file and prints what it did,
# line for line as the Rust bridge test prints `RestartBudget` and the
# constants (crates/eukhe-daemon/src/supervision_bridge.rs,
# `the_supervisor_runs_as_its_model`). Build it with
#
#   bend bend/bridge_supervise.bend -o <out>
#
# and run `<out> <events>`. An events file has one event per line:
#
#   c K W B M      a restart budget: K failures allowed in a window of W,
#                  first pause B, longest pause M (units of 250 ms)
#   f G            a failure G units after the one before it
#   t V V ...      the timeouts' base values, in the order of Su.Tm (ms)
#
# Then it prints, for each failure until the first give-up,
#
#   r N P          relaunch: N failures in the window, pause P
#   x N            give up: N failures in the window
#
# and for a `t` line
#
#   t TD SG DR LW CK LO MA QH WI   the teardown, stop grace, drain,
#                  launcher wait, child kill, lost window, max age,
#                  quiesce hold and restart window

import Base
import ./supervise.bend as Su

# Reading
# -------

def tok.nat(s: String) -> Nat:
  Maybe.default(&2, Nat, Nat.read(s), 0n)

def tok.at(ws: List<&2, String>, k: Nat) -> String:
  Maybe.default(&2, String, List.get(&2, String, ws, k), "")

def arg(+ws: List<&2, String>, k: Nat) -> Nat:
  tok.nat(tok.at(ws, k))

# Running
# -------

# the budget, its state, whether it gave up, the transcript so far
type St is Data:
  St{cfg: Su.Cfg, s: Su.St, over: Bool, out: String}

def show.verdict(v: Su.Verdict) -> String:
  match v:
    case Su.Relaunch{n, b}:
      String.concat(["r ", Nat.show(n), " ", Nat.show(b), "\n"])
    case Su.GiveUp{n}:
      String.concat(["x ", Nat.show(n), "\n"])

def failure.put(over: Bool, +c: Su.Cfg, s: Su.St, +g: Nat, out: String) -> St:
  match over:
    case True{}:
      St{c, s, True{}, out}
    case False{}:
      +s2 = Su.step(c, s, g)
      +v = Su.verdict(c, Su.St.n(s2))
      St{c, s2, Su.gives_up(v), String.append(out, show.verdict(v))}

def tm.of(+ws: List<&2, String>) -> Su.Tm:
  Su.Tm{arg(ws, 1n), arg(ws, 2n), arg(ws, 3n), arg(ws, 4n), arg(ws, 5n), arg(ws, 6n), arg(ws, 7n), arg(ws, 8n), arg(ws, 9n), arg(ws, 10n), arg(ws, 11n), arg(ws, 12n), arg(ws, 13n), arg(ws, 14n), arg(ws, 15n), arg(ws, 16n), arg(ws, 17n), arg(ws, 18n), arg(ws, 19n)}

def show.tm(+t: Su.Tm) -> String:
  String.concat(["t ", Nat.show(Su.Tm.teardown(t)), " ", Nat.show(Su.Tm.stop_grace(t)), " ", Nat.show(Su.Tm.drain(t)), " ", Nat.show(Su.Tm.launcher_wait(t)), " ", Nat.show(Su.Tm.child_kill(t)), " ", Nat.show(Su.Tm.lost(t)), " ", Nat.show(Su.Tm.max_age(t)), " ", Nat.show(Su.Tm.quiesce_hold(t)), " ", Nat.show(Su.Tm.window(t)), "\n"])

# one line; h is its first word, ws all its words
def line(st: St, h: String, +ws: List<&2, String>) -> St:
  match st:
    case St{c, s, over, out}:
      match h:
        case SCon{'c', r}:
          St{Su.Cfg{arg(ws, 1n), arg(ws, 2n), arg(ws, 3n), arg(ws, 4n)}, Su.St.empty(), False{}, out}
        case SCon{'f', r}:
          failure.put(over, c, s, arg(ws, 1n), out)
        case SCon{'t', r}:
          St{c, s, over, String.append(out, show.tm(tm.of(ws)))}
        case r:
          St{c, s, over, out}

def go(ls: List<&2, String>, st: St) -> String:
  match ls:
    case Nil{}:
      match st:
        case St{c, s, over, out}:
          out
    case l <> rest:
      +ws = String.split(l, ' ')
      go(rest, line(st, tok.at(ws, 0n), ws))

def run(text: String) -> String:
  go(String.lines(text), St{Su.Cfg{0n, 0n, 0n, 0n}, Su.St.empty(), False{}, ""})

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
      IO.die(String, 2, "usage: bridge_supervise <events>")
    case prog <> rest:
      match rest:
        case Nil{}:
          IO.die(String, 2, "usage: bridge_supervise <events>")
        case path <> more:
          do IO<String>:
            f : File <- IO.try(File, File.open(path, "r"))
            m : File & Result<&1, &1, U32 & String, String> <- File.read(f, 1073741824)
            read.file(m)

def main() -> IO(Unit):
  do IO<Unit>:
    args : List<String> <- IO.args()
    text : String <- scenario(args)
    IO.write(run(text))
