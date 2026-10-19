# bridge_launcher: runs the model of a daemon replacement
# (bend/launcher.bend) on an events file and prints what it did, line for
# line as the Rust bridge test prints `work_gate::WorkGate`,
# `work_gate::idle_shutdown_commits` and `adoption::adoption_verdict`
# (crates/eukhe-daemon/src/supervision_bridge.rs,
# `the_replacement_runs_as_its_model`). Build it with
#
#   bend bend/bridge_launcher.bend -o <out>
#
# and run `<out> <events>`. An events file has one event per line:
#
#   w B B ...      the workers, each with a run (1) or not (0), gates open
#   p I | f I      a prompt to worker I | worker I's run ends
#   q I | r I      the supervisor quiesces | releases worker I
#   c              the supervisor commits the idle shutdown
#   a S W          adoption: a supervisor of build S, a worker of build W
#                  (`-` for a worker that reports no build)
#
# Then it prints, after each worker operation,
#
#   o R G S A      the runs (R) and the closed gates (G) as bits, whether
#                  the daemon stopped (S) and the runs aborted (A)
#
# and for each adoption `a adopt` or `a replace`.

import Base
import ./launcher.bend as La

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

def yes(n: Nat) -> Bool:
  match n:
    case 0n:
      False{}
    case 1n+m:
      True{}

def flags.go(ws: List<&2, String>) -> List<&2, Bool>:
  match ws:
    case Nil{}:
      Nil{}
    case w <> rest:
      yes(tok.nat(w)) <> flags.go(rest)

# the words after the first, as flags
def flags(ws: List<&2, String>) -> List<&2, Bool>:
  match ws:
    case Nil{}:
      Nil{}
    case w <> rest:
      flags.go(rest)

def show.runs(ws: List<&2, La.Wk>) -> String:
  match ws:
    case Nil{}:
      ""
    case w <> t:
      match w:
        case La.Wk{b, c}:
          String.append(bit(b), show.runs(t))

def show.gates(ws: List<&2, La.Wk>) -> String:
  match ws:
    case Nil{}:
      ""
    case w <> t:
      match w:
        case La.Wk{b, c}:
          String.append(bit(c), show.gates(t))

def show.st(s: La.St) -> String:
  match s:
    case La.St{+ws, a, d}:
      String.concat(["o ", show.runs(ws), " ", show.gates(ws), " ", bit(d), " ", Nat.show(a), "\n"])

def build.of(w: String) -> Maybe<&2, Nat>:
  match w:
    case SCon{'-', r}:
      None{}
    case r:
      Some{tok.nat(r)}

def show.adoption(a: La.Adoption) -> String:
  match a:
    case La.Adopt{}:
      "a adopt\n"
    case La.Replace{}:
      "a replace\n"

# the state and the transcript
type Run is Data:
  Run{s: La.St, out: String}

def op.then(+s: La.St, out: String) -> Run:
  Run{s, String.append(out, show.st(s))}

def line(r: Run, h: String, +ws: List<&2, String>) -> Run:
  match r:
    case Run{s, out}:
      match h:
        case SCon{'w', x}:
          Run{La.St{La.open(flags(ws)), 0n, False{}}, out}
        case SCon{'p', x}:
          op.then(La.step(s, La.Prompt{arg(ws, 1n)}), out)
        case SCon{'f', x}:
          op.then(La.step(s, La.Finish{arg(ws, 1n)}), out)
        case SCon{'q', x}:
          op.then(La.step(s, La.Quiesce{arg(ws, 1n)}), out)
        case SCon{'r', x}:
          op.then(La.step(s, La.Release{arg(ws, 1n)}), out)
        case SCon{'c', x}:
          op.then(La.step(s, La.Commit{}), out)
        case SCon{'a', x}:
          Run{s, String.append(out, show.adoption(La.adoption(arg(ws, 1n), build.of(tok.at(ws, 2n)))))}
        case x:
          Run{s, out}

def go(ls: List<&2, String>, r: Run) -> String:
  match ls:
    case Nil{}:
      match r:
        case Run{s, out}:
          out
    case l <> rest:
      +ws = String.split(l, ' ')
      go(rest, line(r, tok.at(ws, 0n), ws))

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
      IO.die(String, 2, "usage: bridge_launcher <events>")
    case prog <> rest:
      match rest:
        case Nil{}:
          IO.die(String, 2, "usage: bridge_launcher <events>")
        case path <> more:
          do IO<String>:
            f : File <- IO.try(File, File.open(path, "r"))
            m : File & Result<&1, &1, U32 & String, String> <- File.read(f, 1073741824)
            read.file(m)

def main() -> IO(Unit):
  do IO<Unit>:
    args : List<String> <- IO.args()
    text : String <- scenario(args)
    IO.write(go(String.lines(text), Run{La.St{Nil{}, 0n, False{}}, ""}))
