# bridge_workflow: runs the dynamic workflow model (bend/workflow.bend)
# on an events file and prints what it did, line for line as the Rust
# bridge test prints the Rust code
# (crates/eukhe-core/src/durable/workflow/bridge.rs: `effective_limits`
# and `admit`). Build it with
#
#   bend bend/bridge_workflow.bend -o <out>
#
# and run `<out> <events>`. An events file has one event per line:
#
#   l S C    the limits of size S (0 small, 1 medium, 2 large) under a
#            subagent cap C (0: unlimited)
#   b M      a run starts with a budget of M agents
#   c K      the run resumes an earlier one that finished key K
#   g K      an agent call with key K
#
# It prints, for an `l` line, `l <concurrency> <max agents>`, and for a
# `g` line `g cached`, `g spawn` or `g refused`.

import Base
import ./workflow.bend as W

def tok.nat(s: String) -> Nat:
  Maybe.default(&2, Nat, Nat.read(s), 0n)

def tok.at(ws: List<&2, String>, k: Nat) -> String:
  Maybe.default(&2, String, List.get(&2, String, ws, k), "")

def arg(+ws: List<&2, String>, k: Nat) -> Nat:
  tok.nat(tok.at(ws, k))

# The size table: (concurrency, max agents).
def limits(s: Nat) -> W.Limits:
  match s:
    case 0n:
      W.Limits{3n, 5n}
    case 1n+a:
      match a:
        case 0n:
          W.Limits{6n, 10n}
        case 1n+b:
          W.Limits{12n, 25n}

def show.limits(l: W.Limits) -> String:
  match l:
    case W.Limits{c, m}:
      String.concat(["l ", Nat.show(c), " ", Nat.show(m), "\n"])

def show.call(c: W.Admit) -> String:
  match c:
    case W.Ended{}:
      "g ended\n"
    case W.Reattach{}:
      "g spawn\n"
    case W.Reuse{i}:
      "g cached\n"
    case W.Spawn{}:
      "g spawn\n"
    case W.Refused{}:
      "g refused\n"

type St is Data:
  St{pool: W.Pool, cache: List<&2, W.Row>, out: List<&2, String>}

def called(r: W.Admit & W.Pool, cache: List<&2, W.Row>, out: List<&2, String>) -> St:
  (c, p) = r
  St{p, cache, show.call(c) <> out}

def line(h: String, +ws: List<&2, String>, s: St) -> St:
  match h:
    case SCon{'l', r}:
      match s:
        case St{p, cache, out}:
          St{p, cache, show.limits(W.effective(limits(arg(ws, 1n)), arg(ws, 2n))) <> out}
    case SCon{'b', r}:
      match s:
        case St{p, cache, out}:
          St{W.pool(arg(ws, 1n)), Nil{}, out}
    case SCon{'c', r}:
      match s:
        case St{p, cache, out}:
          St{p, List.append(&2, W.Row, cache, [W.Row{arg(ws, 1n), W.Finished{}}]), out}
    case SCon{'g', r}:
      match s:
        case St{p, +cache, out}:
          called(W.admit(None{}, arg(ws, 1n), cache, p), cache, out)
    case r:
      s

def lines(ls: List<&2, String>, s: St) -> St:
  match ls:
    case Nil{}:
      s
    case l <> rest:
      +ws = String.split(l, ' ')
      lines(rest, line(tok.at(ws, 0n), ws, s))

def show(s: St) -> String:
  match s:
    case St{p, cache, out}:
      String.concat(List.reverse(&2, String, out))

def go(text: String) -> String:
  show(lines(String.lines(text), St{W.pool(0n), Nil{}, Nil{}}))

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
      IO.die(String, 2, "usage: bridge_workflow <events>")
    case prog <> rest:
      match rest:
        case Nil{}:
          IO.die(String, 2, "usage: bridge_workflow <events>")
        case path <> more:
          do IO<String>:
            f : File <- IO.try(File, File.open(path, "r"))
            m : File & Result<&1, &1, U32 & String, String> <- File.read(f, 1073741824)
            read.file(m)

def main() -> IO(Unit):
  do IO<Unit>:
    args : List<String> <- IO.args()
    text : String <- scenario(args)
    IO.write(go(text))
