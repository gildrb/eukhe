# bridge_recover: runs the recoveries of the run model (bend/run.bend,
# Rec) on a scenario file and prints what they did, line for line as the
# Rust bridge test prints the Rust decisions
# (crates/eukhe-durable/src/harness/generation/recover_bridge.rs). Build
# it with
#
#   bend bend/bridge_recover.bend -o <out>
#
# and run `<out> <scenario>`. A scenario has one input per line:
#
#   9 long leak redirect repeat   the caps (first line)
#   v kind h rebuilt kept         a reply (R.Out): kind L a length stop,
#                                 K leaked calls (rebuilt 1: rebuilt into
#                                 calls of hash h), R calls of hash h
#                                 (kept 1: when they run, their results
#                                 are the last round's), N another noted
#                                 reply, S a user message, A an answer, O
#                                 any other reply
#
# After each reply it prints the act, then the recoveries after it:
#
#   <act> <kind> row=<row> same=<same>
#
# act: pass, exec, redo, stand, quit; kind: free, longs, leaks, loops.

import Base
import ./run.bend as R

# Reading
# -------

def tok.nat(s: String) -> Nat:
  Maybe.default(&2, Nat, Nat.read(s), 0n)

def tok.at(ws: List<&2, String>, k: Nat) -> String:
  Maybe.default(&2, String, List.get(&2, String, ws, k), "")

def tok.bool(s: String) -> Bool:
  Nat.is_eq(tok.nat(s), 1n)

def tok.head(s: String) -> Char:
  match s:
    case SNil{}:
      ' '
    case SCon{c, t}:
      c

def out.pick(l: Bool, k: Bool, r: Bool, n: Bool, s: Bool, a: Bool, +ws: List<&2, String>) -> R.Out:
  match l k r n s a:
    case True{} k r n s a:
      R.Long{}
    case False{} True{} r n s a:
      R.Leak{tok.bool(tok.at(ws, 3n)), tok.nat(tok.at(ws, 2n)), tok.bool(tok.at(ws, 4n))}
    case False{} False{} True{} n s a:
      R.Ran{tok.nat(tok.at(ws, 2n)), tok.bool(tok.at(ws, 4n))}
    case False{} False{} False{} True{} s a:
      R.Noted{}
    case False{} False{} False{} False{} True{} a:
      R.Said{}
    case False{} False{} False{} False{} False{} True{}:
      R.Answer{}
    case False{} False{} False{} False{} False{} False{}:
      R.Other{}

def out.of(+k: Char, +ws: List<&2, String>) -> R.Out:
  out.pick(Char.is_eq(k, 'L'), Char.is_eq(k, 'K'), Char.is_eq(k, 'R'), Char.is_eq(k, 'N'), Char.is_eq(k, 'S'), Char.is_eq(k, 'A'), ws)

def caps.of(+ws: List<&2, String>) -> R.RCfg:
  R.RCfg{tok.nat(tok.at(ws, 1n)), tok.nat(tok.at(ws, 2n)), tok.nat(tok.at(ws, 3n)), tok.nat(tok.at(ws, 4n))}

# Writing
# -------

def show.act(a: R.Act) -> String:
  match a:
    case R.Pass{}:
      "pass"
    case R.Exec{}:
      "exec"
    case R.Redo{}:
      "redo"
    case R.Stand{}:
      "stand"
    case R.Quit{}:
      "quit"

def show.kind(k: R.Rk) -> String:
  match k:
    case R.Free{}:
      "free"
    case R.Longs{}:
      "longs"
    case R.Leaks{}:
      "leaks"
    case R.Loops{}:
      "loops"

def show.dec(d: R.Dec) -> String:
  match d:
    case R.Dec{act, r}:
      match r:
        case R.Rec{k, row, same, last}:
          String.concat([show.act(act), " ", show.kind(k), " row=", Nat.show(row), " same=", Nat.show(same), "\n"])

# Running
# -------

# what one line did: the caps, the recoveries after it, and its output
type Out is Data:
  Out{rc: R.RCfg, r: R.Rec, text: String}

def Out.rc(o: Out) -> R.RCfg:
  match o:
    case Out{c, r, x}:
      c

def Out.r(o: Out) -> R.Rec:
  match o:
    case Out{c, r, x}:
      r

def Out.text(o: Out) -> String:
  match o:
    case Out{c, r, x}:
      x

# a line: the caps (`9 ...`), nothing (a blank line), or a reply
def line(config: Bool, blank: Bool, +ws: List<&2, String>, +rc: R.RCfg, +r: R.Rec) -> Out:
  match config blank:
    case True{} blank:
      Out{caps.of(ws), R.Rec.init(), ""}
    case False{} True{}:
      Out{rc, r, ""}
    case False{} False{}:
      +d = R.Rec.step(rc, out.of(tok.head(tok.at(ws, 1n)), ws), r)
      Out{rc, R.Dec.r(d), show.dec(d)}

def go(ls: List<&2, String>, +rc: R.RCfg, +r: R.Rec) -> String:
  match ls:
    case Nil{}:
      ""
    case l <> rest:
      +ws = String.split(l, ' ')
      +k = tok.head(tok.at(ws, 0n))
      +o = line(Char.is_eq(k, '9'), Char.is_eq(k, ' '), ws, rc, r)
      String.append(Out.text(o), go(rest, Out.rc(o), Out.r(o)))

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
      IO.die(String, 2, "usage: bridge_recover <scenario>")
    case prog <> rest:
      match rest:
        case Nil{}:
          IO.die(String, 2, "usage: bridge_recover <scenario>")
        case path <> more:
          do IO<String>:
            f : File <- IO.try(File, File.open(path, "r"))
            m : File & Result<&1, &1, U32 & String, String> <- File.read(f, 1073741824)
            read.file(m)

def main() -> IO(Unit):
  do IO<Unit>:
    args : List<String> <- IO.args()
    text : String <- scenario(args)
    IO.write(go(String.lines(text), R.RCfg{0n, 0n, 0n, 0n}, R.Rec.init()))
