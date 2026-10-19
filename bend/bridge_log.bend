# bridge_log: runs the model of the commit log (bend/log.bend) on an
# events file and prints what it did, line for line as the Rust bridge
# test prints the real `JsonlStorage`
# (crates/eukhe-durable/src/storage/jsonl/bridge.rs,
# `the_commit_log_runs_as_its_model`). Build it with
#
#   bend bend/bridge_log.bend -o <out>
#
# and run `<out> <events>`. The disk starts with no file. An events file
# has one event per line:
#
#   e P K D    a new epoch: P steps before the crash, K bytes not flushed
#              that the crash keeps, D 1 when it drops the directory
#              entries not flushed (0 when not)
#   c S N      a commit of the epoch: sequence S, a line of N bytes (its
#              newline included, N >= 2)
#
# For each epoch it prints
#
#   a S S ...  the sequences of the commits it acknowledged, in order
#   r S S ...  the sequences an open reads after the crash, in order

import Base
import ./log.bend as Lg

# Reading
# -------

def tok.nat(s: String) -> Nat:
  Maybe.default(&2, Nat, Nat.read(s), 0n)

def tok.at(ws: List<&2, String>, k: Nat) -> String:
  Maybe.default(&2, String, List.get(&2, String, ws, k), "")

def arg(+ws: List<&2, String>, k: Nat) -> Nat:
  tok.nat(tok.at(ws, k))

def yes(n: Nat) -> Bool:
  match n:
    case 0n:
      False{}
    case 1n+m:
      True{}

# the content of a commit's line: its sequence, then N - 2 bytes
def content(+s: Nat, n: Nat) -> List<&2, Nat>:
  s <> List.replicate(Nat, Nat.sub(n, 2n), 0n)

# An epoch while it is read: its crash and its commits, newest first
type Ep is Data:
  Ep{p: Nat, k: Nat, drop: Bool, cs: List<&2, List<&2, Nat>>}

def Ep.epoch(e: Ep) -> Lg.Epoch:
  match e:
    case Ep{p, k, drop, cs}:
      Lg.Epoch{List.reverse(&2, List<&2, Nat>, cs), p, k, drop}

def commit(c: List<&2, Nat>, es: List<&2, Ep>) -> List<&2, Ep>:
  match es:
    case Nil{}:
      Nil{}
    case e <> rest:
      match e:
        case Ep{p, k, drop, cs}:
          Ep{p, k, drop, c <> cs} <> rest

# one line; h is its first word, ws all its words. Epochs are kept
# newest first.
def line(h: String, +ws: List<&2, String>, es: List<&2, Ep>) -> List<&2, Ep>:
  match h:
    case SCon{'e', r}:
      Ep{arg(ws, 1n), arg(ws, 2n), yes(arg(ws, 3n)), Nil{}} <> es
    case SCon{'c', r}:
      commit(content(arg(ws, 1n), arg(ws, 2n)), es)
    case r:
      es

def setup(ls: List<&2, String>, es: List<&2, Ep>) -> List<&2, Ep>:
  match ls:
    case Nil{}:
      es
    case l <> rest:
      +ws = String.split(l, ' ')
      setup(rest, line(tok.at(ws, 0n), ws, es))

# Writing
# -------

def show.heads(ls: List<&2, List<&2, Nat>>) -> String:
  match ls:
    case Nil{}:
      ""
    case l <> rest:
      match l:
        case Nil{}:
          String.concat([" ?", show.heads(rest)])
        case s <> more:
          String.concat([" ", Nat.show(s), show.heads(rest)])

def run(es: List<&2, Ep>, +d: Lg.Disk) -> String:
  match es:
    case Nil{}:
      ""
    case e <> rest:
      +ep = Ep.epoch(e)
      +after = Lg.after(d, ep)
      String.concat(["a", show.heads(Lg.acked(d, ep)), "\nr", show.heads(Lg.Disk.log(after)), "\n", run(rest, after)])

def go(text: String) -> String:
  run(List.reverse(&2, Ep, setup(String.lines(text), Nil{})), Lg.Absent{})

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
      IO.die(String, 2, "usage: bridge_log <events>")
    case prog <> rest:
      match rest:
        case Nil{}:
          IO.die(String, 2, "usage: bridge_log <events>")
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
