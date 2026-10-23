# bridge_revive: runs the model of busy evidence (bend/revive.bend) on an
# events file and prints what it did, line for line as the Rust bridge
# test prints `revival_gate::busy_evidence_fresh` on the worker's refresh
# schedule (crates/eukhe-daemon/src/supervision_bridge.rs,
# `the_revival_runs_as_its_model`). Build it with
#
#   bend bridge/bridge_revive.bend -o <out>
#
# and run `<out> <events>`. An events file has one run per line (seconds):
#
#   v H B C D      a refresh every H, the boot window B, a crash C into the
#                  run, a boot D after the crash
#
# Then it prints, for each run,
#
#   v 1            the boot revives the run (its evidence is fresh)
#   v 0            the evidence is stale

import Base
import ../bend/revive.bend as Rv

def tok.nat(s: String) -> Nat:
  Maybe.default(&2, Nat, Nat.read(s), 0n)

def tok.at(ws: List<&2, String>, k: Nat) -> String:
  Maybe.default(&2, String, List.get(&2, String, ws, k), "")

def arg(+ws: List<&2, String>, k: Nat) -> Nat:
  tok.nat(tok.at(ws, k))

def show.bool(b: Bool) -> String:
  match b:
    case True{}:
      "v 1\n"
    case False{}:
      "v 0\n"

def run.line(+ws: List<&2, String>) -> String:
  +h = arg(ws, 1n)
  show.bool(Rv.fresh(Nat.add(h, arg(ws, 2n)), Rv.age(h, arg(ws, 3n), arg(ws, 4n))))

def line(h: String, +ws: List<&2, String>) -> String:
  match h:
    case SCon{'v', r}:
      run.line(ws)
    case r:
      ""

def go(ls: List<&2, String>) -> String:
  match ls:
    case Nil{}:
      ""
    case l <> rest:
      +ws = String.split(l, ' ')
      String.append(line(tok.at(ws, 0n), ws), go(rest))

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
      IO.die(String, 2, "usage: bridge_revive <events>")
    case prog <> rest:
      match rest:
        case Nil{}:
          IO.die(String, 2, "usage: bridge_revive <events>")
        case path <> more:
          do IO<String>:
            f : File <- IO.try(File, File.open(path, "r"))
            m : File & Result<&1, &1, U32 & String, String> <- File.read(f, 1073741824)
            read.file(m)

def main() -> IO(Unit):
  do IO<Unit>:
    args : List<String> <- IO.args()
    text : String <- scenario(args)
    IO.write(go(String.lines(text)))
