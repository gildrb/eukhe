# bridge_default_model: runs the session-model model (`resolve` and `open`
# in default_model.bend) on a scenario file and prints each session, line
# for line as the Rust bridge test prints the real `resolve_open_model`
# over generated catalogs
# (crates/eukhe-core/src/durable/models/default_bridge.rs). Build it with
#
#   bend bend/bridge_default_model.bend -o <out>
#
# and run `<out> <scenario>`. A scenario has one resolution per line:
#
#   saved cat key out next
#
#   saved  0: no saved default, 1+m: the saved default is model m
#   cat    1: the model catalog has the saved default, 0: it does not
#   key    1: its provider has credentials, 0: it does not
#   out    1: a set enabledModels scope leaves it out, 0: it does not
#   next   0: the startup chain picks nothing without the saved default,
#          1+i: it picks the other model i
#
# For each resolution it prints the model the session runs on (`S`: the
# saved default, `O i`: the other model i, `X`: no model), then ` N m r`
# for each notice (the saved default m and the reason r: 0 not in the
# catalog, 1 no credentials, 2 not in the scope).

import Base
import ./default_model.bend as Dm

# Reading
# -------

def tok.nat(s: String) -> Nat:
  Maybe.default(&2, Nat, Nat.read(s), 0n)

def tok.at(ws: List<&2, String>, k: Nat) -> String:
  Maybe.default(&2, String, List.get(&2, String, ws, k), "")

def tok.bool(n: Nat) -> Bool:
  match n:
    case 0n:
      False{}
    case 1n+p:
      True{}

def saved.of(n: Nat) -> Dm.Saved:
  match n:
    case 0n:
      Dm.NoDefault{}
    case 1n+m:
      Dm.Default{m}

def next.of(n: Nat) -> Dm.Next:
  match n:
    case 0n:
      Dm.NoNext{}
    case 1n+i:
      Dm.Next{i}

def field(+ws: List<&2, String>, k: Nat) -> Nat:
  tok.nat(tok.at(ws, k))

# a line that starts with a number is a resolution; others are skipped
def res.add(m: Maybe<&2, Nat>, +ws: List<&2, String>, t: List<&2, Dm.In>) -> List<&2, Dm.In>:
  match m:
    case None{}:
      t
    case Some{x}:
      Dm.In{saved.of(x), tok.bool(field(ws, 1n)), tok.bool(field(ws, 2n)), tok.bool(field(ws, 3n)), next.of(field(ws, 4n))} <> t

def resolutions(ls: List<&2, String>) -> List<&2, Dm.In>:
  match ls:
    case Nil{}:
      Nil{}
    case l <> rest:
      +ws = String.split(l, ' ')
      res.add(Nat.read(tok.at(ws, 0n)), ws, resolutions(rest))

# Writing
# -------

def show.reason(r: Dm.Reason) -> String:
  match r:
    case Dm.NotInCatalog{}:
      "0"
    case Dm.NoCredentials{}:
      "1"
    case Dm.NotInScope{}:
      "2"

def show.run(r: Dm.Run) -> String:
  match r:
    case Dm.On{p}:
      match p:
        case Dm.Saved{}:
          "S"
        case Dm.Other{n}:
          String.append("O ", Nat.show(n))
    case Dm.Idle{}:
      "X"

def show.notes(ks: List<&2, Dm.Key>) -> String:
  match ks:
    case Nil{}:
      ""
    case k <> rest:
      match k:
        case Dm.K{m, r}:
          String.concat([" N ", Nat.show(m), " ", show.reason(r), show.notes(rest)])

def show.session(s: Dm.Session) -> String:
  match s:
    case Dm.Session{run, notes}:
      String.concat([show.run(run), show.notes(notes), "\n"])

def show(xs: List<&2, Dm.In>) -> String:
  match xs:
    case Nil{}:
      ""
    case x <> rest:
      String.append(show.session(Dm.open(Dm.resolve(x))), show(rest))

# the report of the scenario text
def report(text: String) -> String:
  show(resolutions(String.lines(text)))

# Running
# -------

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
      IO.die(String, 2, "usage: bridge_default_model <scenario>")
    case prog <> rest:
      match rest:
        case Nil{}:
          IO.die(String, 2, "usage: bridge_default_model <scenario>")
        case path <> more:
          do IO<String>:
            f : File <- IO.try(File, File.open(path, "r"))
            m : File & Result<&1, &1, U32 & String, String> <- File.read(f, 1073741824)
            read.file(m)

def main() -> IO(Unit):
  do IO<Unit>:
    args : List<String> <- IO.args()
    text : String <- scenario(args)
    IO.write(report(text))
