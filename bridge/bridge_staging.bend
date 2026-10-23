# bridge_staging: runs the models of bend/staging.bend on an events file
# and prints what they did, line for line as the Rust bridge test prints
# the real code (crates/eukhe-core/src/durable/staging/bridge.rs,
# `staging_sweep_and_listing_run_as_their_model`). Build it with
#
#   bend bridge/bridge_staging.bend -o <out>
#
# and run `<out> <events>`. An events file has one event per line:
#
#   p T              publish a staging directory to a target that is
#                    absent (T 0), an empty directory (1), a directory with
#                    entries (2), or a file (3)
#   n I S H T O      a node the sweep may meet: id I; sort S (0 staging
#                    directory or tombstone, 1 lock file with its
#                    directory, 2 lock file alone, 3 storage, 4 other
#                    directory, 5 other); held H, stale T, reached O (1/0)
#   d N M H C        a directory N of the sessions directory: it holds
#                    main.jsonl (M), is hidden (H), its cwd reads (C)
#   l N R            a legacy file with stem N whose header reads (R)
#
# Then it prints
#
#   p ok|exists      what the publish did
#   t T              what the target holds then (0: the staged storage)
#   x I I ...        the ids the sweep removes, in order
#   s N N ...        the listing, by name, ascending
#   i N N ...        the listing after each listed legacy file is
#                    imported, by name, ascending

import Base
import ../bend/staging.bend as Sg

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

def sort(n: Nat) -> Sg.Sort:
  match n:
    case 0n:
      Sg.Leftover{}
    case 1n+a:
      match a:
        case 0n:
          Sg.Lock{True{}}
        case 1n+b:
          match b:
            case 0n:
              Sg.Lock{False{}}
            case 1n+c:
              match c:
                case 0n:
                  Sg.Store{}
                case 1n+d:
                  match d:
                    case 0n:
                      Sg.Plain{}
                    case 1n+e:
                      Sg.Other{}

# What the events set up: the publish target, the nodes and the entries,
# each newest first
type St is Data:
  St{pub: List<&2, Nat>, nodes: List<&2, Sg.Node>, ents: List<&2, Sg.Ent>}

def line(h: String, +ws: List<&2, String>, s: St) -> St:
  match h:
    case SCon{'p', r}:
      match s:
        case St{p, ns, es}:
          St{arg(ws, 1n) <> p, ns, es}
    case SCon{'n', r}:
      match s:
        case St{p, ns, es}:
          St{p, Sg.Node{arg(ws, 1n), sort(arg(ws, 2n)), yes(arg(ws, 3n)), yes(arg(ws, 4n)), yes(arg(ws, 5n))} <> ns, es}
    case SCon{'d', r}:
      match s:
        case St{p, ns, es}:
          St{p, ns, Sg.Dir{arg(ws, 1n), yes(arg(ws, 2n)), yes(arg(ws, 3n)), yes(arg(ws, 4n))} <> es}
    case SCon{'l', r}:
      match s:
        case St{p, ns, es}:
          St{p, ns, Sg.Legacy{arg(ws, 1n), yes(arg(ws, 2n))} <> es}
    case r:
      s

def setup(ls: List<&2, String>, s: St) -> St:
  match ls:
    case Nil{}:
      s
    case l <> rest:
      +ws = String.split(l, ' ')
      setup(rest, line(tok.at(ws, 0n), ws, s))

# Writing
# -------

def show.nats(ns: List<&2, Nat>) -> String:
  match ns:
    case Nil{}:
      ""
    case n <> rest:
      String.concat([" ", Nat.show(n), show.nats(rest)])

def show.ids(ns: List<&2, Sg.Node>) -> String:
  match ns:
    case Nil{}:
      ""
    case n <> rest:
      match n:
        case Sg.Node{i, k, h, t, o}:
          String.concat([" ", Nat.show(i), show.ids(rest)])

def show.tag.put(b: Bool, g: Nat, rest: String) -> String:
  match b:
    case True{}:
      String.concat([" ", Nat.show(g), rest])
    case False{}:
      rest

# the tag of the target, entry 2
def show.tag(es: List<&2, Sg.Entry>) -> String:
  match es:
    case Nil{}:
      ""
    case e <> rest:
      match e:
        case Sg.Entry{n, g}:
          show.tag.put(Nat.is_eq(n, 2n), g, show.tag(rest))

def show.res(p: Sg.Pub) -> String:
  match p:
    case Sg.Pub{ok, es}:
      match ok:
        case True{}:
          String.concat(["p ok\nt", show.tag(es), "\n"])
        case False{}:
          String.concat(["p exists\nt", show.tag(es), "\n"])

# the staging directory is entry 1 (it holds tag 0); the target is entry 2
def show.pub(ts: List<&2, Nat>) -> String:
  match ts:
    case Nil{}:
      ""
    case t <> rest:
      match t:
        case 0n:
          String.concat([show.res(Sg.publish(1n, 2n, [Sg.Entry{1n, 0n}])), show.pub(rest)])
        case 1n+u:
          String.concat([show.res(Sg.publish(1n, 2n, [Sg.Entry{1n, 0n}, Sg.Entry{2n, 1n+u}])), show.pub(rest)])

def le(a: Nat, b: Nat) -> Bool:
  Nat.is_le(a, b)

def sorted(xs: List<&2, Nat>) -> List<&2, Nat>:
  List.sort(~Nat, ~le, xs)

# import every listed legacy stem, in order
def import.all(ss: List<&2, Nat>, es: List<&2, Sg.Ent>) -> List<&2, Sg.Ent>:
  match ss:
    case Nil{}:
      es
    case s <> rest:
      import.all(rest, Sg.imported(s, es))

def show.list(es: List<&2, Sg.Ent>) -> String:
  match es:
    case Nil{}:
      ""
    case e <> rest:
      +all = {e <> rest : List<&2, Sg.Ent>}
      +after = import.all(sorted(Sg.legacies(all, all)), all)
      String.concat(["s", show.nats(sorted(Sg.listing(all))), "\ni", show.nats(sorted(Sg.listing(after))), "\n"])

def show.sweep(ns: List<&2, Sg.Node>) -> String:
  match ns:
    case Nil{}:
      ""
    case n <> rest:
      String.concat(["x", show.ids(Sg.sweep(n <> rest)), "\n"])

def show(s: St) -> String:
  match s:
    case St{p, ns, es}:
      String.concat([show.pub(List.reverse(&2, Nat, p)), show.sweep(List.reverse(&2, Sg.Node, ns)), show.list(List.reverse(&2, Sg.Ent, es))])

def go(text: String) -> String:
  show(setup(String.lines(text), St{Nil{}, Nil{}, Nil{}}))

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
      IO.die(String, 2, "usage: bridge_staging <events>")
    case prog <> rest:
      match rest:
        case Nil{}:
          IO.die(String, 2, "usage: bridge_staging <events>")
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
