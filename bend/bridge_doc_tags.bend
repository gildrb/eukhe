# bridge_doc_tags: runs the result model of bend/doc_tags.bend on an
# events file and prints which version of a file the tag and the rows of
# a grep result name, line for line as the Rust bridge test prints the
# real grep (crates/eukhe-docs/src/grep/bridge.rs,
# `a_grep_tag_names_the_searched_text_as_the_bend_model`). Build it with
#
#   bend bend/bridge_doc_tags.bend -o <out>
#
# and run `<out> <events>`. Each line `N1 N2` is one grep of every line of
# a file that holds version 1 (N1 lines) when grep searches it and
# version 2 (N2 lines) when grep records the result. Line i of version v
# is the number 1000 v + i. Each line prints
#
#   t V..    the versions whose text the tag names
#   r V..    the versions whose lines the rows are (all of them, in order)

import Base
import ./doc_tags.bend as Dt

def tok.at(ws: List<&2, String>, k: Nat) -> String:
  Maybe.default(&2, String, List.get(&2, String, ws, k), "")

def tok.nat(s: String) -> Nat:
  Maybe.default(&2, Nat, Nat.read(s), 0n)

def arg(+ws: List<&2, String>, k: Nat) -> Nat:
  tok.nat(tok.at(ws, k))

# lines i..n of version v
def version.go(n: Nat, +v: Nat, +i: Nat) -> List<&2, Nat>:
  match n:
    case 0n:
      Nil{}
    case 1n+m:
      Nat.add(Nat.mul(1000n, v), i) <> version.go(m, v, 1n+i)

def version(+v: Nat, n: Nat) -> List<&2, Nat>:
  version.go(n, v, 1n)

def nats.eq(a: List<&2, Nat>, b: List<&2, Nat>) -> Bool:
  match a:
    case Nil{}:
      List.is_empty(&2, Nat, b)
    case x <> xs:
      match b:
        case Nil{}:
          False{}
        case y <> ys:
          Bool.and(Nat.is_eq(x, y), nats.eq(xs, ys))

def mark(b: Bool, s: String) -> String:
  match b:
    case True{}:
      s
    case False{}:
      ""

# the rows are the lines of t, all of them
def rows.of(+t: List<&2, Nat>, +rs: List<&2, Dt.Row>) -> Bool:
  Bool.and(Dt.from_text(t, rs), Nat.is_eq(List.length(&2, Dt.Row, rs), List.length(&2, Nat, t)))

def show(+v1: List<&2, Nat>, +v2: List<&2, Nat>, +s: Dt.Shown) -> String:
  +tag = Dt.Shown.tag(s)
  +rs = Dt.Shown.rows(s)
  String.concat(["t", mark(nats.eq(tag, v1), " 1"), mark(nats.eq(tag, v2), " 2"), "\nr", mark(rows.of(v1, rs), " 1"), mark(rows.of(v2, rs), " 2"), "\n"])

def line(+ws: List<&2, String>) -> String:
  +v1 = version(1n, arg(ws, 0n))
  +v2 = version(2n, arg(ws, 1n))
  show(v1, v2, Dt.show(v1, Dt.Grep{List.replicate(Bool, List.length(&2, Nat, v1), True{}), v2}))

def run(ls: List<&2, String>) -> String:
  match ls:
    case Nil{}:
      ""
    case l <> rest:
      String.append(line(String.split(l, ' ')), run(rest))

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
      IO.die(String, 2, "usage: bridge_doc_tags <events>")
    case prog <> rest:
      match rest:
        case Nil{}:
          IO.die(String, 2, "usage: bridge_doc_tags <events>")
        case path <> more:
          do IO<String>:
            f : File <- IO.try(File, File.open(path, "r"))
            m : File & Result<&1, &1, U32 & String, String> <- File.read(f, 1073741824)
            read.file(m)

def main() -> IO(Unit):
  do IO<Unit>:
    args : List<String> <- IO.args()
    text : String <- scenario(args)
    IO.write(run(String.lines(text)))
