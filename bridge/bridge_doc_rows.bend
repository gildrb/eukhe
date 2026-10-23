# bridge_doc_rows: runs the two row splitters of bend/doc_lines.bend (read
# and grep) on an events file and prints their rows, line for line as the
# Rust bridge test prints the rows of a real read and grep
# (crates/eukhe-docs/src/grep/bridge.rs,
# `read_and_grep_rows_equal_the_bend_model`). Build it with
#
#   bend bridge/bridge_doc_rows.bend -o <out>
#
# and run `<out> <events>`. Each line is one file: `M BODY`. M is 1 when the
# file starts with a BOM (read and grep do not show it). BODY is the body,
# one letter a byte: `a` (content), `r` (\r), `n` (\n). Each file prints
#
#   r N TEXT     each row of read: its line number and text
#   g N TEXT     each row of grep
#
# TEXT has one letter a byte (`a`, `r`), `-` when it is empty.

import Base
import ../bend/doc_lines.bend as Dl

def tok.at(ws: List<&2, String>, k: Nat) -> String:
  Maybe.default(&2, String, List.get(&2, String, ws, k), "")

def body(s: String) -> List<&2, Dl.B>:
  match s:
    case SNil{}:
      Nil{}
    case SCon{'a', rest}:
      Dl.A{} <> body(rest)
    case SCon{'r', rest}:
      Dl.R{} <> body(rest)
    case SCon{'n', rest}:
      Dl.N{} <> body(rest)
    case SCon{c, rest}:
      body(rest)

def show.text(bs: List<&2, Dl.B>) -> String:
  match bs:
    case Nil{}:
      ""
    case b <> rest:
      match b:
        case Dl.A{}:
          String.append("a", show.text(rest))
        case Dl.R{}:
          String.append("r", show.text(rest))
        case Dl.N{}:
          String.append("n", show.text(rest))

def show.row(bs: List<&2, Dl.B>) -> String:
  match bs:
    case Nil{}:
      "-"
    case b <> rest:
      show.text(b <> rest)

def show.rows(+k: String, rs: List<&2, List<&2, Dl.B>>, +n: Nat) -> String:
  match rs:
    case Nil{}:
      ""
    case r <> rest:
      String.concat([k, " ", Nat.show(n), " ", show.row(r), "\n", show.rows(k, rest, 1n+n)])

def line(+bs: List<&2, Dl.B>) -> String:
  String.append(show.rows("r", Dl.read_rows(bs), 1n), show.rows("g", Dl.grep_rows(bs), 1n))

def run(ls: List<&2, String>) -> String:
  match ls:
    case Nil{}:
      ""
    case l <> rest:
      String.append(line(body(tok.at(String.split(l, ' '), 1n))), run(rest))

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
      IO.die(String, 2, "usage: bridge_doc_rows <events>")
    case prog <> rest:
      match rest:
        case Nil{}:
          IO.die(String, 2, "usage: bridge_doc_rows <events>")
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
