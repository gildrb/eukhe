# bridge_gateway_width: runs the table model (bend/gateway_width.bend) on
# a scenario file and prints the table it renders, line for line as the
# bridge test in crates/eukhe-gateway/src/style/tests.rs prints the Rust
# formatter. Build it with
#
#   bend bend/bridge_gateway_width.bend -o <out>
#
# and run `<out> <scenario>`. Each row of the table is one line, its
# fields separated by tabs:
#
#   r C1 C2 ..
#
# Ci is a cell: one digit per glyph, its display width (an empty field is
# an empty cell). Other lines are ignored. It prints one line per row: the
# display width of each column, separated by spaces.

import Base
import ./gateway_width.bend as Gw

def cell(cs: List<&2, Char>) -> List<&2, Nat>:
  match cs:
    case Nil{}:
      Nil{}
    case c <> rest:
      U32.to_nat((Char.to_u32(c) - 48 : U32)) <> cell(rest)

def cells(fs: List<&2, String>) -> List<&2, List<&2, Nat>>:
  match fs:
    case Nil{}:
      Nil{}
    case f <> rest:
      cell(String.to_list(f)) <> cells(rest)

def row.of(ok: Bool, fields: List<&2, String>) -> List<&2, List<&2, List<&2, Nat>>>:
  match ok:
    case True{}:
      [cells(fields)]
    case False{}:
      Nil{}

def row(ws: List<&2, String>) -> List<&2, List<&2, List<&2, Nat>>>:
  match ws:
    case Nil{}:
      Nil{}
    case w <> rest:
      row.of(String.eq(w, "r"), rest)

def rows(ls: List<&2, String>) -> List<&2, List<&2, List<&2, Nat>>>:
  match ls:
    case Nil{}:
      Nil{}
    case l <> rest:
      List.append(&2, List<&2, List<&2, Nat>>, row(String.split(l, '\t')), rows(rest))

def show.line(ws: List<&2, Nat>) -> String:
  match ws:
    case Nil{}:
      ""
    case w <> rest:
      match rest:
        case Nil{}:
          Nat.show(w)
        case v <> more:
          String.concat([Nat.show(w), " ", show.line(v <> more)])

def show(ls: List<&2, List<&2, Nat>>) -> String:
  match ls:
    case Nil{}:
      ""
    case l <> rest:
      String.concat([show.line(l), "\n", show(rest)])

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
      IO.die(String, 2, "usage: bridge_gateway_width <scenario>")
    case prog <> rest:
      match rest:
        case Nil{}:
          IO.die(String, 2, "usage: bridge_gateway_width <scenario>")
        case path <> more:
          do IO<String>:
            f : File <- IO.try(File, File.open(path, "r"))
            m : File & Result<&1, &1, U32 & String, String> <- File.read(f, 1073741824)
            read.file(m)

def main() -> IO(Unit):
  do IO<Unit>:
    args : List<String> <- IO.args()
    text : String <- scenario(args)
    IO.write(show(Gw.table(Gw.Display{}, rows(String.lines(text)))))
