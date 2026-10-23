# bridge_doc_lines: runs the line model of bend/doc_lines.bend (load, an
# edit, persist) on an events file and prints the bytes it persists, line
# for line as the Rust bridge test prints the file the real edit wrote
# (crates/eukhe-docs/src/hashline/bridge.rs). Build it with
#
#   bend bridge/bridge_doc_lines.bend -o <out>
#
# and run `<out> <events>`. Each line is one file and one edit:
#
#   M BODY OP ARGS
#
# M is 1 when the file starts with a BOM, else 0. BODY is the body, one
# letter a byte: `a` (content), `r` (\r), `n` (\n); `-` when it is empty.
# OP is the hashline edit (line numbers are one-based):
#
#   p S E K   PUT S.=E: with K new lines
#   c S E     CUT S.=E
#   b S K     PUT <S: with K new lines (S > 1)
#   a S K     PUT >S: with K new lines
#   h K       PUT <1: with K new lines
#   t K       PUT >$: with K new lines
#
# New line i (from 0) is 10 + i `a` bytes. Each line prints the persisted
# file: `B` when it starts with a BOM, then its body as BODY is written.

import Base
import ../bend/doc_lines.bend as Dl

# Reading
# -------

def tok.at(ws: List<&2, String>, k: Nat) -> String:
  Maybe.default(&2, String, List.get(&2, String, ws, k), "")

def tok.nat(s: String) -> Nat:
  Maybe.default(&2, Nat, Nat.read(s), 0n)

def arg(+ws: List<&2, String>, k: Nat) -> Nat:
  tok.nat(tok.at(ws, k))

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

# The edit
# --------

def news(n: Nat, +i: Nat) -> List<&2, List<&2, Dl.B>>:
  match n:
    case 0n:
      Nil{}
    case 1n+m:
      List.replicate(Dl.B, Nat.add(10n, i), Dl.A{}) <> news(m, 1n+i)

# whether the pieces are one empty piece (an empty body)
def empty1(ps: List<&2, Dl.Piece>) -> Bool:
  match ps:
    case Nil{}:
      False{}
    case p <> rest:
      match p:
        case Dl.Piece{t, e}:
          match rest:
            case Nil{}:
              List.is_empty(&2, Dl.B, t)
            case q <> more:
              False{}

def last_empty.go(rest: List<&2, Dl.Piece>, t: List<&2, Dl.B>) -> Bool:
  match rest:
    case Nil{}:
      List.is_empty(&2, Dl.B, t)
    case q <> more:
      match q:
        case Dl.Piece{t2, e2}:
          last_empty.go(more, t2)

# whether the last piece is empty (the body ends with `\n`)
def last_empty(ps: List<&2, Dl.Piece>) -> Bool:
  match ps:
    case Nil{}:
      False{}
    case p <> rest:
      match p:
        case Dl.Piece{t, e}:
          last_empty.go(rest, t)

# where an insert at the start of the file goes: (s, k)
def at_bof(e1: Bool) -> Nat & Nat:
  match e1:
    case True{}:
      (0n, 1n)
    case False{}:
      (0n, 0n)

# where an insert at the end of the file goes: (s, k)
def at_eof(e1: Bool, le: Bool, n: Nat) -> Nat & Nat:
  match e1:
    case True{}:
      (0n, 1n)
    case False{}:
      match le:
        case True{}:
          (Nat.sub(n, 1n), 0n)
        case False{}:
          (n, 0n)

# the lines [s, s+k) the op (first letter h) of the words ws replaces in
# the pieces ps, and its new lines
def plan(h: String, +ws: List<&2, String>, +ps: List<&2, Dl.Piece>) -> (Nat & Nat) & List<&2, List<&2, Dl.B>>:
  match h:
    case SCon{'p', r}:
      ((Nat.sub(arg(ws, 3n), 1n), Nat.sub(Nat.add(arg(ws, 4n), 1n), arg(ws, 3n))), news(arg(ws, 5n), 0n))
    case SCon{'c', r}:
      ((Nat.sub(arg(ws, 3n), 1n), Nat.sub(Nat.add(arg(ws, 4n), 1n), arg(ws, 3n))), Nil{})
    case SCon{'b', r}:
      ((Nat.sub(arg(ws, 3n), 1n), 0n), news(arg(ws, 4n), 0n))
    case SCon{'a', r}:
      ((arg(ws, 3n), 0n), news(arg(ws, 4n), 0n))
    case SCon{'h', r}:
      (at_bof(empty1(ps)), news(arg(ws, 3n), 0n))
    case r:
      (at_eof(empty1(ps), last_empty(ps), List.length(&2, Dl.Piece, ps)), news(arg(ws, 3n), 0n))

def apply(d: Dl.Ed, pl: (Nat & Nat) & List<&2, List<&2, Dl.B>>) -> Dl.Doc:
  (at, xs) = pl
  (s, k) = at
  Dl.persist(Dl.edit(d, s, k, xs))

# run the op (its first letter h) of the words ws on the file d
def run.op(h: String, +ws: List<&2, String>, d: Dl.Ed) -> Dl.Doc:
  match d:
    case Dl.Ed{bom, c, +ps}:
      apply(Dl.Ed{bom, c, ps}, plan(h, ws, ps))

# Writing
# -------

def show.body(bs: List<&2, Dl.B>) -> String:
  match bs:
    case Nil{}:
      ""
    case b <> rest:
      match b:
        case Dl.A{}:
          String.append("a", show.body(rest))
        case Dl.R{}:
          String.append("r", show.body(rest))
        case Dl.N{}:
          String.append("n", show.body(rest))

def show.bom(b: Bool) -> String:
  match b:
    case True{}:
      "B"
    case False{}:
      ""

def show.all(bs: List<&2, Dl.B>) -> String:
  match bs:
    case Nil{}:
      "-"
    case b <> rest:
      show.body(b <> rest)

def show(d: Dl.Doc) -> String:
  match d:
    case Dl.Doc{bom, bs}:
      String.concat([show.bom(bom), show.all(bs), "\n"])

def line(+ws: List<&2, String>) -> String:
  +doc = {Dl.Doc{Nat.is_eq(arg(ws, 0n), 1n), body(tok.at(ws, 1n))} : Dl.Doc}
  show(run.op(tok.at(ws, 2n), ws, Dl.load(doc)))

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
      IO.die(String, 2, "usage: bridge_doc_lines <events>")
    case prog <> rest:
      match rest:
        case Nil{}:
          IO.die(String, 2, "usage: bridge_doc_lines <events>")
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
