# bridge_paths: runs the path part of the tool surface model
# (bend/tools.bend §3) on a scenario file and prints what it did, line
# for line as the Rust bridge test prints the internal URL code
# (crates/eukhe-docs/src/url/bridge.rs). Build it with
#
#   bend bend/bridge_paths.bend -o <out>
#
# and run `<out> <scenario>`. Each line is one path, its segments
# separated by spaces:
#
#   n N     Name{N}
#   u       Up
#   h       Here
#
# and prints `B NAMES`: B is 1 when the path stays under its root
# (`stays(segs, 0)`) and 0 when not; NAMES is `-` when `resolve` gives
# None, else the names it reaches, deepest first, each after a space.

import Base
import ./tools.bend as Tl

# Reading
# -------

def tok.at(ws: List<&2, String>, k: Nat) -> String:
  Maybe.default(&2, String, List.get(&2, String, ws, k), "")

def tok.nat(s: String) -> Nat:
  Maybe.default(&2, Nat, Nat.read(s), 0n)

def tok.head(s: String) -> Char:
  match s:
    case SNil{}:
      ' '
    case SCon{c, t}:
      c

def tok.tail(s: String) -> String:
  match s:
    case SNil{}:
      ""
    case SCon{c, t}:
      t

def bit(b: Bool) -> String:
  match b:
    case True{}:
      "1"
    case False{}:
      "0"

# a token: `nN`, `u` or `h`
def seg.of(name: Bool, up: Bool, n: Nat) -> Tl.Seg:
  match name:
    case True{}:
      Tl.Name{n}
    case False{}:
      match up:
        case True{}:
          Tl.Up{}
        case False{}:
          Tl.Here{}

def seg(+w: String) -> Tl.Seg:
  +c = tok.head(w)
  seg.of(Char.is_eq(c, 'n'), Char.is_eq(c, 'u'), tok.nat(tok.tail(w)))

def segs(ws: List<&2, String>) -> List<&2, Tl.Seg>:
  match ws:
    case Nil{}:
      Nil{}
    case w <> rest:
      match w:
        case SNil{}:
          segs(rest)
        case SCon{c, t}:
          seg(SCon{c, t}) <> segs(rest)

# Showing
# -------

def names.show(xs: List<&2, Nat>) -> String:
  match xs:
    case Nil{}:
      ""
    case x <> rest:
      String.concat([" ", Nat.show(x), names.show(rest)])

def resolved.show(r: Maybe<&2, List<&2, Nat>>) -> String:
  match r:
    case None{}:
      " -"
    case Some{xs}:
      names.show(xs)

def line.show(+ss: List<&2, Tl.Seg>) -> String:
  String.concat([bit(Tl.stays(ss, 0n)), resolved.show(Tl.resolve(ss)), "\n"])

def run(ls: List<&2, String>) -> String:
  match ls:
    case Nil{}:
      ""
    case l <> rest:
      String.append(line.show(segs(String.split(l, ' '))), run(rest))

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
      IO.die(String, 2, "usage: bridge_paths <scenario>")
    case prog <> rest:
      match rest:
        case Nil{}:
          IO.die(String, 2, "usage: bridge_paths <scenario>")
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
