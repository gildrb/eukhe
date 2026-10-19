# bridge_tui_color: runs the terminal color model (bend/tui_color.bend)
# on a scenario file and prints what it computes, line for line as the
# Rust bridge test prints the Rust code (crates/eukhe-tui/src/theme/
# bridge.rs). Build it with
#
#   bend bend/bridge_tui_color.bend -o <out>
#
# and run `<out> <scenario>`. One query a line:
#
#   e LR LG LB HR HG HB N   the N-rung ramp from (LR, LG, LB) to (HR, HG,
#                           HB) (`ramp`); prints `e` and ` R,G,B` a rung
#   s I N                   the N-rung effort ramp of shipped theme I (0
#                           eukhe, 1 dark, 2 light); prints `s` and the
#                           rungs
#   b T W                   the usage band of T tokens in a W-token
#                           window (`band`); prints `b B`
#   r                       the roles (`roles`); prints `r` and ` I` a
#                           role, its token index

import Base
import ./tui_color.bend as TC
import ./theme.bend as T

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

def arg(+ws: List<&2, String>, k: Nat) -> Nat:
  tok.nat(tok.at(ws, k))

# Showing
# -------

def rungs.show(xs: List<&2, TC.Px>) -> String:
  match xs:
    case Nil{}:
      ""
    case Con{x, rest}:
      match x:
        case TC.Px{r, g, b}:
          String.concat([" ", Nat.show(r), ",", Nat.show(g), ",", Nat.show(b), rungs.show(rest)])

def nats.show(xs: List<&2, Nat>) -> String:
  match xs:
    case Nil{}:
      ""
    case Con{x, rest}:
      String.concat([" ", Nat.show(x), nats.show(rest)])

def shipped.of(i: Nat) -> T.Shipped:
  match i:
    case 0n:
      T.Eukhe{}
    case 1n:
      T.Dark{}
    case 2n+p:
      T.Light{}

# Running
# -------

def query.ramp(+ws: List<&2, String>) -> String:
  +lo = {TC.Px{arg(ws, 1n), arg(ws, 2n), arg(ws, 3n)} : TC.Px}
  +hi = {TC.Px{arg(ws, 4n), arg(ws, 5n), arg(ws, 6n)} : TC.Px}
  String.concat(["e", rungs.show(TC.ramp(lo, hi, arg(ws, 7n))), "\n"])

def query.shipped(+ws: List<&2, String>) -> String:
  +s = shipped.of(arg(ws, 1n))
  String.concat(["s", rungs.show(TC.ramp(TC.shipped.lo(s), TC.shipped.hi(s), arg(ws, 2n))), "\n"])

def query.pick(ramp: Bool, shipped: Bool, band: Bool, +ws: List<&2, String>) -> String:
  match ramp:
    case True{}:
      query.ramp(ws)
    case False{}:
      match shipped:
        case True{}:
          query.shipped(ws)
        case False{}:
          match band:
            case True{}:
              String.concat(["b ", Nat.show(TC.band(arg(ws, 1n), arg(ws, 2n))), "\n"])
            case False{}:
              String.concat(["r", nats.show(TC.roles()), "\n"])

def query(+c: Char, +ws: List<&2, String>) -> String:
  query.pick(Char.is_eq(c, 'e'), Char.is_eq(c, 's'), Char.is_eq(c, 'b'), ws)

def run(ls: List<&2, String>) -> String:
  match ls:
    case Nil{}:
      ""
    case l <> rest:
      +ws = String.split(l, ' ')
      String.append(query(tok.head(tok.at(ws, 0n)), ws), run(rest))

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
      IO.die(String, 2, "usage: bridge_tui_color <scenario>")
    case prog <> rest:
      match rest:
        case Nil{}:
          IO.die(String, 2, "usage: bridge_tui_color <scenario>")
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
