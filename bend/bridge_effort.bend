# bridge_effort: runs the reasoning-depth model (bend/infer.bend section 6,
# the ladder data; bend/effort.bend, the clamp and the cycle) on a
# scenario file and prints what it did, line for line as the Rust bridge
# test prints the Rust code (crates/eukhe-core/src/durable/effort_bridge.rs).
# Build it with
#
#   bend bend/bridge_effort.bend -o <out>
#
# and run `<out> <scenario>`. The first line gives the rulebook's default
# ladders:
#
#   d R0 .. R6 P0 .. P6
#
# Ri is `1` when the reasoning default ladder lists level i of the ladder
# (off, minimal, low, medium, high, xhigh, max), else `0`; Pi the same for
# the plain default ladder. Each later line is one model:
#
#   R M E0 E1 E2 E3 E4 E5 E6 L F0 F1 F2 F3 F4 F5 F6
#
# R is `1` for a reasoning model, else `0`; M is `1` when the model has an
# explicit thinking-level map, else `0` (then every entry is `-`); Ei is
# the map's entry for level i: `-` missing, `n` null, `w` a wire string. L
# is `1` when the rulebook gives the model a ladder, else `0`; Fi is that
# ladder's entry for level i. For each model it prints four lines; each
# item has one space before it:
#
#   offered L ..     the offered levels (`lad.offered`)
#   clamp C0 .. C6   the clamp of each ladder level (`clamp.in`)
#   forward F0 .. F6 a forward cycle step from each ladder level
#                    (`cycle.in`), `-` when it changes nothing
#   backward B0 .. B6 a backward cycle step from each ladder level
#
# A level prints as its wire name: off, minimal, low, medium, high,
# xhigh, max.

import Base
import ./effort.bend as Ef
import ./infer.bend as If

# Reading
# -------

def tok.at(ws: List<&2, String>, k: Nat) -> String:
  Maybe.default(&2, String, List.get(&2, String, ws, k), "")

def tok.head(s: String) -> Char:
  match s:
    case SNil{}:
      ' '
    case SCon{c, t}:
      c

def flag(+ws: List<&2, String>, k: Nat) -> Bool:
  Char.is_eq(tok.head(tok.at(ws, k)), '1')

def ent.of(null: Bool, wire: Bool) -> Ef.Ent:
  match null:
    case True{}:
      Ef.Null{}
    case False{}:
      match wire:
        case True{}:
          Ef.Wire{}
        case False{}:
          Ef.Missing{}

# the entry at word k
def ent(+ws: List<&2, String>, k: Nat) -> Ef.Ent:
  +c = tok.head(tok.at(ws, k))
  ent.of(Char.is_eq(c, 'n'), Char.is_eq(c, 'w'))

# the map whose entries start at word k, when has
def map.of(has: Bool, +ws: List<&2, String>, +k: Nat) -> Maybe<&2, Ef.LvMap>:
  match has:
    case True{}:
      Some{Ef.LvMap{ent(ws, k), ent(ws, 1n+k), ent(ws, 2n+k), ent(ws, 3n+k), ent(ws, 4n+k), ent(ws, 5n+k), ent(ws, 6n+k)}}
    case False{}:
      None{}

# the levels of xs whose flag, from word k on, is `1`
def flags(xs: List<&2, Ef.Lv>, +ws: List<&2, String>, +k: Nat) -> List<&2, Ef.Lv>:
  match xs:
    case Nil{}:
      Nil{}
    case x <> rest:
      Ef.cons_if(flag(ws, k), x, flags(rest, ws, 1n+k))

def defaults.of(+ws: List<&2, String>) -> If.Defaults:
  If.Defaults{flags(Ef.ladder(), ws, 1n), flags(Ef.ladder(), ws, 8n)}

# the levels the model of a line offers
def offered.of(+ws: List<&2, String>, d: If.Defaults) -> List<&2, Ef.Lv>:
  If.lad.offered(flag(ws, 0n), map.of(flag(ws, 1n), ws, 2n), map.of(flag(ws, 9n), ws, 10n), d)

# Printing
# --------

def lv.show(l: Ef.Lv) -> String:
  match l:
    case Ef.Off{}:
      "off"
    case Ef.Minimal{}:
      "minimal"
    case Ef.Low{}:
      "low"
    case Ef.Medium{}:
      "medium"
    case Ef.High{}:
      "high"
    case Ef.Xhigh{}:
      "xhigh"
    case Ef.Max{}:
      "max"

def step.show(r: Maybe<&2, Ef.Lv>) -> String:
  match r:
    case None{}:
      "-"
    case Some{l}:
      lv.show(l)

def lvs.show(ls: List<&2, Ef.Lv>) -> String:
  match ls:
    case Nil{}:
      ""
    case l <> rest:
      String.concat([" ", lv.show(l), lvs.show(rest)])

def clamps.show(+lad: List<&2, Ef.Lv>, ls: List<&2, Ef.Lv>) -> String:
  match ls:
    case Nil{}:
      ""
    case l <> rest:
      String.concat([" ", lv.show(Ef.clamp.in(lad, l)), clamps.show(lad, rest)])

def steps.show(+lad: List<&2, Ef.Lv>, +d: Ef.Dir, ls: List<&2, Ef.Lv>) -> String:
  match ls:
    case Nil{}:
      ""
    case l <> rest:
      String.concat([" ", step.show(Ef.cycle.in(lad, l, d)), steps.show(lad, d, rest)])

def lad.show(+lad: List<&2, Ef.Lv>) -> String:
  String.concat(["offered", lvs.show(lad), "\nclamp", clamps.show(lad, Ef.ladder()), "\nforward", steps.show(lad, Ef.Forward{}, Ef.ladder()), "\nbackward", steps.show(lad, Ef.Backward{}, Ef.ladder()), "\n"])

# Running
# -------

# what one line did: the default ladders after it, and its output
type Out is Data:
  Out{d: If.Defaults, text: String}

def Out.d(o: Out) -> If.Defaults:
  match o:
    case Out{d, t}:
      d

def Out.text(o: Out) -> String:
  match o:
    case Out{d, t}:
      t

# one line; isd and ism say whether its first word names the defaults or
# a model; any other line (the empty line after the last) prints nothing
def line(isd: Bool, ism: Bool, +ws: List<&2, String>, +d: If.Defaults) -> Out:
  match isd ism:
    case True{} ism:
      Out{defaults.of(ws), ""}
    case False{} True{}:
      Out{d, lad.show(offered.of(ws, d))}
    case False{} False{}:
      Out{d, ""}

def run(ls: List<&2, String>, +d: If.Defaults) -> String:
  match ls:
    case Nil{}:
      ""
    case l <> rest:
      +ws = String.split(l, ' ')
      +c = tok.head(tok.at(ws, 0n))
      +o = line(Char.is_eq(c, 'd'), Bool.or(Char.is_eq(c, '0'), Char.is_eq(c, '1')), ws, d)
      String.append(Out.text(o), run(rest, Out.d(o)))

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
      IO.die(String, 2, "usage: bridge_effort <scenario>")
    case prog <> rest:
      match rest:
        case Nil{}:
          IO.die(String, 2, "usage: bridge_effort <scenario>")
        case path <> more:
          do IO<String>:
            f : File <- IO.try(File, File.open(path, "r"))
            m : File & Result<&1, &1, U32 & String, String> <- File.read(f, 1073741824)
            read.file(m)

def main() -> IO(Unit):
  do IO<Unit>:
    args : List<String> <- IO.args()
    text : String <- scenario(args)
    IO.write(run(String.lines(text), If.Defaults{Nil{}, Nil{}}))
