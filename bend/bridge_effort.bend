# bridge_effort: runs the reasoning-depth model (bend/effort.bend) on a
# scenario file and prints what it did, line for line as the Rust bridge
# test prints the Rust code (crates/eukhe-core/src/durable/effort_bridge.rs).
# Build it with
#
#   bend bend/bridge_effort.bend -o <out>
#
# and run `<out> <scenario>`. Each line of the scenario is one model:
#
#   R M E0 E1 E2 E3 E4 E5 E6
#
# R is `1` for a reasoning model, else `0`; M is `1` when the model has a
# thinking-level map, else `0` (then every entry is `-`); Ei is the map's
# entry for level i of the ladder (off, minimal, low, medium, high,
# xhigh, max): `-` missing, `n` null, `w` a wire string. For each model
# it prints four lines; each item has one space before it:
#
#   offered L ..     the offered levels (`offered`)
#   clamp C0 .. C6   the clamp of each ladder level (`clamp`)
#   forward F0 .. F6 a forward cycle step from each ladder level
#                    (`cycle`), `-` when it changes nothing
#   backward B0 .. B6 a backward cycle step from each ladder level
#
# A level prints as its wire name: off, minimal, low, medium, high,
# xhigh, max.

import Base
import ./effort.bend as Ef

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

# entry i of the map: the token at word 2 + i
def ent(+ws: List<&2, String>, k: Nat) -> Ef.Ent:
  +c = tok.head(tok.at(ws, k))
  ent.of(Char.is_eq(c, 'n'), Char.is_eq(c, 'w'))

def map.of(has: Bool, +ws: List<&2, String>) -> Ef.LvMap:
  match has:
    case True{}:
      Ef.LvMap{ent(ws, 2n), ent(ws, 3n), ent(ws, 4n), ent(ws, 5n), ent(ws, 6n), ent(ws, 7n), ent(ws, 8n)}
    case False{}:
      Ef.LvMap.none()

def model(+ws: List<&2, String>) -> Ef.Mdl:
  Ef.Mdl{flag(ws, 0n), map.of(flag(ws, 1n), ws)}

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

def clamps.show(+m: Ef.Mdl, ls: List<&2, Ef.Lv>) -> String:
  match ls:
    case Nil{}:
      ""
    case l <> rest:
      String.concat([" ", lv.show(Ef.clamp(m, l)), clamps.show(m, rest)])

def steps.show(+m: Ef.Mdl, +d: Ef.Dir, ls: List<&2, Ef.Lv>) -> String:
  match ls:
    case Nil{}:
      ""
    case l <> rest:
      String.concat([" ", step.show(Ef.cycle(m, l, d)), steps.show(m, d, rest)])

def model.show(+m: Ef.Mdl) -> String:
  String.concat(["offered", lvs.show(Ef.offered(m)), "\nclamp", clamps.show(m, Ef.ladder()), "\nforward", steps.show(m, Ef.Forward{}, Ef.ladder()), "\nbackward", steps.show(m, Ef.Backward{}, Ef.ladder()), "\n"])

# Running
# -------

# a line that starts with no flag (the empty line after the last) prints
# nothing
def line(model_line: Bool, +ws: List<&2, String>) -> String:
  match model_line:
    case True{}:
      model.show(model(ws))
    case False{}:
      ""

def run(ls: List<&2, String>) -> String:
  match ls:
    case Nil{}:
      ""
    case l <> rest:
      +ws = String.split(l, ' ')
      +c = tok.head(tok.at(ws, 0n))
      String.append(line(Bool.or(Char.is_eq(c, '0'), Char.is_eq(c, '1')), ws), run(rest))

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
    IO.write(run(String.lines(text)))
