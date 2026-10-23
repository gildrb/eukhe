# bridge_screen: runs the interface model (bend/screen.bend) on a
# scenario file and prints what it did, line for line as the Rust bridge
# test prints the Rust code (crates/eukhe-tui/src/view/bridge.rs). Build
# it with
#
#   bend bend/bridge_screen.bend -o <out>
#
# and run `<out> <scenario>`. The first line names the part of the model:
#
#   t            the transcript (`run`), from Tx{[], 0, 0}; one event a
#                line:
#                  o        Open
#                  g X N    Grow{X, N}
#                  f X      Fin{X}
#                  l        Flush
#                  r W      Resize{W}
#                after each it prints
#                  W N|ID:S:LEN ...|ID:LEN ...|F G
#                the width, the next id, the blocks (S is a, f or c), the
#                scrollback (`scroll`), `flushed` and `gapless` (1 or 0)
#   p MIN K      pacing (`pace.step`) at min MIN and share 1/(1+K), from
#                Pace{0, 0}; one event a line: `c N` (Chunk{N}) or `n`
#                (Frame); after each it prints `RECV SHOWN`
#   v            the verify decision (`present`); each line `F G A B`
#                (A, B the two checks, 1 or 0) prints `d F 0` (Drawn{F,
#                False}), `d G 1` (Drawn{G, True}) or `e F` (Error{F})
#   r            the decision after it (`resync` of `present`); each line
#                `F G H A B C` (C the fresh redraw's check) prints `d F 0`
#                (Put{F, False}), `d G 1` (Put{G, True}), `f H` (Fresh{H})
#                or `k F` (Kept{F})
#   s            the layout (`vstack`); each line `Y ROWS H1 H2 ...`
#                prints the rects ` Y:H` of the children, after `s`

import Base
import ./screen.bend as Sc

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

def bit(b: Bool) -> String:
  match b:
    case True{}:
      "1"
    case False{}:
      "0"

# The transcript
# --------------

def tx.ev.of(open: Bool, grow: Bool, fin: Bool, flush: Bool, +a: Nat, b: Nat) -> Sc.Ev:
  match open:
    case True{}:
      Sc.Open{}
    case False{}:
      match grow:
        case True{}:
          Sc.Grow{a, b}
        case False{}:
          match fin:
            case True{}:
              Sc.Fin{a}
            case False{}:
              match flush:
                case True{}:
                  Sc.Flush{}
                case False{}:
                  Sc.Resize{a}

def tx.ev(+c: Char, +ws: List<&2, String>) -> Sc.Ev:
  tx.ev.of(Char.is_eq(c, 'o'), Char.is_eq(c, 'g'), Char.is_eq(c, 'f'), Char.is_eq(c, 'l'), arg(ws, 1n), arg(ws, 2n))

def st.show(s: Sc.St) -> String:
  match s:
    case Sc.Active{}:
      "a"
    case Sc.Final{}:
      "f"
    case Sc.Comm{}:
      "c"

def blk.show(b: Sc.Blk) -> String:
  match b:
    case Sc.Blk{i, s, l}:
      String.concat([Nat.show(i), ":", st.show(s), ":", Nat.show(l)])

def blks.show(bs: List<&2, Sc.Blk>) -> String:
  match bs:
    case Nil{}:
      ""
    case b <> rest:
      match rest:
        case Nil{}:
          blk.show(b)
        case h <> t:
          String.concat([blk.show(b), " ", blks.show(h <> t)])

def line.show(x: Sc.Line) -> String:
  match x:
    case Sc.Line{i, l}:
      String.concat([Nat.show(i), ":", Nat.show(l)])

def lines.show(xs: List<&2, Sc.Line>) -> String:
  match xs:
    case Nil{}:
      ""
    case x <> rest:
      match rest:
        case Nil{}:
          line.show(x)
        case h <> t:
          String.concat([line.show(x), " ", lines.show(h <> t)])

def tx.show(t: Sc.Tx) -> String:
  match t:
    case Sc.Tx{+bs, n, w}:
      String.concat([Nat.show(w), " ", Nat.show(n), "|", blks.show(bs), "|", lines.show(Sc.scroll(bs)), "|", bit(Sc.flushed(bs)), " ", bit(Sc.gapless(bs)), "\n"])

def tx.go(ls: List<&2, String>, +t: Sc.Tx) -> String:
  match ls:
    case Nil{}:
      ""
    case l <> rest:
      +ws = String.split(l, ' ')
      +next = Sc.step(t, tx.ev(tok.head(tok.at(ws, 0n)), ws))
      String.append(tx.show(next), tx.go(rest, next))

# Pacing
# ------

def pace.ev.of(chunk: Bool, n: Nat) -> Sc.PEv:
  match chunk:
    case True{}:
      Sc.Chunk{n}
    case False{}:
      Sc.Frame{}

def pace.ev(+c: Char, n: Nat) -> Sc.PEv:
  pace.ev.of(Char.is_eq(c, 'c'), n)

def pace.show(p: Sc.Pace) -> String:
  match p:
    case Sc.Pace{r, s}:
      String.concat([Nat.show(r), " ", Nat.show(s), "\n"])

def pace.go(ls: List<&2, String>, +min: Nat, +k: Nat, +p: Sc.Pace) -> String:
  match ls:
    case Nil{}:
      ""
    case l <> rest:
      +ws = String.split(l, ' ')
      +next = Sc.pace.step(min, k, p, pace.ev(tok.head(tok.at(ws, 0n)), arg(ws, 1n)))
      String.append(pace.show(next), pace.go(rest, min, k, next))

# The verify decision
# -------------------

def shown.show(s: Sc.Shown) -> String:
  match s:
    case Sc.Drawn{f, full}:
      String.concat(["d ", Nat.show(f), " ", bit(full), "\n"])
    case Sc.Error{f}:
      String.concat(["e ", Nat.show(f), "\n"])

def verify.go(ls: List<&2, String>) -> String:
  match ls:
    case Nil{}:
      ""
    case l <> rest:
      +ws = String.split(l, ' ')
      String.append(shown.show(Sc.present(arg(ws, 0n), arg(ws, 1n), Nat.is_eq(arg(ws, 2n), 1n), Nat.is_eq(arg(ws, 3n), 1n))), verify.go(rest))

# The decision after present
# --------------------------

def paint.show(p: Sc.Paint) -> String:
  match p:
    case Sc.Put{f, full}:
      String.concat(["d ", Nat.show(f), " ", bit(full), "\n"])
    case Sc.Fresh{h}:
      String.concat(["f ", Nat.show(h), "\n"])
    case Sc.Kept{f}:
      String.concat(["k ", Nat.show(f), "\n"])

def resync.go(ls: List<&2, String>) -> String:
  match ls:
    case Nil{}:
      ""
    case l <> rest:
      +ws = String.split(l, ' ')
      +shown = Sc.present(arg(ws, 0n), arg(ws, 1n), Nat.is_eq(arg(ws, 3n), 1n), Nat.is_eq(arg(ws, 4n), 1n))
      String.append(paint.show(Sc.resync(shown, arg(ws, 2n), Nat.is_eq(arg(ws, 5n), 1n))), resync.go(rest))

# The layout
# ----------

def nats(ws: List<&2, String>) -> List<&2, Nat>:
  match ws:
    case Nil{}:
      Nil{}
    case w <> rest:
      tok.nat(w) <> nats(rest)

# the heights: the words after the first two
def heights(ws: List<&2, String>) -> List<&2, Nat>:
  match ws:
    case Nil{}:
      Nil{}
    case a <> r:
      match r:
        case Nil{}:
          Nil{}
        case b <> t:
          nats(t)

def rects.show(rs: List<&2, Sc.Rect>) -> String:
  match rs:
    case Nil{}:
      ""
    case r <> rest:
      match r:
        case Sc.Rect{y, h}:
          String.concat([" ", Nat.show(y), ":", Nat.show(h), rects.show(rest)])

def layout.go(ls: List<&2, String>) -> String:
  match ls:
    case Nil{}:
      ""
    case l <> rest:
      +ws = String.split(l, ' ')
      String.concat(["s", rects.show(Sc.vstack(heights(ws), arg(ws, 0n), arg(ws, 1n))), "\n", layout.go(rest)])

# Running
# -------

def run.part(tx: Bool, pace: Bool, verify: Bool, after: Bool, +ws: List<&2, String>, +rest: List<&2, String>) -> String:
  match tx:
    case True{}:
      tx.go(rest, Sc.Tx{Nil{}, 0n, 0n})
    case False{}:
      match pace:
        case True{}:
          pace.go(rest, arg(ws, 1n), arg(ws, 2n), Sc.Pace{0n, 0n})
        case False{}:
          match verify:
            case True{}:
              verify.go(rest)
            case False{}:
              match after:
                case True{}:
                  resync.go(rest)
                case False{}:
                  layout.go(rest)

def run.kind(+c: Char, +ws: List<&2, String>, +rest: List<&2, String>) -> String:
  run.part(Char.is_eq(c, 't'), Char.is_eq(c, 'p'), Char.is_eq(c, 'v'), Char.is_eq(c, 'r'), ws, rest)

def run(ls: List<&2, String>) -> String:
  match ls:
    case Nil{}:
      ""
    case l <> rest:
      +ws = String.split(l, ' ')
      run.kind(tok.head(tok.at(ws, 0n)), ws, rest)

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
      IO.die(String, 2, "usage: bridge_screen <scenario>")
    case prog <> rest:
      match rest:
        case Nil{}:
          IO.die(String, 2, "usage: bridge_screen <scenario>")
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
