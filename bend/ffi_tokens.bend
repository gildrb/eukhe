import Base
import ./wire.bend as W
import ./tokens.bend as Tk
import ./color.bend as Co

# ffi_tokens: the dashboard's token tables (bend/tokens.bend) as the lines
# of crates/eukhe-dashboard/ui/src/tokens.stylex.ts that hold them, an
# entry of the compiled Bend core. The web app's StyleX build needs the
# values as literals in that file, so the core writes them: a Rust test
# checks the file's generated blocks equal this answer, and its ignored
# twin writes them (`make dashboard-tokens`).
# Request: tag 0 (the tables). Reply: a list of blocks, each its name and
# its lines in order:
#   lightPalette, darkPalette  `  <tone>: "<color>",` per tone, palette
#                              order: an opaque color as #rrggbb, a tint
#                              as rgb(R G B / 0.A) (alpha in hundredths,
#                              no trailing zero)
#   space                      `  <step>: "<px>px",`
#   type                       the type sizes, then the line heights, as px
#   layer                      `  <layer>: <z>,`
# Any other input: the error form.

# a generated block of the file: its name and its lines
type Block is Data:
  Block{name: String, lines: List<&2, String>}

# Text
# ----

def hex.dig.at(low: Bool, +d: U32) -> Char:
  match low:
    case True{}:
      Chr{U32.add(48, d)}
    case False{}:
      Chr{U32.add(87, d)}

# a hex digit (0..15), lowercase
def hex.dig(+d: U32) -> Char:
  hex.dig.at(U32.is_lt(d, 10), d)

# a channel (0..255) as two hex digits, then rest
def hex2(+x: U32, rest: String) -> String:
  SCon{hex.dig(U32.div(x, 16)), SCon{hex.dig(U32.mod(x, 16)), rest}}

# the units digit of an alpha, when it is not 0
def alpha.units(zero: Bool, +u: U32, rest: String) -> String:
  match zero:
    case True{}:
      rest
    case False{}:
      SCon{hex.dig(u), rest}

# an alpha in hundredths below 100 as 0.<tens>[<units>]
def alpha(+a: U32, rest: String) -> String:
  +u = U32.mod(a, 10)
  SCon{'0', SCon{'.', SCon{hex.dig(U32.div(a, 10)), alpha.units(U32.is_eq(u, 0), u, rest)}}}

def css.of(opaque: Bool, +r: U32, +g: U32, +b: U32, +a: U32) -> String:
  match opaque:
    case True{}:
      SCon{'#', hex2(r, hex2(g, hex2(b, "")))}
    case False{}:
      String.concat(["rgb(", U32.show(r), " ", U32.show(g), " ", U32.show(b), " / ", alpha(a, ")")])

# a color as the web app writes it
def css(c: Tk.Col) -> String:
  match c:
    case Tk.Col{Co.Rgb{+r, +g, +b}, +a}:
      css.of(U32.is_eq(a, 100), r, g, b, a)

# one key of a block: `  <key>: <value>,`
def line(key: String, value: String) -> String:
  String.concat(["  ", key, ": ", value, ","])

def quoted(v: String) -> String:
  String.concat(["\"", v, "\""])

# Blocks
# ------

def palette.lines(es: List<&2, Tk.Entry>) -> List<&2, String>:
  match es:
    case Nil{}:
      Nil{}
    case Tk.Entry{t, c} <> rest:
      line(Tk.Tone.name(t), quoted(css(c))) <> palette.lines(rest)

def px.lines(xs: List<&2, Tk.Step>) -> List<&2, String>:
  match xs:
    case Nil{}:
      Nil{}
    case Tk.Step{n, v} <> rest:
      line(n, quoted(String.append(U32.show(v), "px"))) <> px.lines(rest)

def z.lines(xs: List<&2, Tk.Step>) -> List<&2, String>:
  match xs:
    case Nil{}:
      Nil{}
    case Tk.Step{n, v} <> rest:
      line(n, U32.show(v)) <> z.lines(rest)

# the generated blocks of tokens.stylex.ts, in file order
def blocks() -> List<&2, Block>:
  [Block{"lightPalette", palette.lines(Tk.palette(Tk.Light{}))}, Block{"darkPalette", palette.lines(Tk.palette(Tk.Dark{}))}, Block{"space", px.lines(Tk.space())}, Block{"type", px.lines(List.append(&2, Tk.Step, Tk.sizes(), Tk.lines()))}, Block{"layer", z.lines(Tk.layers())}]

# The entry
# ---------

def put_block(b: Block, rest: String) -> String:
  match b:
    case Block{n, ls}:
      W.put_str(n, W.put_list(~String, ~W.put_str, ls, rest))

def fail() -> String:
  W.err("tokens: malformed request")

def run.end(whole: Bool) -> String:
  match whole:
    case True{}:
      W.put_list(~Block, ~put_block, blocks(), "")
    case False{}:
      fail()

def run.tag(t: Nat, s: String) -> String:
  match t:
    case 0n:
      run.end(W.end(s))
    case 1n+p:
      fail()

def run(r: W.Dec<Nat>) -> String:
  match r:
    case W.Got{t, s}:
      run.tag(t, s)
    case W.Bad{}:
      fail()

def ffi(input: String) -> String:
  run(W.get_nat(input))
