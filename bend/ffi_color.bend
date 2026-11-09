import Base
import ./wire.bend as W
import ./color.bend as Co

# ffi_color: the color math of the themes (bend/color.bend: the
# quantization to the xterm-256 palette, light or dark, the xterm-256
# palette) as an entry of the compiled Bend core
# (crates/eukhe-bend/src/rules/color.rs). Request: a tag, then
#   0  quantize: a count, then per color its channels r g b (each a U32,
#      at most 255)
#   1  lights: the same colors
#   2  the xterm-256 palette: nothing
# Reply: quantize: a count, then per color the xterm-256 index a
# 256-color terminal paints for it (Co.to256); lights: a count, then per
# color T (light: Co.light) or F; the palette: a count (256), then per
# index 0-255 its color's channels (Co.ansi256, written here from its
# parts in index order: the 16 ANSI colors, the cube, the grays). Any
# other input (an unknown tag, a channel past 255, a short list, input
# left over): the error form.

type Req is Data:
  Quantize{cs: List<&2, Co.Rgb>}
  Lights{cs: List<&2, Co.Rgb>}
  Table{}

# Decoding
# --------

def get_ch.in(ok: Bool, x: U32, s: String) -> W.Dec<U32>:
  match ok:
    case True{}:
      W.Got{x, s}
    case False{}:
      W.Bad{}

# a channel: a U32 of at most 255
def get_ch(r: W.Dec<U32>) -> W.Dec<U32>:
  match r:
    case W.Got{+x, s}:
      get_ch.in(U32.is_le(x, 255), x, s)
    case W.Bad{}:
      W.Bad{}

def get_rgb.b(r: U32, g: U32, d: W.Dec<U32>) -> W.Dec<Co.Rgb>:
  match d:
    case W.Got{b, s}:
      W.Got{Co.Rgb{r, g, b}, s}
    case W.Bad{}:
      W.Bad{}

def get_rgb.g(r: U32, d: W.Dec<U32>) -> W.Dec<Co.Rgb>:
  match d:
    case W.Got{g, s}:
      get_rgb.b(r, g, get_ch(W.get_u32(s)))
    case W.Bad{}:
      W.Bad{}

def get_rgb.r(d: W.Dec<U32>) -> W.Dec<Co.Rgb>:
  match d:
    case W.Got{r, s}:
      get_rgb.g(r, get_ch(W.get_u32(s)))
    case W.Bad{}:
      W.Bad{}

# a color: its red, green and blue channels
def get_rgb(s: String) -> W.Dec<Co.Rgb>:
  get_rgb.r(get_ch(W.get_u32(s)))

def get_rgbs.cons(c: Co.Rgb, r: W.Dec<List<&2, Co.Rgb>>) -> W.Dec<List<&2, Co.Rgb>>:
  match r:
    case W.Got{cs, s}:
      W.Got{c <> cs, s}
    case W.Bad{}:
      W.Bad{}

# the first color cur, then n more
def get_rgbs.go(n: Nat, cur: W.Dec<Co.Rgb>) -> W.Dec<List<&2, Co.Rgb>>:
  match n:
    case 0n:
      match cur:
        case W.Got{c, s}:
          W.Got{[c], s}
        case W.Bad{}:
          W.Bad{}
    case 1n+m:
      match cur:
        case W.Got{c, s}:
          get_rgbs.cons(c, get_rgbs.go(m, get_rgb(s)))
        case W.Bad{}:
          W.Bad{}

# a list of colors: its count, then each color
def get_rgbs(r: W.Dec<Nat>) -> W.Dec<List<&2, Co.Rgb>>:
  match r:
    case W.Got{n, s}:
      match n:
        case 0n:
          W.Got{Nil{}, s}
        case 1n+m:
          get_rgbs.go(m, get_rgb(s))
    case W.Bad{}:
      W.Bad{}

def get_quantize(r: W.Dec<List<&2, Co.Rgb>>) -> W.Dec<Req>:
  match r:
    case W.Got{cs, s}:
      W.Got{Quantize{cs}, s}
    case W.Bad{}:
      W.Bad{}

def get_lights(r: W.Dec<List<&2, Co.Rgb>>) -> W.Dec<Req>:
  match r:
    case W.Got{cs, s}:
      W.Got{Lights{cs}, s}
    case W.Bad{}:
      W.Bad{}

def get_req.tag(t: Nat, s: String) -> W.Dec<Req>:
  match t:
    case 0n:
      get_quantize(get_rgbs(W.get_nat(s)))
    case 1n:
      get_lights(get_rgbs(W.get_nat(s)))
    case 2n:
      W.Got{Table{}, s}
    case 3n+p:
      W.Bad{}

def get_req.go(r: W.Dec<Nat>) -> W.Dec<Req>:
  match r:
    case W.Got{t, s}:
      get_req.tag(t, s)
    case W.Bad{}:
      W.Bad{}

# Replies
# -------

def put_idxs.items(cs: List<&2, Co.Rgb>, rest: String) -> String:
  match cs:
    case Nil{}:
      rest
    case c <> t:
      W.put_u32(Co.to256(c), put_idxs.items(t, rest))

def put_lights.items(cs: List<&2, Co.Rgb>, rest: String) -> String:
  match cs:
    case Nil{}:
      rest
    case c <> t:
      W.put_bool(Co.light(c), put_lights.items(t, rest))

def put_rgb(c: Co.Rgb, rest: String) -> String:
  match c:
    case Co.Rgb{r, g, b}:
      W.put_u32(r, W.put_u32(g, W.put_u32(b, rest)))

# each color of cs
def put_rgbs(cs: List<&2, Co.Rgb>, rest: String) -> String:
  match cs:
    case Nil{}:
      rest
    case c <> t:
      put_rgb(c, put_rgbs(t, rest))

# the cube colors with red level r and green level g, one per blue level of bs
def put_cube.b(+r: U32, +g: U32, bs: List<&2, U32>, rest: String) -> String:
  match bs:
    case Nil{}:
      rest
    case b <> t:
      put_rgb(Co.Rgb{r, g, b}, put_cube.b(r, g, t, rest))

# the cube colors with red level r, one row per green level of gs
def put_cube.g(+r: U32, gs: List<&2, U32>, rest: String) -> String:
  match gs:
    case Nil{}:
      rest
    case g <> t:
      put_cube.b(r, g, Co.levels(), put_cube.g(r, t, rest))

# the 6x6x6 cube (palette indices 16-231: red slowest, blue fastest), one
# plane per red level of rs
def put_cube(rs: List<&2, U32>, rest: String) -> String:
  match rs:
    case Nil{}:
      rest
    case r <> t:
      put_cube.g(r, Co.levels(), put_cube(t, rest))

# the grays (palette indices 232-255), one per level of gs
def put_grays(gs: List<&2, U32>, rest: String) -> String:
  match gs:
    case Nil{}:
      rest
    case +g <> t:
      put_rgb(Co.Rgb{g, g, g}, put_grays(t, rest))

# the colors of the 256 palette indices, in order
def put_table(rest: String) -> String:
  put_rgbs(Co.ansi16(), put_cube(Co.levels(), put_grays(Co.grays(), rest)))

def reply(r: Req) -> String:
  match r:
    case Quantize{+cs}:
      W.put_nat(List.length(&2, Co.Rgb, cs), put_idxs.items(cs, ""))
    case Lights{+cs}:
      W.put_nat(List.length(&2, Co.Rgb, cs), put_lights.items(cs, ""))
    case Table{}:
      W.put_nat(256n, put_table(""))

# Running
# -------

def refuse() -> String:
  W.err("color: malformed request")

def run.end(whole: Bool, r: Req) -> String:
  match whole:
    case True{}:
      reply(r)
    case False{}:
      refuse()

def run(d: W.Dec<Req>) -> String:
  match d:
    case W.Got{r, s}:
      run.end(W.end(s), r)
    case W.Bad{}:
      refuse()

def ffi(input: String) -> String:
  run(get_req.go(W.get_nat(input)))
