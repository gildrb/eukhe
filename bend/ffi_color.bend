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
# index 0-255 its color's channels (Co.ansi256). Any other input (an
# unknown tag, a channel past 255, a short list, input left over): the
# error form.

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

# the colors of the n palette indices from i on
def put_table(n: Nat, +i: U32, rest: String) -> String:
  match n:
    case 0n:
      rest
    case 1n+m:
      put_rgb(Co.ansi256(i), put_table(m, (i + 1 : U32), rest))

def reply(r: Req) -> String:
  match r:
    case Quantize{+cs}:
      W.put_nat(List.length(&2, Co.Rgb, cs), put_idxs.items(cs, ""))
    case Lights{+cs}:
      W.put_nat(List.length(&2, Co.Rgb, cs), put_lights.items(cs, ""))
    case Table{}:
      W.put_nat(256n, put_table(256n, 0, ""))

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
