# eukhe: the laws of area color: the compiled entry (T1)

import Base
import ../../bend/color.bend as Co
import ../../bend/ffi_color.bend as FCo
import ../../bend/wire.bend as Wr
import ../base.bend as LawsBase

# (T1) The compiled entry
# -----------------------
# bend/ffi_color.bend runs the color math above for Rust
# (crates/eukhe-bend/src/rules/color.rs): the xterm-256 index a 256-color
# terminal paints for each color (the terminal UI), whether each color is
# light (the HTML export's derived backgrounds), and the xterm-256 palette
# (the terminal UI and the HTML export). The spellers and the reader here
# are made of the wire primitives only (bend/wire.bend, laws/wire.bend).
# R6 every request Rust writes (each channel at most 255, each count
#    within the wire) is answered with bend/color.bend's answer for each
#    color, in order; any other input gets exactly the error form
#    "E color: malformed request"; input after a request is never read as
#    part of it.

# a color, as Rust writes it: its red, green and blue channels
def co_spell_rgb(c: Co.Rgb, rest: String) -> String:
  match c:
    case Co.Rgb{r, g, b}:
      Wr.put_u32(r, Wr.put_u32(g, Wr.put_u32(b, rest)))

def co_spell_rgbs.items(cs: List<&2, Co.Rgb>, rest: String) -> String:
  match cs:
    case Nil{}:
      rest
    case c <> t:
      co_spell_rgb(c, co_spell_rgbs.items(t, rest))

# a list of colors: its count, then each color
def co_spell_rgbs(+cs: List<&2, Co.Rgb>, rest: String) -> String:
  Wr.put_nat(List.length(&2, Co.Rgb, cs), co_spell_rgbs.items(cs, rest))

# a request, as Rust writes it, then rest
def co_spell_req(r: FCo.Req, rest: String) -> String:
  match r:
    case FCo.Quantize{cs}:
      Wr.put_nat(0n, co_spell_rgbs(cs, rest))
    case FCo.Lights{cs}:
      Wr.put_nat(1n, co_spell_rgbs(cs, rest))
    case FCo.Table{}:
      Wr.put_nat(2n, rest)

def co_spell_idxs(cs: List<&2, Co.Rgb>, rest: String) -> String:
  match cs:
    case Nil{}:
      rest
    case c <> t:
      Wr.put_u32(Co.to256(c), co_spell_idxs(t, rest))

def co_spell_lights(cs: List<&2, Co.Rgb>, rest: String) -> String:
  match cs:
    case Nil{}:
      rest
    case c <> t:
      Wr.put_bool(Co.light(c), co_spell_lights(t, rest))

# the colors of the k palette indices from i on
def co_spell_table(k: Nat, +i: U32, rest: String) -> String:
  match k:
    case 0n:
      rest
    case 1n+m:
      co_spell_rgb(Co.ansi256(i), co_spell_table(m, (i + 1 : U32), rest))

# the answer to a request: bend/color.bend's answer per color, in order;
# the 256 colors of the palette, from index 0
def co_spell_answer(r: FCo.Req) -> String:
  match r:
    case FCo.Quantize{+cs}:
      Wr.put_nat(List.length(&2, Co.Rgb, cs), co_spell_idxs(cs, ""))
    case FCo.Lights{+cs}:
      Wr.put_nat(List.length(&2, Co.Rgb, cs), co_spell_lights(cs, ""))
    case FCo.Table{}:
      Wr.put_nat(256n, co_spell_table(256n, 0, ""))

# a color Rust writes: each channel at most 255
def co_fits_rgb(c: Co.Rgb) -> Bool:
  match c:
    case Co.Rgb{r, g, b}:
      Bool.and(U32.is_le(r, 255), Bool.and(U32.is_le(g, 255), U32.is_le(b, 255)))

def co_fits_rgbs(cs: List<&2, Co.Rgb>) -> Bool:
  match cs:
    case Nil{}:
      True{}
    case c <> t:
      Bool.and(co_fits_rgb(c), co_fits_rgbs(t))

# a request Rust writes: every channel at most 255, the count within the
# wire
def co_fits(r: FCo.Req) -> Bool:
  match r:
    case FCo.Quantize{+cs}:
      Bool.and(LawsBase.wire_fits(List.length(&2, Co.Rgb, cs)), co_fits_rgbs(cs))
    case FCo.Lights{+cs}:
      Bool.and(LawsBase.wire_fits(List.length(&2, Co.Rgb, cs)), co_fits_rgbs(cs))
    case FCo.Table{}:
      True{}

# The reader: what a request is, read with the wire's decoders

def co_read_ch.in(ok: Bool, x: U32, s: String) -> Wr.Dec<U32>:
  match ok:
    case True{}:
      Wr.Got{x, s}
    case False{}:
      Wr.Bad{}

def co_read_ch(r: Wr.Dec<U32>) -> Wr.Dec<U32>:
  match r:
    case Wr.Got{+x, s}:
      co_read_ch.in(U32.is_le(x, 255), x, s)
    case Wr.Bad{}:
      Wr.Bad{}

def co_read_rgb.b(r: U32, g: U32, d: Wr.Dec<U32>) -> Wr.Dec<Co.Rgb>:
  match d:
    case Wr.Got{b, s}:
      Wr.Got{Co.Rgb{r, g, b}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def co_read_rgb.g(r: U32, d: Wr.Dec<U32>) -> Wr.Dec<Co.Rgb>:
  match d:
    case Wr.Got{g, s}:
      co_read_rgb.b(r, g, co_read_ch(Wr.get_u32(s)))
    case Wr.Bad{}:
      Wr.Bad{}

def co_read_rgb.r(d: Wr.Dec<U32>) -> Wr.Dec<Co.Rgb>:
  match d:
    case Wr.Got{r, s}:
      co_read_rgb.g(r, co_read_ch(Wr.get_u32(s)))
    case Wr.Bad{}:
      Wr.Bad{}

def co_read_rgb(s: String) -> Wr.Dec<Co.Rgb>:
  co_read_rgb.r(co_read_ch(Wr.get_u32(s)))

def co_read_rgbs.cons(c: Co.Rgb, r: Wr.Dec<List<&2, Co.Rgb>>) -> Wr.Dec<List<&2, Co.Rgb>>:
  match r:
    case Wr.Got{cs, s}:
      Wr.Got{c <> cs, s}
    case Wr.Bad{}:
      Wr.Bad{}

def co_read_rgbs.go(n: Nat, cur: Wr.Dec<Co.Rgb>) -> Wr.Dec<List<&2, Co.Rgb>>:
  match n:
    case 0n:
      match cur:
        case Wr.Got{c, s}:
          Wr.Got{[c], s}
        case Wr.Bad{}:
          Wr.Bad{}
    case 1n+m:
      match cur:
        case Wr.Got{c, s}:
          co_read_rgbs.cons(c, co_read_rgbs.go(m, co_read_rgb(s)))
        case Wr.Bad{}:
          Wr.Bad{}

def co_read_rgbs(r: Wr.Dec<Nat>) -> Wr.Dec<List<&2, Co.Rgb>>:
  match r:
    case Wr.Got{n, s}:
      match n:
        case 0n:
          Wr.Got{Nil{}, s}
        case 1n+m:
          co_read_rgbs.go(m, co_read_rgb(s))
    case Wr.Bad{}:
      Wr.Bad{}

def co_read_quantize(r: Wr.Dec<List<&2, Co.Rgb>>) -> Wr.Dec<FCo.Req>:
  match r:
    case Wr.Got{cs, s}:
      Wr.Got{FCo.Quantize{cs}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def co_read_lights(r: Wr.Dec<List<&2, Co.Rgb>>) -> Wr.Dec<FCo.Req>:
  match r:
    case Wr.Got{cs, s}:
      Wr.Got{FCo.Lights{cs}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def co_read_req.tag(t: Nat, s: String) -> Wr.Dec<FCo.Req>:
  match t:
    case 0n:
      co_read_quantize(co_read_rgbs(Wr.get_nat(s)))
    case 1n:
      co_read_lights(co_read_rgbs(Wr.get_nat(s)))
    case 2n:
      Wr.Got{FCo.Table{}, s}
    case 3n+p:
      Wr.Bad{}

def co_read_req.go(r: Wr.Dec<Nat>) -> Wr.Dec<FCo.Req>:
  match r:
    case Wr.Got{t, s}:
      co_read_req.tag(t, s)
    case Wr.Bad{}:
      Wr.Bad{}

def co_read_req.end(whole: Bool, r: FCo.Req) -> Maybe<&2, FCo.Req>:
  match whole:
    case True{}:
      Some{r}
    case False{}:
      None{}

def co_read_req.whole(d: Wr.Dec<FCo.Req>) -> Maybe<&2, FCo.Req>:
  match d:
    case Wr.Got{r, s}:
      co_read_req.end(Wr.end(s), r)
    case Wr.Bad{}:
      None{}

# the request s is, when s is exactly one request
def co_read_req(s: String) -> Maybe<&2, FCo.Req>:
  co_read_req.whole(co_read_req.go(Wr.get_nat(s)))

# the error form the entry refuses with
def co_refused() -> String:
  SCon{'E', SCon{' ', "color: malformed request"}}

# LAW color_ffi_answers (R6): every request Rust writes is answered with the xterm-256 index, or
# whether it is light, of each color in order, or the 256 colors of the
# xterm-256 palette from index 0, as bend/color.bend says
# EXCLUDES: a channel or a color lost, swapped or reordered; a request
#   answered with another request's rule; a reply spelled otherwise
law color_ffi_answers:
  for +r: FCo.Req
  for fits: {co_fits(r) == True{} : Bool}
  {FCo.ffi(co_spell_req(r, "")) == co_spell_answer(r) : String}

# LAW color_ffi_malformed_exact (R6): every input that is not exactly one request (an unknown tag, a
# channel past 255, a short list, a number past the wire, input left
# over) gets exactly the error form "E color: malformed request"
# EXCLUDES: a default answer, a clamped or wrapped channel, a partial
#   reply to malformed input
law color_ffi_malformed_exact:
  for +s: String
  for no: {co_read_req(s) == None{} : Maybe<&2, FCo.Req>}
  {FCo.ffi(s) == co_refused() : String}

# LAW color_ffi_left_over (R6): a request followed by more input is refused whole
# EXCLUDES: an entry that answers a prefix of its input and drops the rest
law color_ffi_left_over:
  for +r: FCo.Req
  for fits: {co_fits(r) == True{} : Bool}
  for c: Char
  for x: String
  {FCo.ffi(co_spell_req(r, SCon{c, x})) == co_refused() : String}

# LAW color_ffi_example (R6): anchor: the strings Rust sends: red and a dark gray quantized,
# white and black judged light and dark, the palette's first two colors;
# a channel of 256, input left over and an unknown tag refused
# EXCLUDES: a reading of the laws above that the human did not mean
law color_ffi_example:
  {[FCo.ffi("0,2,255,0,0,8,8,8,"), FCo.ffi("1,2,255,255,255,0,0,0,"), FCo.ffi("0,1,256,0,0,"), FCo.ffi("2,x"), FCo.ffi("3,")] == ["2,196,232,", "2,TF", co_refused(), co_refused(), co_refused()] : List<&2, String>}
