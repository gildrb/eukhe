# eukhe: the laws of area color, section spec: the compiled entry on every
# input, from the specs alone

import Base
import ../../bend/color.bend as Co
import ../../bend/ffi_color.bend as FCo
import ../../bend/wire.bend as Wr
import ./entry.bend as Color
import ./math.bend as ColorMath
import ../../spec/theme/color.bend as Cm

# (T1) The compiled entry, every input
# ------------------------------------
# laws/color/entry.bend (R6) pins the answer to each request Rust spells,
# as bend/color.bend computes it, and the error form. The law here pins the
# answer to every input from the specs alone, never bend/color.bend: the
# request is read with laws/color/entry.bend's reader (the wire primitives,
# co_read_req); each color's xterm-256 index is th.to256 of
# laws/color/math.bend (the nearest cube
# color, or the nearest gray when the color is near-neutral and that gray
# is strictly closer), whether it is light is its WCAG relative luminance
# above one half over the transfer table of spec/theme/color.bend, and the
# palette is th.ansi_any (the 16 ANSI colors, the 6x6x6 cube, the 24
# grays). The requirement is R6 of laws/color/entry.bend.

# the WCAG relative luminance, 0.2126 R + 0.7152 G + 0.0722 B over the
# linear channels of spec/theme/color.bend, in units of 1/100000000
def cx_lum(c: Co.Rgb) -> U32:
  match c:
    case Co.Rgb{r, g, b}:
      (2126 * Cm.lin(r) + 7152 * Cm.lin(g) + 722 * Cm.lin(b) : U32)

# the xterm-256 index of each color, in order, then rest
def cx_idxs(cs: List<&2, Co.Rgb>, rest: String) -> String:
  match cs:
    case Nil{}:
      rest
    case c <> t:
      Wr.put_u32(ColorMath.th.to256(c), cx_idxs(t, rest))

# whether each color is light (its luminance above one half), in order,
# then rest
def cx_lights(cs: List<&2, Co.Rgb>, rest: String) -> String:
  match cs:
    case Nil{}:
      rest
    case c <> t:
      Wr.put_bool(U32.is_gt(cx_lum(c), 50000000), cx_lights(t, rest))

# the colors of the k palette indices from i on, then rest
def cx_table(k: Nat, +i: U32, rest: String) -> String:
  match k:
    case 0n:
      rest
    case 1n+m:
      Color.co_spell_rgb(ColorMath.th.ansi_any(i), cx_table(m, (i + 1 : U32), rest))

# the answer to a request: the count, then each color's index or whether
# it is light; the 256 colors of the palette from index 0
def cx_answer(r: FCo.Req) -> String:
  match r:
    case FCo.Quantize{+cs}:
      Wr.put_nat(List.length(&2, Co.Rgb, cs), cx_idxs(cs, ""))
    case FCo.Lights{+cs}:
      Wr.put_nat(List.length(&2, Co.Rgb, cs), cx_lights(cs, ""))
    case FCo.Table{}:
      Wr.put_nat(256n, cx_table(256n, 0, ""))

# the answer to an input: no whole request, the error form
def cx_entry(m: Maybe<&2, FCo.Req>) -> String:
  match m:
    case None{}:
      Color.co_refused()
    case Some{r}:
      cx_answer(r)

# LAW color_ffi_spec (R6): every input is answered from the spec alone: exactly one request
# (co_read_req) gets the xterm-256 index (th.to256), or whether it is light
# (its WCAG luminance above one half), of each color in order, or the 256
# colors of the palette (th.ansi_any) from index 0; every other input
# exactly the error form "E color: malformed request"
# EXCLUDES: an input other than one whole request answered with a value (a
#   second spelling, input left over), a color quantized, judged or painted
#   otherwise than the spec says, a reply that depends on anything but the
#   input
law color_ffi_spec:
  for +s: String
  {FCo.ffi(s) == cx_entry(Color.co_read_req(s)) : String}
