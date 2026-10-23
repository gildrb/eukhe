# bridge_tokens: prints the token tables of bend/tokens.bend, line for line
# as crates/eukhe-dashboard/ui/src/tokens.test.ts prints the tokens of
# src/tokens.stylex.ts; the test fails when the two differ. Build it with
#
#   bend bridge/bridge_tokens.bend -o <out>
#
# and run `<out>`. Each line has one space before each item:
#
#   color N LR LG LB LA DR DG DB DA   a color token in palette order: its
#                                     light value, then its dark value
#                                     (channels 0..255, alpha in
#                                     hundredths; `-` for a missing value)
#   layer N Z                         the stacking layers, bottom to top
#   space N PX                        the spacing steps
#   type N PX                         the type sizes
#   line N PX                         the line heights

import Base
import ../bend/tokens.bend as Tk
import ../bend/color.bend as Co

def col.show(c: Maybe<&2, Tk.Col>) -> String:
  match c:
    case None{}:
      " - - - -"
    case Some{Tk.Col{Co.Rgb{r, g, b}, a}}:
      String.concat([" ", U32.show(r), " ", U32.show(g), " ", U32.show(b), " ", U32.show(a)])

def colors(ts: List<&2, Tk.Tone>) -> String:
  match ts:
    case Nil{}:
      ""
    case Con{+t, rest}:
      String.concat(["color ", Tk.Tone.name(t), col.show(Tk.find(t, Tk.palette(Tk.Light{}))), col.show(Tk.find(t, Tk.palette(Tk.Dark{}))), "\n", colors(rest)])

def scale(+kind: String, xs: List<&2, Tk.Step>) -> String:
  match xs:
    case Nil{}:
      ""
    case Con{Tk.Step{n, v}, rest}:
      String.concat([kind, " ", n, " ", U32.show(v), "\n", scale(kind, rest)])

def main() -> IO(Unit):
  do IO<Unit>:
    IO.print(String.concat([colors(Tk.tones()), scale("layer", Tk.layers()), scale("space", Tk.space()), scale("type", Tk.sizes()), scale("line", Tk.lines())]))
