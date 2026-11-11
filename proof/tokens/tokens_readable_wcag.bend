# eukhe: the proof of LAW tokens_readable_wcag
# The premises give both lookups; meets then compares the two colors with
# the need's ratio (9/2 text, 3/1 caption), by computation.

import Base
import ../../bend/tokens.bend as Tk
import ../../bend/color.bend as Co
import ../../laws/tokens.bend as Tokens

def trw.one(+m: Tk.Mode, +fg: Tk.Tone, +bg: Tk.Tone, +x: Co.Rgb, +ax: U32, +y: Co.Rgb, +ay: U32, +n: Tk.Need, hf: {Tk.find(fg, Tk.palette(m)) == Some{Tk.Col{x, ax}} : Maybe<&2, Tk.Col>}, hb: {Tk.find(bg, Tk.palette(m)) == Some{Tk.Col{y, ay}} : Maybe<&2, Tk.Col>}) -> {Tk.readable(m, Tk.Ink{fg, bg, n}) == Tk.meets(Some{Tk.Col{x, ax}}, Some{Tk.Col{y, ay}}, n) : Bool}:
  %Equal.sym(Maybe<&2, Tk.Col>, Tk.find(fg, Tk.palette(m)), Some{Tk.Col{x, ax}}, hf) : {Tk.meets(_, Tk.find(bg, Tk.palette(m)), n) == Tk.meets(Some{Tk.Col{x, ax}}, Some{Tk.Col{y, ay}}, n) : Bool}
  %Equal.sym(Maybe<&2, Tk.Col>, Tk.find(bg, Tk.palette(m)), Some{Tk.Col{y, ay}}, hb) : {Tk.meets(Some{Tk.Col{x, ax}}, _, n) == Tk.meets(Some{Tk.Col{x, ax}}, Some{Tk.Col{y, ay}}, n) : Bool}
  {==}

def Tokens.tokens_readable_wcag(m, fg, bg, x, ax, y, ay, hf, hb):
  (trw.one(m, fg, bg, x, ax, y, ay, Tk.Prose{}, hf, hb), trw.one(m, fg, bg, x, ax, y, ay, Tk.Caption{}, hf, hb))
