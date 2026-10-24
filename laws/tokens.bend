# eukhe: the laws of area tokens

import Base
import ../bend/tokens.bend as Tk
import ../bend/color.bend as Co
import ../bend/ffi_tokens.bend as FT
import ../bend/wire.bend as Wr

# ---- dashboard_tokens ----

# LAWS (T2): the dashboard's presentation tokens. Each law is an open
# claim about the model in bend/tokens.bend; PROOF.bend proves them (as
# Tokens.<law>) with the lemmas of proof/tokens/.

# (T2) Dashboard tokens
# ---------------------
# docs/dashboard.md "Tokens", the model in bend/tokens.bend. The compiled
# core writes its tables into the marked blocks of
# crates/eukhe-dashboard/ui/src/tokens.stylex.ts (entry bend/ffi_tokens.bend,
# laws below).

# LAW tokens_paired: every color token has a value in both modes, light and dark
law tokens_paired:
  for t: Tk.Tone
  for m: Tk.Mode
  {Maybe.is_some(&2, Tk.Col, Tk.find(t, Tk.palette(m))) == True{} : Bool}

# LAW tokens_legible: in both modes, every text pair meets the contrast it needs (4.5:1
# for text, 3:1 for a caption on a fill), as exact rationals
law tokens_legible:
  for m: Tk.Mode
  for +pre: List<&2, Tk.Ink>
  for p: Tk.Ink
  for +post: List<&2, Tk.Ink>
  for split: {Tk.pairs() == List.append(&2, Tk.Ink, pre, p <> post) : List<&2, Tk.Ink>}
  {Tk.readable(m, p) == True{} : Bool}

# LAW tokens_layers_ordered: the stacking layers are strictly ordered, bottom to top
law tokens_layers_ordered:
  {Tk.ascends(Tk.layers()) == True{} : Bool}

# LAW tokens_space_ascends: the spacing scale strictly ascends
law tokens_space_ascends:
  {Tk.ascends(Tk.space()) == True{} : Bool}

# LAW tokens_type_ascends: the type sizes strictly ascend, and so do the line heights
law tokens_type_ascends:
  {Bool.and(Tk.ascends(Tk.sizes()), Tk.ascends(Tk.lines())) == True{} : Bool}

# The entry (bend/ffi_tokens.bend)
# --------------------------------
# The web app's StyleX build needs the token values as literals in
# tokens.stylex.ts, so the compiled core writes the lines that hold them:
# a Rust test checks that the file's generated blocks are this answer.
# The spec below renders the model's tables independently (hex digits by
# a table, decimals by Base's U32.show, alpha by Nat arithmetic).

def spec.hex(n: Nat) -> Char:
  Maybe.default(&2, Char, String.get("0123456789abcdef", n), '?')

def spec.byte(x: U32, rest: String) -> String:
  +n = U32.to_nat(x)
  SCon{spec.hex(Nat.div(n, 16n)), SCon{spec.hex(Nat.mod(n, 16n)), rest}}

def spec.units(u: Nat) -> String:
  match u:
    case 0n:
      ""
    case 1n+k:
      String.from_list([spec.hex(1n+k)])

# an alpha in hundredths: 0.<tens>, then the units digit unless it is 0
def spec.alpha(a: U32) -> String:
  +n = U32.to_nat(a)
  String.concat(["0.", String.from_list([spec.hex(Nat.div(n, 10n))]), spec.units(Nat.mod(n, 10n))])

def spec.css.of(opaque: Bool, +r: U32, +g: U32, +b: U32, a: U32) -> String:
  match opaque:
    case True{}:
      SCon{'#', spec.byte(r, spec.byte(g, spec.byte(b, "")))}
    case False{}:
      String.concat(["rgb(", U32.show(r), " ", U32.show(g), " ", U32.show(b), " / ", spec.alpha(a), ")"])

# a color: opaque (alpha 100) as #rrggbb, a tint as rgb(R G B / alpha)
def spec.css(c: Tk.Col) -> String:
  match c:
    case Tk.Col{Co.Rgb{r, g, b}, +a}:
      spec.css.of(Nat.is_eq(U32.to_nat(a), 100n), r, g, b, a)

def spec.key(k: String, v: String) -> String:
  String.concat(["  ", k, ": ", v, ","])

def spec.palette(es: List<&2, Tk.Entry>) -> List<&2, String>:
  match es:
    case Nil{}:
      Nil{}
    case Tk.Entry{t, c} <> rest:
      spec.key(Tk.Tone.name(t), String.concat(["\"", spec.css(c), "\""])) <> spec.palette(rest)

def spec.px(xs: List<&2, Tk.Step>) -> List<&2, String>:
  match xs:
    case Nil{}:
      Nil{}
    case Tk.Step{n, v} <> rest:
      spec.key(n, String.concat(["\"", U32.show(v), "px\""])) <> spec.px(rest)

def spec.z(xs: List<&2, Tk.Step>) -> List<&2, String>:
  match xs:
    case Nil{}:
      Nil{}
    case Tk.Step{n, v} <> rest:
      spec.key(n, U32.show(v)) <> spec.z(rest)

def spell_lines(ls: List<&2, String>, rest: String) -> String:
  Wr.put_list(~String, ~Wr.put_str, ls, rest)

# the reply: five blocks, each its name and its lines
def spell_blocks() -> String:
  Wr.put_nat(5n, Wr.put_str("lightPalette", spell_lines(spec.palette(Tk.palette(Tk.Light{})), Wr.put_str("darkPalette", spell_lines(spec.palette(Tk.palette(Tk.Dark{})), Wr.put_str("space", spell_lines(spec.px(Tk.space()), Wr.put_str("type", spell_lines(List.append(&2, String, spec.px(Tk.sizes()), spec.px(Tk.lines())), Wr.put_str("layer", spell_lines(spec.z(Tk.layers()), "")))))))))))

# the request s is exactly the one request (tag 0)
def read_req.tag(t: Nat, s: String) -> Bool:
  match t:
    case 0n:
      Wr.end(s)
    case 1n+p:
      False{}

def read_req.go(r: Wr.Dec<Nat>) -> Bool:
  match r:
    case Wr.Got{t, s}:
      read_req.tag(t, s)
    case Wr.Bad{}:
      False{}

def read_req(s: String) -> Bool:
  read_req.go(Wr.get_nat(s))

# LAW tokens_ffi_blocks: the request Rust writes gets the token tables of bend/tokens.bend as the lines of tokens.stylex.ts: both palettes in palette order (opaque colors as #rrggbb, tints as rgb(R G B / 0.A)), the spacing steps, the type sizes then the line heights as px, the layers as z-indexes
law tokens_ffi_blocks:
  {FT.ffi(Wr.put_nat(0n, "")) == spell_blocks() : String}

# LAW tokens_ffi_malformed_exact: every input that is not exactly the one request gets exactly the error form 'E ', then "tokens: malformed request"
law tokens_ffi_malformed_exact:
  for +s: String
  for no: {read_req(s) == False{} : Bool}
  {FT.ffi(s) == SCon{'E', SCon{' ', "tokens: malformed request"}} : String}

# LAW tokens_ffi_example: anchor: the reply's first bytes are the light palette's first lines as the web app writes them; a second tag and input left over are refused
law tokens_ffi_example:
  {String.take(FT.ffi("0,"), 86n) == "5,12,lightPalette17,16,  bg: \"#ffffff\",21,  sidebar: \"#f9f9f9\",20,  raised: \"#ffffff\"," : String} &
  {FT.ffi("1,") == SCon{'E', SCon{' ', "tokens: malformed request"}} : String} &
  {FT.ffi("0,0,") == SCon{'E', SCon{' ', "tokens: malformed request"}} : String}
