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
# The model in bend/tokens.bend. The compiled
# core writes its tables into the marked blocks of
# crates/eukhe-dashboard/ui/src/tokens.stylex.ts (entry bend/ffi_tokens.bend,
# laws below). T2 asks:
#   (a) every color token has a value in both modes, light and dark, each
#       under its own key (tokens_paired, tokens_palette_tones,
#       tokens_names_distinct; the lookup the laws read: tokens_find_first);
#   (b) every text pair the web app draws meets its WCAG 2.x contrast:
#       4.5:1 for text (SC 1.4.3), 3:1 for the tertiary captions on the
#       fills (tokens_legible, tokens_pairs_cover, tokens_readable_wcag);
#   (c) the stacking layers, the spacing scale, the type sizes and the
#       line heights strictly ascend (tokens_layers_ordered,
#       tokens_space_ascends, tokens_type_ascends; the test they read:
#       tokens_ascends_sound), with values a browser keeps exactly
#       (tokens_layers_in_range, tokens_px_in_range, tokens_type_in_range);
#   (d) every value renders as valid CSS (tokens_channels_in_range,
#       tokens_alpha_visible) under a distinct plain key
#       (tokens_scale_keys_distinct, tokens_scale_keys_plain);
#   (e) the reply to the one request Rust writes ("0,") is the generated
#       blocks of tokens.stylex.ts, each line reading back to its table
#       entry (tokens_ffi_reads_back); every other input is refused
#       (tokens_ffi_refuses).
# A1 a legible pair is opaque, so the contrast computed on its colors is
#    the contrast the user sees (tokens_ink_opaque).

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
# The laws read the reply back: as Rust reads it
# (crates/eukhe-bend/src/rules/tokens.rs: a count of blocks, each a name and
# a count of lines, then nothing), with the wire's decoders, then each
# line as CSS, its numbers read back by the place of each digit in
# "0123456789abcdef" (hex) or "0123456789" (decimal) and compared with the
# model's tables. Nothing here renders a value.

# a block as read: its name and its lines
type Shown is Data:
  Shown{name: String, lines: List<&2, String>}

def rd.lines(n: String, r: Wr.Dec<List<&2, String>>) -> Wr.Dec<Shown>:
  match r:
    case Wr.Got{ls, s}:
      Wr.Got{Shown{n, ls}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def rd.name(r: Wr.Dec<String>) -> Wr.Dec<Shown>:
  match r:
    case Wr.Got{n, s}:
      rd.lines(n, Wr.get_list(~String, ~Wr.get_str, s))
    case Wr.Bad{}:
      Wr.Bad{}

# one block: its name, then its lines
def rd.block(s: String) -> Wr.Dec<Shown>:
  rd.name(Wr.get_str(s))

# the value of digit c: its place in ds, None when ds does not hold it
def digit.hit(b: Bool, i: Nat) -> Maybe<&2, Nat>:
  match b:
    case True{}:
      Some{i}
    case False{}:
      None{}

def digit.go(+c: Char, ds: String, +i: Nat) -> Maybe<&2, Nat>:
  match ds:
    case SNil{}:
      None{}
    case SCon{d, rest}:
      Maybe.or(&2, Nat, digit.hit(Char.is_eq(d, c), i), digit.go(c, rest, 1n+i))

def digit(c: Char, ds: String) -> Maybe<&2, Nat>:
  digit.go(c, ds, 0n)

def keep(ok: Bool, s: String) -> Maybe<&2, String>:
  match ok:
    case True{}:
      Some{s}
    case False{}:
      None{}

# what follows p in the text read so far, when it starts with p
def want(+p: String, m: Maybe<&2, String>) -> Maybe<&2, String>:
  match m:
    case None{}:
      None{}
    case Some{+s}:
      keep(String.starts_with(s, p), String.drop(s, String.length(p)))

def dec.sel(d: Maybe<&2, Nat>, stop: Nat & String, more: Nat & String) -> Nat & String:
  match d:
    case None{}:
      stop
    case Some{x}:
      more

# the decimal digits at the head of s read as a number after v, and what
# follows them
def dec.go(s: String, +v: Nat) -> Nat & String:
  match s:
    case SNil{}:
      (v, SNil{})
    case SCon{+c, +t}:
      dec.sel(digit(c, "0123456789"), (v, SCon{c, t}), dec.go(t, Nat.add(Nat.mul(10n, v), Maybe.default(&2, Nat, digit(c, "0123456789"), 0n))))

def dec.got(+n: Nat, r: Nat & String) -> Maybe<&2, String>:
  (v, s) = r
  keep(Nat.is_eq(v, n), s)

def dec.first(+n: Nat, d: Maybe<&2, Nat>, t: String) -> Maybe<&2, String>:
  match d:
    case None{}:
      None{}
    case Some{x}:
      dec.got(n, dec.go(t, x))

# what follows a decimal number (one digit or more) that reads as n
def want_dec(+n: Nat, m: Maybe<&2, String>) -> Maybe<&2, String>:
  match m:
    case None{}:
      None{}
    case Some{s}:
      match s:
        case SNil{}:
          None{}
        case SCon{c, t}:
          dec.first(n, digit(c, "0123456789"), t)

def want_hex.of(+n: Nat, h: Maybe<&2, Nat>, l: Maybe<&2, Nat>, rest: String) -> Maybe<&2, String>:
  match h:
    case None{}:
      None{}
    case Some{x}:
      match l:
        case None{}:
          None{}
        case Some{y}:
          keep(Nat.is_eq(Nat.add(Nat.mul(16n, x), y), n), rest)

# what follows two lowercase hex digits that read as n
def want_hex(+n: Nat, m: Maybe<&2, String>) -> Maybe<&2, String>:
  match m:
    case None{}:
      None{}
    case Some{s}:
      match s:
        case SNil{}:
          None{}
        case SCon{a, t}:
          match t:
            case SNil{}:
              None{}
            case SCon{b, u}:
              want_hex.of(n, digit(a, "0123456789abcdef"), digit(b, "0123456789abcdef"), u)

def want_alpha.two(+n: Nat, +x: Nat, d: Maybe<&2, Nat>, t: String, u: String) -> Maybe<&2, String>:
  match d:
    case None{}:
      keep(Nat.is_eq(Nat.mul(10n, x), n), t)
    case Some{y}:
      keep(Nat.is_eq(Nat.add(Nat.mul(10n, x), y), n), u)

def want_alpha.second(+n: Nat, +x: Nat, s: String) -> Maybe<&2, String>:
  match s:
    case SNil{}:
      keep(Nat.is_eq(Nat.mul(10n, x), n), SNil{})
    case SCon{+c, +u}:
      want_alpha.two(n, x, digit(c, "0123456789"), SCon{c, u}, u)

def want_alpha.first(+n: Nat, d: Maybe<&2, Nat>, t: String) -> Maybe<&2, String>:
  match d:
    case None{}:
      None{}
    case Some{x}:
      want_alpha.second(n, x, t)

def want_alpha.digits(+n: Nat, m: Maybe<&2, String>) -> Maybe<&2, String>:
  match m:
    case None{}:
      None{}
    case Some{s}:
      match s:
        case SNil{}:
          None{}
        case SCon{c, t}:
          want_alpha.first(n, digit(c, "0123456789"), t)

# what follows an alpha 0.D or 0.DD that reads as n hundredths (0.D is D
# tenths)
def want_alpha(+n: Nat, m: Maybe<&2, String>) -> Maybe<&2, String>:
  want_alpha.digits(n, want("0.", m))

def want_if(ok: Bool, m: Maybe<&2, String>) -> Maybe<&2, String>:
  match ok:
    case True{}:
      m
    case False{}:
      None{}

# what follows a CSS color that denotes exactly channels r, g, b and alpha
# a (hundredths): #rrggbb when a is 100, or rgb(R G B / 0.A)
def want_css(+r: Nat, +g: Nat, +b: Nat, +a: Nat, +m: Maybe<&2, String>) -> Maybe<&2, String>:
  Maybe.or(&2, String, want_if(Nat.is_eq(a, 100n), want_hex(b, want_hex(g, want_hex(r, want("#", m))))), want(")", want_alpha(a, want(" / ", want_dec(b, want(" ", want_dec(g, want(" ", want_dec(r, want("rgb(", m))))))))))

def at_end(m: Maybe<&2, String>) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{s}:
      String.is_empty(s)

# line l writes palette entry e: `  <key>: "<css>",`, the tone's key and a
# color that denotes the entry's
def pal_line(l: String, e: Tk.Entry) -> Bool:
  match e:
    case Tk.Entry{t, c}:
      match c:
        case Tk.Col{rgb, a}:
          match rgb:
            case Co.Rgb{r, g, b}:
              at_end(want("\",", want_css(U32.to_nat(r), U32.to_nat(g), U32.to_nat(b), U32.to_nat(a), want(": \"", want(Tk.Tone.name(t), want("  ", Some{l}))))))

# line l writes step x: `  <name>: <v>,` in the layer block (z), else
# `  <name>: "<v>px",`
def step_line(z: Bool, l: String, x: Tk.Step) -> Bool:
  match z:
    case True{}:
      match x:
        case Tk.Step{n, v}:
          at_end(want(",", want_dec(U32.to_nat(v), want(": ", want(n, want("  ", Some{l}))))))
    case False{}:
      match x:
        case Tk.Step{n, v}:
          at_end(want("px\",", want_dec(U32.to_nat(v), want(": \"", want(n, want("  ", Some{l}))))))

# the lines write the entries, one each, in order
def pal_ok(ls: List<&2, String>, es: List<&2, Tk.Entry>) -> Bool:
  match ls:
    case Nil{}:
      List.is_empty(&2, Tk.Entry, es)
    case l <> rest:
      match es:
        case Nil{}:
          False{}
        case e <> more:
          Bool.and(pal_line(l, e), pal_ok(rest, more))

# the lines write the steps, one each, in order
def steps_ok(+z: Bool, ls: List<&2, String>, xs: List<&2, Tk.Step>) -> Bool:
  match ls:
    case Nil{}:
      List.is_empty(&2, Tk.Step, xs)
    case l <> rest:
      match xs:
        case Nil{}:
          False{}
        case x <> more:
          Bool.and(step_line(z, l, x), steps_ok(z, rest, more))

# what a generated block of tokens.stylex.ts holds: a palette, or a scale
# (z: the layer block, z-indexes; else px)
type Wanted is Data:
  WPal{name: String, es: List<&2, Tk.Entry>}
  WSteps{name: String, z: Bool, xs: List<&2, Tk.Step>}

# the generated blocks of tokens.stylex.ts, in file order: the light and
# dark palettes, the spacing steps, the type sizes then the line heights,
# the layers
def wanted() -> List<&2, Wanted>:
  [WPal{"lightPalette", Tk.palette(Tk.Light{})}, WPal{"darkPalette", Tk.palette(Tk.Dark{})}, WSteps{"space", False{}, Tk.space()}, WSteps{"type", False{}, List.append(&2, Tk.Step, Tk.sizes(), Tk.lines())}, WSteps{"layer", True{}, Tk.layers()}]

def block_ok(b: Shown, w: Wanted) -> Bool:
  match b:
    case Shown{n, ls}:
      match w:
        case WPal{wn, es}:
          Bool.and(String.eq(n, wn), pal_ok(ls, es))
        case WSteps{wn, z, xs}:
          Bool.and(String.eq(n, wn), steps_ok(z, ls, xs))

def blocks_ok(bs: List<&2, Shown>, ws: List<&2, Wanted>) -> Bool:
  match bs:
    case Nil{}:
      List.is_empty(&2, Wanted, ws)
    case b <> rest:
      match ws:
        case Nil{}:
          False{}
        case w <> more:
          Bool.and(block_ok(b, w), blocks_ok(rest, more))

def reply_ok(r: Wr.Dec<List<&2, Shown>>) -> Bool:
  match r:
    case Wr.Got{bs, rest}:
      Bool.and(String.is_empty(rest), blocks_ok(bs, wanted()))
    case Wr.Bad{}:
      False{}

# LAW tokens_ffi_reads_back: read as Rust reads it (a count of blocks, each a name and a count of lines, then nothing), the reply to the one request "0," is the generated blocks of tokens.stylex.ts in file order (lightPalette, darkPalette, space, type, layer), and every line reads back to its table entry: a palette line `  <key>: "<css>",` per entry of that mode's palette, in palette order, keyed by the tone's key, whose css (#rrggbb in lowercase hex for alpha 100, else rgb(R G B / 0.A) with decimal channels and the alpha in hundredths) denotes exactly the entry's channels and alpha; a space or type line `  <step>: "<v>px",` per step (the type sizes, then the line heights) and a layer line `  <layer>: <v>,` per layer, its decimal the step's value
# EXCLUDES: a channel or alpha rendered wrong (a hex digit off or swapped,
#   a decimal off, the units digit of an alpha dropped), a tint written as
#   an opaque color, a line keyed by another tone or step, a line or block
#   dropped, added or reordered, a reply Rust reads with input left over
law tokens_ffi_reads_back:
  {reply_ok(Wr.get_list(~Shown, ~rd.block, FT.ffi("0,"))) == True{} : Bool}

# LAW tokens_ffi_refuses: every input other than the one request "0," (tag 0, then nothing) gets exactly the error form 'E ', then "tokens: malformed request"
# EXCLUDES: another tag, a second spelling of tag 0 (a leading zero), input
#   left over after the request, a malformed input answered with the
#   tables or another reply
law tokens_ffi_refuses:
  for +s: String
  for no: {String.eq(s, "0,") == False{} : Bool}
  {FT.ffi(s) == SCon{'E', SCon{' ', "tokens: malformed request"}} : String}

# LAW tokens_ffi_example: anchor: the reply's first bytes are the light palette's first lines as the web app writes them; a second tag and input left over are refused
law tokens_ffi_example:
  {String.take(FT.ffi("0,"), 86n) == "5,12,lightPalette17,16,  bg: \"#ffffff\",21,  sidebar: \"#f9f9f9\",20,  raised: \"#ffffff\"," : String} &
  {FT.ffi("1,") == SCon{'E', SCon{' ', "tokens: malformed request"}} : String} &
  {FT.ffi("0,0,") == SCon{'E', SCon{' ', "tokens: malformed request"}} : String}

# the tones of a palette, in order
def palette_tones(es: List<&2, Tk.Entry>) -> List<&2, Tk.Tone>:
  match es:
    case Nil{}:
      Nil{}
    case Tk.Entry{t, c} <> rest:
      t <> palette_tones(rest)

# LAW tokens_palette_tones: each mode's palette lists every color token exactly once, in the order of lightPalette (bg .. shadowLatest), so every generated block holds every tone
law tokens_palette_tones:
  for m: Tk.Mode
  {palette_tones(Tk.palette(m)) == [Tk.Bg{}, Tk.Sidebar{}, Tk.Raised{}, Tk.Surface{}, Tk.Hover{}, Tk.Primary{}, Tk.Secondary{}, Tk.Tertiary{}, Tk.Hairline{}, Tk.Scrim{}, Tk.Danger{}, Tk.Selection{}, Tk.Scrollbar{}, Tk.ShadowNear{}, Tk.ShadowFar{}, Tk.ShadowDrawer{}, Tk.ShadowLatest{}] : List<&2, Tk.Tone>}

# LAW tokens_ascends_sound: the ascent test the scale laws read accepts a list only when every step's value is below the next step's: wherever two steps stand next to each other in a list it accepts, the first value is below the second
# EXCLUDES: an ascent test that accepts equal or falling neighbours (the
#   scale laws made vacuous: a constant True, a test of the first pair
#   only, a non-strict comparison)
law tokens_ascends_sound:
  for +pre: List<&2, Tk.Step>
  for n: String
  for +v: U32
  for k: String
  for +w: U32
  for post: List<&2, Tk.Step>
  for ok: {Tk.ascends(List.append(&2, Tk.Step, pre, Tk.Step{n, v} <> Tk.Step{k, w} <> post)) == True{} : Bool}
  {U32.is_lt(v, w) == True{} : Bool}

# a and b are the same tone
def tone_same(a: Tk.Tone, b: Tk.Tone) -> Bool:
  match a b:
    case Tk.Bg{} Tk.Bg{}:
      True{}
    case Tk.Sidebar{} Tk.Sidebar{}:
      True{}
    case Tk.Raised{} Tk.Raised{}:
      True{}
    case Tk.Surface{} Tk.Surface{}:
      True{}
    case Tk.Hover{} Tk.Hover{}:
      True{}
    case Tk.Primary{} Tk.Primary{}:
      True{}
    case Tk.Secondary{} Tk.Secondary{}:
      True{}
    case Tk.Tertiary{} Tk.Tertiary{}:
      True{}
    case Tk.Hairline{} Tk.Hairline{}:
      True{}
    case Tk.Scrim{} Tk.Scrim{}:
      True{}
    case Tk.Danger{} Tk.Danger{}:
      True{}
    case Tk.Selection{} Tk.Selection{}:
      True{}
    case Tk.Scrollbar{} Tk.Scrollbar{}:
      True{}
    case Tk.ShadowNear{} Tk.ShadowNear{}:
      True{}
    case Tk.ShadowFar{} Tk.ShadowFar{}:
      True{}
    case Tk.ShadowDrawer{} Tk.ShadowDrawer{}:
      True{}
    case Tk.ShadowLatest{} Tk.ShadowLatest{}:
      True{}
    case _ _:
      False{}

# no entry of es has tone t
def absent(+t: Tk.Tone, es: List<&2, Tk.Entry>) -> Bool:
  match es:
    case Nil{}:
      True{}
    case Tk.Entry{k, c} <> rest:
      Bool.and(Bool.not(tone_same(k, t)), absent(t, rest))

# LAW tokens_find_first: the color of a tone the legibility laws read is its first entry in the palette: in a list whose entries before an entry of tone t have other tones, the lookup of t answers that entry's color
# EXCLUDES: a lookup that answers a later entry, an entry of another tone
#   (the first entry whatever its tone), or nothing for a tone listed
law tokens_find_first:
  for +t: Tk.Tone
  for +pre: List<&2, Tk.Entry>
  for +c: Tk.Col
  for +post: List<&2, Tk.Entry>
  for no: {absent(t, pre) == True{} : Bool}
  {Tk.find(t, List.append(&2, Tk.Entry, pre, Tk.Entry{t, c} <> post)) == Some{c} : Maybe<&2, Tk.Col>}

# the color of tone t in a palette: its first entry
def find_spec.at(hit: Bool, c: Tk.Col, later: Maybe<&2, Tk.Col>) -> Maybe<&2, Tk.Col>:
  match hit:
    case True{}:
      Some{c}
    case False{}:
      later

def find_spec(+t: Tk.Tone, xs: List<&2, Tk.Entry>) -> Maybe<&2, Tk.Col>:
  match xs:
    case Nil{}:
      None{}
    case Tk.Entry{k, c} <> rest:
      find_spec.at(tone_same(k, t), c, find_spec(t, rest))

# LAW tokens_readable_wcag: a pair whose tones have colors x (text) and y (ground) in a mode is readable there exactly when the contrast of x on y is at least 9/2 (4.5:1, WCAG 2.x SC 1.4.3) for text, 3/1 (WCAG 2.x SC 1.4.11) for a caption, whatever the alphas
# EXCLUDES: a weaker or another threshold (3:1 for text, 4.5:1 swapped onto
#   captions), the colors of other tones compared, a constant readable test
#   (tokens_legible made vacuous)
law tokens_readable_wcag:
  for +m: Tk.Mode
  for +fg: Tk.Tone
  for +bg: Tk.Tone
  for +x: Co.Rgb
  for +ax: U32
  for +y: Co.Rgb
  for +ay: U32
  for +hf: {Tk.find(fg, Tk.palette(m)) == Some{Tk.Col{x, ax}} : Maybe<&2, Tk.Col>}
  for +hb: {Tk.find(bg, Tk.palette(m)) == Some{Tk.Col{y, ay}} : Maybe<&2, Tk.Col>}
  {Tk.readable(m, Tk.Ink{fg, bg, Tk.Prose{}}) == Co.contrast_ge(x, y, 9, 2) : Bool} & {Tk.readable(m, Tk.Ink{fg, bg, Tk.Caption{}}) == Co.contrast_ge(x, y, 3, 1) : Bool}

# the pairs the web app draws as text on a ground (the design of
# bend/tokens.bend 2.): primary, secondary and danger text on every ground
# (bg, sidebar, raised, surface, hover); tertiary text on bg, sidebar and
# raised, and as a caption on the fills surface and hover; bg on the
# primary, secondary and danger fills (tooltips, the approval card, the
# send button; a primary button under the pointer; a danger button)
def must_pairs() -> List<&2, Tk.Ink>:
  [Tk.Ink{Tk.Primary{}, Tk.Bg{}, Tk.Prose{}}, Tk.Ink{Tk.Primary{}, Tk.Sidebar{}, Tk.Prose{}}, Tk.Ink{Tk.Primary{}, Tk.Raised{}, Tk.Prose{}}, Tk.Ink{Tk.Primary{}, Tk.Surface{}, Tk.Prose{}}, Tk.Ink{Tk.Primary{}, Tk.Hover{}, Tk.Prose{}}, Tk.Ink{Tk.Secondary{}, Tk.Bg{}, Tk.Prose{}}, Tk.Ink{Tk.Secondary{}, Tk.Sidebar{}, Tk.Prose{}}, Tk.Ink{Tk.Secondary{}, Tk.Raised{}, Tk.Prose{}}, Tk.Ink{Tk.Secondary{}, Tk.Surface{}, Tk.Prose{}}, Tk.Ink{Tk.Secondary{}, Tk.Hover{}, Tk.Prose{}}, Tk.Ink{Tk.Danger{}, Tk.Bg{}, Tk.Prose{}}, Tk.Ink{Tk.Danger{}, Tk.Sidebar{}, Tk.Prose{}}, Tk.Ink{Tk.Danger{}, Tk.Raised{}, Tk.Prose{}}, Tk.Ink{Tk.Danger{}, Tk.Surface{}, Tk.Prose{}}, Tk.Ink{Tk.Danger{}, Tk.Hover{}, Tk.Prose{}}, Tk.Ink{Tk.Tertiary{}, Tk.Bg{}, Tk.Prose{}}, Tk.Ink{Tk.Tertiary{}, Tk.Sidebar{}, Tk.Prose{}}, Tk.Ink{Tk.Tertiary{}, Tk.Raised{}, Tk.Prose{}}, Tk.Ink{Tk.Tertiary{}, Tk.Surface{}, Tk.Caption{}}, Tk.Ink{Tk.Tertiary{}, Tk.Hover{}, Tk.Caption{}}, Tk.Ink{Tk.Bg{}, Tk.Primary{}, Tk.Prose{}}, Tk.Ink{Tk.Bg{}, Tk.Secondary{}, Tk.Prose{}}, Tk.Ink{Tk.Bg{}, Tk.Danger{}, Tk.Prose{}}]

def need_same(a: Tk.Need, b: Tk.Need) -> Bool:
  match a b:
    case Tk.Prose{} Tk.Prose{}:
      True{}
    case Tk.Caption{} Tk.Caption{}:
      True{}
    case _ _:
      False{}

def ink_same(a: Tk.Ink, b: Tk.Ink) -> Bool:
  match a:
    case Tk.Ink{f, g, n}:
      match b:
        case Tk.Ink{f2, g2, n2}:
          Bool.and(tone_same(f, f2), Bool.and(tone_same(g, g2), need_same(n, n2)))

# p is one of ps
def ink_in(+p: Tk.Ink, ps: List<&2, Tk.Ink>) -> Bool:
  match ps:
    case Nil{}:
      False{}
    case q <> rest:
      Bool.or(ink_same(p, q), ink_in(p, rest))

# every pair of xs is one of ys
def inks_within(xs: List<&2, Tk.Ink>, +ys: List<&2, Tk.Ink>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case p <> rest:
      Bool.and(ink_in(p, ys), inks_within(rest, ys))

# LAW tokens_pairs_cover: the pairs the legibility laws check include every pair the web app draws as text on a ground (must_pairs), each with the contrast it needs
# EXCLUDES: a pair dropped from the checked list or checked as a caption
#   when it is text (tokens_legible and tokens_ink_opaque then silent about
#   it), an empty pair list
law tokens_pairs_cover:
  {inks_within(must_pairs(), Tk.pairs()) == True{} : Bool}

# the tone has an opaque color (alpha 100) in the palette
def opaque_spec(m: Maybe<&2, Tk.Col>) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{c}:
      match c:
        case Tk.Col{x, a}:
          U32.is_eq(a, 100)

# both tones of every pair are opaque in the palette es
def inks_opaque(+es: List<&2, Tk.Entry>, ps: List<&2, Tk.Ink>) -> Bool:
  match ps:
    case Nil{}:
      True{}
    case Tk.Ink{fg, bg, n} <> rest:
      Bool.and(Bool.and(opaque_spec(find_spec(fg, es)), opaque_spec(find_spec(bg, es))), inks_opaque(es, rest))

# LAW tokens_ink_opaque: in both modes both tones of every pair that must be legible are opaque, so the contrast the legibility law computes on their colors is the contrast the user sees (a tint over the ground would read lighter)
law tokens_ink_opaque:
  for m: Tk.Mode
  {inks_opaque(Tk.palette(m), Tk.pairs()) == True{} : Bool}

# LAW tokens_names_distinct: every color token is written under its own key, never another token's: two tones with the same key are the same tone
# EXCLUDES: two tokens written under one key (the later line overriding the
#   earlier in the generated object, one token's value lost)
law tokens_names_distinct:
  for +a: Tk.Tone
  for +b: Tk.Tone
  for same: {Tk.Tone.name(a) == Tk.Tone.name(b) : String}
  {a == b : Tk.Tone}

# every channel of every entry is a byte (0..255) and every alpha at most 100
def channels_ok(es: List<&2, Tk.Entry>) -> Bool:
  match es:
    case Nil{}:
      True{}
    case Tk.Entry{t, c} <> rest:
      match c:
        case Tk.Col{rgb, a}:
          match rgb:
            case Co.Rgb{r, g, b}:
              Bool.and(Bool.and(U32.is_le(r, 255), Bool.and(U32.is_le(g, 255), Bool.and(U32.is_le(b, 255), U32.is_le(a, 100)))), channels_ok(rest))

# LAW tokens_channels_in_range: in both modes every color's channels are bytes (0..255) and its alpha at most 100 hundredths, so each renders as a valid #rrggbb or rgb(R G B / 0.A)
law tokens_channels_in_range:
  for m: Tk.Mode
  {channels_ok(Tk.palette(m)) == True{} : Bool}

# the step names of xs
def step_names(xs: List<&2, Tk.Step>) -> List<&2, String>:
  match xs:
    case Nil{}:
      Nil{}
    case Tk.Step{n, v} <> rest:
      n <> step_names(rest)

# no name of ns equals n
def name_absent(+n: String, ns: List<&2, String>) -> Bool:
  match ns:
    case Nil{}:
      True{}
    case x <> rest:
      Bool.and(Bool.not(String.eq(x, n)), name_absent(n, rest))

# the names of ns are distinct
def names_distinct(ns: List<&2, String>) -> Bool:
  match ns:
    case Nil{}:
      True{}
    case +n <> +rest:
      Bool.and(name_absent(n, rest), names_distinct(rest))

# LAW tokens_scale_keys_distinct: every generated block writes each key once: the spacing steps, the layers, and the type sizes with the line heights (one block) have distinct names
law tokens_scale_keys_distinct:
  {Bool.and(names_distinct(step_names(Tk.space())), Bool.and(names_distinct(step_names(Tk.layers())), names_distinct(step_names(List.append(&2, Tk.Step, Tk.sizes(), Tk.lines()))))) == True{} : Bool}

# c is an ASCII letter
def ident.letter(+x: U32) -> Bool:
  Bool.or(Bool.and(U32.is_le(65, x), U32.is_le(x, 90)), Bool.and(U32.is_le(97, x), U32.is_le(x, 122)))

# c is an ASCII letter or digit
def ident.char(c: Char) -> Bool:
  match c:
    case Chr{+x}:
      Bool.or(ident.letter(x), Bool.and(U32.is_le(48, x), U32.is_le(x, 57)))

def ident.rest(s: String) -> Bool:
  match s:
    case SNil{}:
      True{}
    case SCon{c, t}:
      Bool.and(ident.char(c), ident.rest(t))

# s is a plain identifier: a letter, then letters and digits (the key and
# the property name the web app reads are then the same text)
def ident(s: String) -> Bool:
  match s:
    case SNil{}:
      False{}
    case SCon{c, t}:
      match c:
        case Chr{x}:
          Bool.and(ident.letter(x), ident.rest(t))

def idents(ns: List<&2, String>) -> Bool:
  match ns:
    case Nil{}:
      True{}
    case n <> rest:
      Bool.and(ident(n), idents(rest))

# LAW tokens_scale_keys_plain: every scale step name (spacing, layers, type sizes, line heights) is a plain identifier, a letter then letters and digits, so distinct names are distinct keys of the generated blocks
law tokens_scale_keys_plain:
  {idents(step_names(List.append(&2, Tk.Step, Tk.space(), List.append(&2, Tk.Step, Tk.layers(), List.append(&2, Tk.Step, Tk.sizes(), Tk.lines()))))) == True{} : Bool}

# every alpha is at least 1 hundredth (a tint of 0 hides its color and
# renders as 0.0)
def alphas_visible(es: List<&2, Tk.Entry>) -> Bool:
  match es:
    case Nil{}:
      True{}
    case Tk.Entry{t, c} <> rest:
      match c:
        case Tk.Col{rgb, a}:
          Bool.and(U32.is_le(1, a), alphas_visible(rest))

# every value of xs is at most top
def steps_at_most(xs: List<&2, Tk.Step>, +top: U32) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Tk.Step{n, v} <> rest:
      Bool.and(U32.is_le(v, top), steps_at_most(rest, top))

# LAW tokens_alpha_visible: in both modes every color's alpha is 1 to 100 hundredths, so a tint renders as 0.A with no trailing zero and shows its color
law tokens_alpha_visible:
  for m: Tk.Mode
  {alphas_visible(Tk.palette(m)) == True{} : Bool}

# LAW tokens_layers_in_range: every layer is at most 2147483647, the largest z-index a browser keeps, so strictly ascending layers stay strictly ordered on screen
law tokens_layers_in_range:
  {steps_at_most(Tk.layers(), 2147483647) == True{} : Bool}

# LAW tokens_px_in_range: every spacing step, type size and line height is at most 1048576px (2^20), well inside the lengths every browser lays out exactly, so ascending px values stay ascending on screen
law tokens_px_in_range:
  {steps_at_most(List.append(&2, Tk.Step, Tk.space(), List.append(&2, Tk.Step, Tk.sizes(), Tk.lines())), 1048576) == True{} : Bool}

# LAW tokens_type_in_range: every type size and line height is at most 10000px, the largest font size a browser renders, so ascending sizes stay ascending on screen
law tokens_type_in_range:
  {steps_at_most(List.append(&2, Tk.Step, Tk.sizes(), Tk.lines()), 10000) == True{} : Bool}

def spec.hex(n: Nat) -> Char:
  Maybe.default(&2, Char, String.get("0123456789abcdef", n), '?')

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

def spec.byte(x: U32, rest: String) -> String:
  +n = U32.to_nat(x)
  SCon{spec.hex(Nat.div(n, 16n)), SCon{spec.hex(Nat.mod(n, 16n)), rest}}

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

# a block's lines: the line count, then each line as a string. spec.palette
# writes each tone's key with Tk.Tone.name, which tokens_names_exact pins to
# name_spec for every tone; the values are the model's tables, which the
# laws below pin (every tone once, in order; channels, alphas and scales in
# range; the scales ascending; the pairs legible).
def spell_lines(ls: List<&2, String>, rest: String) -> String:
  Wr.put_list(~String, ~Wr.put_str, ls, rest)

# the reply: five blocks, each its name and its lines
def spell_blocks() -> String:
  Wr.put_nat(5n, Wr.put_str("lightPalette", spell_lines(spec.palette(Tk.palette(Tk.Light{})), Wr.put_str("darkPalette", spell_lines(spec.palette(Tk.palette(Tk.Dark{})), Wr.put_str("space", spell_lines(spec.px(Tk.space()), Wr.put_str("type", spell_lines(List.append(&2, String, spec.px(Tk.sizes()), spec.px(Tk.lines())), Wr.put_str("layer", spell_lines(spec.z(Tk.layers()), "")))))))))))

# LAW tokens_ffi_blocks: the request Rust writes gets the token tables of bend/tokens.bend as the lines of tokens.stylex.ts: both palettes in palette order (opaque colors as #rrggbb, tints as rgb(R G B / 0.A)), the spacing steps, the type sizes then the line heights as px, the layers as z-indexes
law tokens_ffi_blocks:
  {FT.ffi(Wr.put_nat(0n, "")) == spell_blocks() : String}

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

# the answer to an input: the token tables when it is exactly the one
# request, else the error form
def spec_entry.of(whole: Bool) -> String:
  match whole:
    case True{}:
      spell_blocks()
    case False{}:
      SCon{'E', SCon{' ', "tokens: malformed request"}}

# LAW tokens_ffi_spec: every input is answered from the spec alone: exactly the one request (tag 0, then nothing) gets the token tables as spell_blocks writes them, every other input exactly the error form 'E ', then "tokens: malformed request"
# EXCLUDES: an input other than the one request answered with the tables
#   (a second spelling of tag 0, input left over), a reply that depends on
#   anything but the input
law tokens_ffi_spec:
  for +s: String
  {FT.ffi(s) == spec_entry.of(read_req(s)) : String}

# each value of xs is below the next one
def ascends_spec(xs: List<&2, Tk.Step>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Tk.Step{n, v} <> rest:
      match rest:
        case Nil{}:
          True{}
        case Tk.Step{+m, +w} <> more:
          Bool.and(U32.is_lt(v, w), ascends_spec(Tk.Step{m, w} <> more))

# LAW tokens_ascends_exact: the ordering the scale laws read is exactly: every step's value is below the next step's
law tokens_ascends_exact:
  for xs: List<&2, Tk.Step>
  {Tk.ascends(xs) == ascends_spec(xs) : Bool}

# A tone's place in the palette type
def idx_spec(t: Tk.Tone) -> Nat:
  match t:
    case Tk.Bg{}:
      0n
    case Tk.Sidebar{}:
      1n
    case Tk.Raised{}:
      2n
    case Tk.Surface{}:
      3n
    case Tk.Hover{}:
      4n
    case Tk.Primary{}:
      5n
    case Tk.Secondary{}:
      6n
    case Tk.Tertiary{}:
      7n
    case Tk.Hairline{}:
      8n
    case Tk.Scrim{}:
      9n
    case Tk.Danger{}:
      10n
    case Tk.Selection{}:
      11n
    case Tk.Scrollbar{}:
      12n
    case Tk.ShadowNear{}:
      13n
    case Tk.ShadowFar{}:
      14n
    case Tk.ShadowDrawer{}:
      15n
    case Tk.ShadowLatest{}:
      16n

def find_spec_orig(+t: Tk.Tone, xs: List<&2, Tk.Entry>) -> Maybe<&2, Tk.Col>:
  match xs:
    case Nil{}:
      None{}
    case Tk.Entry{k, c} <> rest:
      find_spec.at(Nat.is_eq(idx_spec(k), idx_spec(t)), c, find_spec_orig(t, rest))

# LAW tokens_find_exact: the color of a tone the legibility laws read is exactly its first entry in the palette
law tokens_find_exact:
  for +t: Tk.Tone
  for xs: List<&2, Tk.Entry>
  {Tk.find(t, xs) == find_spec_orig(t, xs) : Maybe<&2, Tk.Col>}

# LAW tokens_pairs_exact: the pairs that must be legible are exactly: primary, secondary and danger text on every ground; tertiary on the grounds and as a caption on the fills; the ground's color on the primary, secondary and danger fills
law tokens_pairs_exact:
  {Tk.pairs() == [Tk.Ink{Tk.Primary{}, Tk.Bg{}, Tk.Prose{}}, Tk.Ink{Tk.Primary{}, Tk.Sidebar{}, Tk.Prose{}}, Tk.Ink{Tk.Primary{}, Tk.Raised{}, Tk.Prose{}}, Tk.Ink{Tk.Primary{}, Tk.Surface{}, Tk.Prose{}}, Tk.Ink{Tk.Primary{}, Tk.Hover{}, Tk.Prose{}}, Tk.Ink{Tk.Secondary{}, Tk.Bg{}, Tk.Prose{}}, Tk.Ink{Tk.Secondary{}, Tk.Sidebar{}, Tk.Prose{}}, Tk.Ink{Tk.Secondary{}, Tk.Raised{}, Tk.Prose{}}, Tk.Ink{Tk.Secondary{}, Tk.Surface{}, Tk.Prose{}}, Tk.Ink{Tk.Secondary{}, Tk.Hover{}, Tk.Prose{}}, Tk.Ink{Tk.Danger{}, Tk.Bg{}, Tk.Prose{}}, Tk.Ink{Tk.Danger{}, Tk.Sidebar{}, Tk.Prose{}}, Tk.Ink{Tk.Danger{}, Tk.Raised{}, Tk.Prose{}}, Tk.Ink{Tk.Danger{}, Tk.Surface{}, Tk.Prose{}}, Tk.Ink{Tk.Danger{}, Tk.Hover{}, Tk.Prose{}}, Tk.Ink{Tk.Tertiary{}, Tk.Bg{}, Tk.Prose{}}, Tk.Ink{Tk.Tertiary{}, Tk.Sidebar{}, Tk.Prose{}}, Tk.Ink{Tk.Tertiary{}, Tk.Raised{}, Tk.Prose{}}, Tk.Ink{Tk.Tertiary{}, Tk.Surface{}, Tk.Caption{}}, Tk.Ink{Tk.Tertiary{}, Tk.Hover{}, Tk.Caption{}}, Tk.Ink{Tk.Bg{}, Tk.Primary{}, Tk.Prose{}}, Tk.Ink{Tk.Bg{}, Tk.Secondary{}, Tk.Prose{}}, Tk.Ink{Tk.Bg{}, Tk.Danger{}, Tk.Prose{}}] : List<&2, Tk.Ink>}

# the key of each color token in tokens.stylex.ts (the web app reads the
# tokens by these keys)
def name_spec(t: Tk.Tone) -> String:
  match t:
    case Tk.Bg{}:
      "bg"
    case Tk.Sidebar{}:
      "sidebar"
    case Tk.Raised{}:
      "raised"
    case Tk.Surface{}:
      "surface"
    case Tk.Hover{}:
      "hover"
    case Tk.Primary{}:
      "primary"
    case Tk.Secondary{}:
      "secondary"
    case Tk.Tertiary{}:
      "tertiary"
    case Tk.Hairline{}:
      "hairline"
    case Tk.Scrim{}:
      "scrim"
    case Tk.Danger{}:
      "danger"
    case Tk.Selection{}:
      "selection"
    case Tk.Scrollbar{}:
      "scrollbar"
    case Tk.ShadowNear{}:
      "shadowNear"
    case Tk.ShadowFar{}:
      "shadowFar"
    case Tk.ShadowDrawer{}:
      "shadowDrawer"
    case Tk.ShadowLatest{}:
      "shadowLatest"

# LAW tokens_names_exact: every color token is written under its own key (bg, sidebar, raised, surface, hover, primary, secondary, tertiary, hairline, scrim, danger, selection, scrollbar, shadowNear, shadowFar, shadowDrawer, shadowLatest), never another token's
law tokens_names_exact:
  for t: Tk.Tone
  {Tk.Tone.name(t) == name_spec(t) : String}
