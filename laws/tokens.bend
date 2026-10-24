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
      find_spec.at(Nat.is_eq(idx_spec(k), idx_spec(t)), c, find_spec(t, rest))

# the contrast a pair needs as num/den: text 9/2 (4.5:1), a caption 3/1
def num_spec(n: Tk.Need) -> U32:
  match n:
    case Tk.Prose{}:
      9
    case Tk.Caption{}:
      3

def den_spec(n: Tk.Need) -> U32:
  match n:
    case Tk.Prose{}:
      2
    case Tk.Caption{}:
      1

def readable_spec.of(fg: Maybe<&2, Tk.Col>, bg: Maybe<&2, Tk.Col>, +n: Tk.Need) -> Bool:
  match fg:
    case None{}:
      False{}
    case Some{a}:
      match a:
        case Tk.Col{x, ax}:
          match bg:
            case None{}:
              False{}
            case Some{b}:
              match b:
                case Tk.Col{y, by}:
                  Co.contrast_ge(x, y, num_spec(n), den_spec(n))

# a pair is readable in m: both tones have a color and their contrast meets the need
def readable_spec(+m: Tk.Mode, p: Tk.Ink) -> Bool:
  match p:
    case Tk.Ink{fg, bg, n}:
      readable_spec.of(find_spec(fg, Tk.palette(m)), find_spec(bg, Tk.palette(m)), n)

# LAW tokens_find_exact: the color of a tone the legibility laws read is exactly its first entry in the palette
law tokens_find_exact:
  for +t: Tk.Tone
  for xs: List<&2, Tk.Entry>
  {Tk.find(t, xs) == find_spec(t, xs) : Maybe<&2, Tk.Col>}

# LAW tokens_readable_exact: a pair is readable exactly when both tones have a color and their contrast is at least 9/2 for text, 3/1 for a caption
law tokens_readable_exact:
  for +m: Tk.Mode
  for p: Tk.Ink
  {Tk.readable(m, p) == readable_spec(m, p) : Bool}

# LAW tokens_pairs_exact: the pairs that must be legible are exactly: primary, secondary and danger text on every ground; tertiary on the grounds and as a caption on the fills; the ground's color on the primary, secondary and danger fills
law tokens_pairs_exact:
  {Tk.pairs() == [Tk.Ink{Tk.Primary{}, Tk.Bg{}, Tk.Prose{}}, Tk.Ink{Tk.Primary{}, Tk.Sidebar{}, Tk.Prose{}}, Tk.Ink{Tk.Primary{}, Tk.Raised{}, Tk.Prose{}}, Tk.Ink{Tk.Primary{}, Tk.Surface{}, Tk.Prose{}}, Tk.Ink{Tk.Primary{}, Tk.Hover{}, Tk.Prose{}}, Tk.Ink{Tk.Secondary{}, Tk.Bg{}, Tk.Prose{}}, Tk.Ink{Tk.Secondary{}, Tk.Sidebar{}, Tk.Prose{}}, Tk.Ink{Tk.Secondary{}, Tk.Raised{}, Tk.Prose{}}, Tk.Ink{Tk.Secondary{}, Tk.Surface{}, Tk.Prose{}}, Tk.Ink{Tk.Secondary{}, Tk.Hover{}, Tk.Prose{}}, Tk.Ink{Tk.Danger{}, Tk.Bg{}, Tk.Prose{}}, Tk.Ink{Tk.Danger{}, Tk.Sidebar{}, Tk.Prose{}}, Tk.Ink{Tk.Danger{}, Tk.Raised{}, Tk.Prose{}}, Tk.Ink{Tk.Danger{}, Tk.Surface{}, Tk.Prose{}}, Tk.Ink{Tk.Danger{}, Tk.Hover{}, Tk.Prose{}}, Tk.Ink{Tk.Tertiary{}, Tk.Bg{}, Tk.Prose{}}, Tk.Ink{Tk.Tertiary{}, Tk.Sidebar{}, Tk.Prose{}}, Tk.Ink{Tk.Tertiary{}, Tk.Raised{}, Tk.Prose{}}, Tk.Ink{Tk.Tertiary{}, Tk.Surface{}, Tk.Caption{}}, Tk.Ink{Tk.Tertiary{}, Tk.Hover{}, Tk.Caption{}}, Tk.Ink{Tk.Bg{}, Tk.Primary{}, Tk.Prose{}}, Tk.Ink{Tk.Bg{}, Tk.Secondary{}, Tk.Prose{}}, Tk.Ink{Tk.Bg{}, Tk.Danger{}, Tk.Prose{}}] : List<&2, Tk.Ink>}

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
