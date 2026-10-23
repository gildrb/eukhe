# eukhe: the laws of area color

import Base
import ../bend/color.bend as Co

# (T1) Color text, value resolution, file reading, completion, picking
# ---------------------------------------------------------------------
# The rules of crates/eukhe-theme that the user sees: which text is a
# color, how a value follows the variables, the error a broken file
# reports (one per kind, never a default), the palette a file completes
# to, and the theme a name picks with its warnings. Requirements:
# R1 a color is "" (the terminal default), an integer 0-255 (an xterm-256
#    index) or #rrggbb (either case); every other value is an error that
#    names it: "Invalid hex color" for a #-string, "Invalid color value"
#    for the rest.
# R2 any other string names a variable; a missing one is "Variable
#    reference not found: <name>", the first one met twice on the chain is
#    "Circular variable reference detected: <name>".
# R3 a file reports the first error of its colors in key order (a key
#    that names no token: "unknown color token"), then the required tokens
#    it does not write, in token order, then the errors of its export
#    page, card and info backgrounds, in that order.
# R4 a file that reads completes: written tokens keep their value, mdBody
#    falls back to text, the refinement pair and foreground to the
#    builtin of the file's mode, the background to the file's background,
#    export page, user-message surface, default theme's background.
# R5 a name picks as the laws above say; a name that picks no theme
#    warns with the first file that did not load and advertises it (or,
#    no theme object, is named after it); every other file that did not
#    load warns once; a valid file whose name an earlier valid file has
#    clashes with the first of them.
# A1 Rust decodes the JSON (serde) and projects it losslessly: keys in
#    order, each string with the index of the variable it names, numbers
#    and other values as JSON writes them (the projection is glue the
#    Rust tests check, the laws cannot see it).

def th.is(m: Maybe<&2, U32>, +v: U32) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{x}:
      U32.is_eq(x, v)

# every index from v on, k of them, written in decimal reads back
def th.nums(k: Nat, +v: U32) -> Bool:
  match k:
    case 0n:
      True{}
    case 1n+p:
      Bool.and(th.is(Co.num(U32.show(v)), v), th.nums(p, (v + 1 : U32)))

# s has seven characters, the first a #
def th.sharp7(s: String) -> Bool:
  match s:
    case SNil{}:
      False{}
    case SCon{h, s1}:
      match s1:
        case SNil{}:
          False{}
        case SCon{a, s2}:
          match s2:
            case SNil{}:
              False{}
            case SCon{b, s3}:
              match s3:
                case SNil{}:
                  False{}
                case SCon{c, s4}:
                  match s4:
                    case SNil{}:
                      False{}
                    case SCon{d, s5}:
                      match s5:
                        case SNil{}:
                          False{}
                        case SCon{e, s6}:
                          match s6:
                            case SNil{}:
                              False{}
                            case SCon{f, s7}:
                              match s7:
                                case SNil{}:
                                  Char.is_eq(h, '#')
                                case SCon{g, s8}:
                                  False{}

# every xterm-256 color from index i on, k of them, quantizes to its own
# index
def th.fixed(k: Nat, +i: U32) -> Bool:
  match k:
    case 0n:
      True{}
    case 1n+p:
      Bool.and(U32.is_eq(Co.to256(Co.ansi256(i)), i), th.fixed(p, (i + 1 : U32)))

# Color text

# LAW theme_hex_example (R1): the strict #rrggbb form: a # and six hex digits, either case
# EXCLUDES: a parser that accepts #rgb, a missing #, a non-hex digit, a
#   seventh digit, or reads digits in the wrong order or channel
law theme_hex_example:
  {[Co.hex("#0A0b0c"), Co.hex("#abc"), Co.hex("0a0b0c"), Co.hex("#0a0b0g"), Co.hex("#0a0b0c0"), Co.hex("#ffFF00")] == [Some{Co.Rgb{10, 11, 12}}, None{}, None{}, None{}, None{}, Some{Co.Rgb{255, 255, 0}}] : List<&2, Maybe<&2, Co.Rgb>>}

# LAW theme_hex_digits (R1): the hex digits: 0-9, a-f and A-F, and nothing next to them
# EXCLUDES: a digit table with a wrong or missing digit, a case that does
#   not read, a neighbor of a digit range read as a digit
law theme_hex_digits:
  {[Co.hexd('0'), Co.hexd('1'), Co.hexd('2'), Co.hexd('3'), Co.hexd('4'), Co.hexd('5'), Co.hexd('6'), Co.hexd('7'), Co.hexd('8'), Co.hexd('9'), Co.hexd('a'), Co.hexd('b'), Co.hexd('c'), Co.hexd('d'), Co.hexd('e'), Co.hexd('f'), Co.hexd('A'), Co.hexd('B'), Co.hexd('C'), Co.hexd('D'), Co.hexd('E'), Co.hexd('F'), Co.hexd('/'), Co.hexd(':'), Co.hexd('@'), Co.hexd('G'), Co.hexd('`'), Co.hexd('g'), Co.hexd('#'), Co.hexd(' ')] == [Some{0}, Some{1}, Some{2}, Some{3}, Some{4}, Some{5}, Some{6}, Some{7}, Some{8}, Some{9}, Some{10}, Some{11}, Some{12}, Some{13}, Some{14}, Some{15}, Some{10}, Some{11}, Some{12}, Some{13}, Some{14}, Some{15}, None{}, None{}, None{}, None{}, None{}, None{}, None{}, None{}] : List<&2, Maybe<&2, U32>>}

# LAW theme_hex_value (R1): #rrggbb reads as its three channels, each the high digit times 16
# plus the low digit, in the order written
# EXCLUDES: a wrong digit weight, swapped digits or channels
law theme_hex_value:
  for +a1: Char
  for +a2: Char
  for +a3: Char
  for +a4: Char
  for +a5: Char
  for +a6: Char
  for +x1: U32
  for +x2: U32
  for +x3: U32
  for +x4: U32
  for +x5: U32
  for +x6: U32
  for h1: {Co.hexd(a1) == Some{x1} : Maybe<&2, U32>}
  for h2: {Co.hexd(a2) == Some{x2} : Maybe<&2, U32>}
  for h3: {Co.hexd(a3) == Some{x3} : Maybe<&2, U32>}
  for h4: {Co.hexd(a4) == Some{x4} : Maybe<&2, U32>}
  for h5: {Co.hexd(a5) == Some{x5} : Maybe<&2, U32>}
  for h6: {Co.hexd(a6) == Some{x6} : Maybe<&2, U32>}
  {Co.hex(SCon{'#', SCon{a1, SCon{a2, SCon{a3, SCon{a4, SCon{a5, SCon{a6, SNil{}}}}}}}}) == Some{Co.Rgb{(x1 * 16 + x2 : U32), (x3 * 16 + x4 : U32), (x5 * 16 + x6 : U32)}} : Maybe<&2, Co.Rgb>}

# LAW theme_hex_shape (R1): a color is read only from seven characters, the first a #
# EXCLUDES: reading a prefix of a longer text, or text without the #
law theme_hex_shape:
  for +s: String
  for +c: Co.Rgb
  for h: {Co.hex(s) == Some{c} : Maybe<&2, Co.Rgb>}
  {th.sharp7(s) == True{} : Bool}

# LAW theme_num_bytes (R1): every index 0-255, written in decimal, reads back
# EXCLUDES: a wrong digit value, a lost index
law theme_num_bytes:
  {th.nums(128n, 0) == True{} : Bool}

# LAW theme_num_bytes_128 (R1): every index 128-255, written in decimal, reads back (two laws:
# all 256 at once is past the kernel's fuel)
# EXCLUDES: a wrong digit value, a lost index
law theme_num_bytes_128:
  {th.nums(128n, 128) == True{} : Bool}

# LAW theme_num_example (R1): no other number is an index: past 255, signed, fractional,
# leading zeros, empty
# EXCLUDES: wrapping 256 to 0, reading a sign, a fraction or an exponent
law theme_num_example:
  {[Co.num("256"), Co.num("-1"), Co.num("1.5"), Co.num("007"), Co.num(""), Co.num("1000"), Co.num("1e2"), Co.num("255"), Co.num("0")] == [None{}, None{}, None{}, None{}, None{}, None{}, None{}, Some{255}, Some{0}] : List<&2, Maybe<&2, U32>>}

# LAW theme_to256_palette_16: the xterm-256 cube and gray colors (16-255) quantize back to their
# own index; four laws of 60 indices each (one is past the kernel's fuel)
# EXCLUDES: a quantization that misses a palette color
law theme_to256_palette_16:
  {th.fixed(60n, 16) == True{} : Bool}

# LAW theme_to256_palette_76: the palette colors 76-135 quantize back to their own index
# EXCLUDES: a quantization that misses a palette color
law theme_to256_palette_76:
  {th.fixed(60n, 76) == True{} : Bool}

# LAW theme_to256_palette_136: the palette colors 136-195 quantize back to their own index
# EXCLUDES: a quantization that misses a palette color
law theme_to256_palette_136:
  {th.fixed(60n, 136) == True{} : Bool}

# LAW theme_to256_palette_196: the palette colors 196-255 quantize back to their own index
# EXCLUDES: a quantization that misses a palette color
law theme_to256_palette_196:
  {th.fixed(60n, 196) == True{} : Bool}

# LAW theme_contrast_example: the WCAG contrast at its extremes: black on white clears 4.5:1, white
# on black 3:1, a color on itself not even 3:1
# EXCLUDES: a contrast that depends on the order of the pair, or that
#   always passes
law theme_contrast_example:
  {[Co.contrast_ge(Co.Rgb{0, 0, 0}, Co.Rgb{255, 255, 255}, 9, 2), Co.contrast_ge(Co.Rgb{255, 255, 255}, Co.Rgb{0, 0, 0}, 3, 1), Co.contrast_ge(Co.Rgb{255, 255, 255}, Co.Rgb{255, 255, 255}, 3, 1)] == [True{}, True{}, False{}] : List<&2, Bool>}
