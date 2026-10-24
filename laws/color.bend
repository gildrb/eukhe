# eukhe: the laws of area color

import Base
import ../bend/color.bend as Co
import ../bend/ffi_color.bend as FCo
import ../bend/wire.bend as Wr
import ./base.bend as LawsBase

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

# The linear channel, light or dark, the xterm-256 palette
# --------------------------------------------------------
# What the HTML export and the terminal UI decide on: the linear channel
# lin (the sRGB transfer function, rounded to 1/10000), light (relative
# luminance above one half) and the xterm-256 palette. The palette's spec
# here builds the cube levels as 0, then 55 + 40 n, and the grays as
# 8 + 10 n; the 16 ANSI colors are the VGA values the terminal UI and the
# HTML export always used (eukhe-theme's former ANSI-16 table).

# every channel from c on, k of them, linearizes above the one before it
def th.rises(k: Nat, +c: U32) -> Bool:
  match k:
    case 0n:
      True{}
    case 1n+p:
      Bool.and(U32.is_lt(Co.lin(c), Co.lin((c + 1 : U32))), th.rises(p, (c + 1 : U32)))

# LAW color_lin_rises: the linear channel rises strictly with the sRGB channel, from 0 to 255
# EXCLUDES: a table entry out of order, two channels that linearize alike
law color_lin_rises:
  {th.rises(255n, 0) == True{} : Bool}

# LAW color_lin_example: anchors of the sRGB transfer function, rounded to 1/10000: the linear
# segment (1, 10), the curve's start (11), 50, 100, middle gray 128, 200,
# 254 and the ends
# EXCLUDES: a table of another transfer function or rounding, a curve that
#   starts at another channel
law color_lin_example:
  {[Co.lin(0), Co.lin(1), Co.lin(10), Co.lin(11), Co.lin(50), Co.lin(100), Co.lin(128), Co.lin(200), Co.lin(254), Co.lin(255)] == [0, 3, 30, 33, 319, 1274, 2159, 5776, 9911, 10000] : List<&2, U32>}

# LAW color_light_example: a gray is light from 188 on (its luminance 0.5029; 187 is 0.4969),
# white is light, black and pure blue are dark, pure green light
# EXCLUDES: light at or below one half, light from the channel sum or from
#   another weighting of the channels
law color_light_example:
  {[Co.light(Co.Rgb{187, 187, 187}), Co.light(Co.Rgb{188, 188, 188}), Co.light(Co.Rgb{255, 255, 255}), Co.light(Co.Rgb{0, 0, 0}), Co.light(Co.Rgb{0, 0, 255}), Co.light(Co.Rgb{0, 255, 0})] == [False{}, True{}, True{}, False{}, False{}, True{}] : List<&2, Bool>}

# the sRGB transfer function of channel c (0-255), in units of 1/10000,
# rounded to nearest: c/255/12.92 up to c/255 = 0.04045, else
# ((c/255 + 0.055)/1.055)^2.4. The table is the formula's value, written
# out by an exact computation (no rounding tie is nearer than 0.0006 of a
# unit); the kernel cannot raise to the 2.4th power.
def th.lin_spec() -> List<&2, U32>:
  [0, 3, 6, 9, 12, 15, 18, 21, 24, 27, 30, 33, 37, 40, 44, 48, 52, 56, 60, 65, 70, 75, 80, 86, 91, 97, 103, 110, 116, 123, 130, 137, 144, 152, 160, 168, 176, 185, 194, 203, 212, 222, 232, 242, 252, 262, 273, 284, 296, 307, 319, 331, 343, 356, 369, 382, 395, 409, 423, 437, 452, 467, 482, 497, 513, 529, 545, 561, 578, 595, 612, 630, 648, 666, 685, 704, 723, 742, 762, 782, 802, 823, 844, 865, 887, 908, 931, 953, 976, 999, 1022, 1046, 1070, 1095, 1119, 1144, 1170, 1195, 1221, 1248, 1274, 1301, 1329, 1356, 1384, 1413, 1441, 1470, 1500, 1529, 1559, 1590, 1620, 1651, 1683, 1714, 1746, 1779, 1812, 1845, 1878, 1912, 1946, 1981, 2016, 2051, 2086, 2122, 2159, 2195, 2232, 2270, 2307, 2346, 2384, 2423, 2462, 2502, 2542, 2582, 2623, 2664, 2705, 2747, 2789, 2831, 2874, 2918, 2961, 3005, 3050, 3095, 3140, 3185, 3231, 3278, 3325, 3372, 3419, 3467, 3515, 3564, 3613, 3663, 3712, 3763, 3813, 3864, 3916, 3968, 4020, 4072, 4125, 4179, 4233, 4287, 4342, 4397, 4452, 4508, 4564, 4621, 4678, 4735, 4793, 4851, 4910, 4969, 5029, 5089, 5149, 5210, 5271, 5333, 5395, 5457, 5520, 5583, 5647, 5711, 5776, 5841, 5906, 5972, 6038, 6105, 6172, 6240, 6308, 6376, 6445, 6514, 6584, 6654, 6724, 6795, 6867, 6939, 7011, 7084, 7157, 7231, 7305, 7379, 7454, 7529, 7605, 7682, 7758, 7835, 7913, 7991, 8070, 8148, 8228, 8308, 8388, 8469, 8550, 8632, 8714, 8796, 8879, 8963, 9047, 9131, 9216, 9301, 9387, 9473, 9560, 9647, 9734, 9823, 9911, 10000]

# every channel from c on, k of them, linearizes as the table says
def th.lins(k: Nat, +c: U32) -> Bool:
  match k:
    case 0n:
      True{}
    case 1n+p:
      Bool.and(U32.is_eq(Co.lin(c), Maybe.default(&2, U32, List.get(&2, U32, th.lin_spec(), U32.to_nat(c)), 0)), th.lins(p, (c + 1 : U32)))

# LAW color_lin_low: the linear channel of 0-127 is the sRGB transfer function, rounded to
# 1/10000 (two laws: 256 at once is a long closed check)
# EXCLUDES: a table entry off by a unit, another transfer function
law color_lin_low:
  {th.lins(128n, 0) == True{} : Bool}

# LAW color_lin_high: the linear channel of 128-255 is the sRGB transfer function, rounded
# EXCLUDES: a table entry off by a unit, another transfer function
law color_lin_high:
  {th.lins(128n, 128) == True{} : Bool}

# the WCAG relative luminance, 0.2126 R + 0.7152 G + 0.0722 B over the
# linear channels, in units of 1/100000000
def th.lum(c: Co.Rgb) -> U32:
  match c:
    case Co.Rgb{r, g, b}:
      (2126 * Co.lin(r) + 7152 * Co.lin(g) + 722 * Co.lin(b) : U32)

# LAW color_light_spec: a color is light exactly when its WCAG relative luminance is above one
# half, for every color; the luminance sums the linear channels as the
# table above rounds them (1/10000), as eukhe always did, so a color within
# about 0.0001 of one half can fall the other way than with exact WCAG
# arithmetic
# EXCLUDES: another weighting of the channels (Rec. 601, a plain mean), a
#   threshold other than one half or at it
law color_light_spec:
  for c: Co.Rgb
  {Co.light(c) == U32.is_gt(th.lum(c), 50000000) : Bool}

# LAW color_light_orange_example: orange (255, 165, 0) is dark: its WCAG luminance is 0.4817 (Rec.
# 601 weights would make it 0.52, light)
# EXCLUDES: Rec. 601 or other luma weights
law color_light_orange_example:
  {Co.light(Co.Rgb{255, 165, 0}) == False{} : Bool}

# the distance of two channels
def th.absd.if(ge: Bool, +a: U32, +b: U32) -> U32:
  match ge:
    case True{}:
      (a - b : U32)
    case False{}:
      (b - a : U32)

def th.absd(+a: U32, +b: U32) -> U32:
  th.absd.if(U32.is_ge(a, b), a, b)

# the distance of v to each value of xs, in order
def th.dists(+v: U32, xs: List<&2, U32>) -> List<&2, U32>:
  match xs:
    case Nil{}:
      Nil{}
    case x <> t:
      th.absd(v, x) <> th.dists(v, t)

def th.pick(c: Bool, a: U32, b: U32) -> U32:
  match c:
    case True{}:
      a
    case False{}:
      b

# the index of the first smallest distance of ds (the first is at index
# at; best, at distance bestd, is the first smallest so far)
def th.first_min(ds: List<&2, U32>, +at: U32, +best: U32, +bestd: U32) -> U32:
  match ds:
    case Nil{}:
      best
    case +d <> t:
      th.first_min(t, (at + 1 : U32), th.pick(U32.is_lt(d, bestd), at, best), th.pick(U32.is_lt(d, bestd), d, bestd))

# the index of the value of xs nearest v: its first smallest distance
def th.nearest(+v: U32, xs: List<&2, U32>) -> U32:
  th.first_min(th.dists(v, xs), 0, 0, 4294967295)

# LAW color_near_spec: the nearest value is the first one at the smallest distance, for every
# value and list
# EXCLUDES: rounding down or up instead of to the nearest, a later value
#   on a tie, a distance measured otherwise
law color_near_spec:
  for +v: U32
  for xs: List<&2, U32>
  {Co.near(v, xs) == th.nearest(v, xs) : U32}

def th.sq(+x: U32) -> U32:
  (x * x : U32)

# the weighted squared distance of two colors: 299, 587 and 114 per mille
# of the squared channel distances
def th.dist(a: Co.Rgb, b: Co.Rgb) -> U32:
  match a b:
    case Co.Rgb{ar, ag, ab} Co.Rgb{br, bg, bb}:
      (299 * th.sq(th.absd(ar, br)) + 587 * th.sq(th.absd(ag, bg)) + 114 * th.sq(th.absd(ab, bb)) : U32)

# LAW color_dist_spec: the distance of two colors weighs the squared channel distances 299,
# 587 and 114 per mille, for every two colors
# EXCLUDES: another weighting, unsquared or swapped channel distances
law color_dist_spec:
  for a: Co.Rgb
  for b: Co.Rgb
  {Co.dist(a, b) == th.dist(a, b) : U32}

def th.levels() -> List<&2, U32>:
  [0, 95, 135, 175, 215, 255]

def th.grays() -> List<&2, U32>:
  [8, 18, 28, 38, 48, 58, 68, 78, 88, 98, 108, 118, 128, 138, 148, 158, 168, 178, 188, 198, 208, 218, 228, 238]

def th.targets() -> List<&2, U32>:
  [8000, 18000, 28000, 38000, 48000, 58000, 68000, 78000, 88000, 98000, 108000, 118000, 128000, 138000, 148000, 158000, 168000, 178000, 188000, 198000, 208000, 218000, 228000, 238000]

def th.at(xs: List<&2, U32>, +i: U32) -> U32:
  Maybe.default(&2, U32, List.get(&2, U32, xs, U32.to_nat(i)), 0)

# the index of r g b given its nearest cube level indices and gray slot:
# the gray (232 + slot) when the color is near-neutral (its channels spread
# below 10) and that gray is strictly closer than the cube color, else the
# cube color (16 + 36 ri + 6 gi + bi)
def th.to256.of(+r: U32, +g: U32, +b: U32, +ri: U32, +gi: U32, +bi: U32, +slot: U32) -> U32:
  +cube = {Co.Rgb{th.at(th.levels(), ri), th.at(th.levels(), gi), th.at(th.levels(), bi)} : Co.Rgb}
  +gv = th.at(th.grays(), slot)
  +spread = (U32.max(r, U32.max(g, b)) - U32.min(r, U32.min(g, b)) : U32)
  th.pick(Bool.and(U32.is_lt(spread, 10), U32.is_lt(th.dist(Co.Rgb{r, g, b}, Co.Rgb{gv, gv, gv}), th.dist(Co.Rgb{r, g, b}, cube))), (232 + slot : U32), (16 + 36 * ri + 6 * gi + bi : U32))

# the xterm-256 index of a color: each channel's nearest cube level, the
# gray nearest its weighted lightness (299 r + 587 g + 114 b)
def th.to256(c: Co.Rgb) -> U32:
  match c:
    case Co.Rgb{+r, +g, +b}:
      th.to256.of(r, g, b, th.nearest(r, th.levels()), th.nearest(g, th.levels()), th.nearest(b, th.levels()), th.nearest((299 * r + 587 * g + 114 * b : U32), th.targets()))

# LAW color_to256_spec: the xterm-256 index of every color: its nearest cube color, or its
# nearest gray when the color is near-neutral and that gray is strictly
# closer
# EXCLUDES: cube levels rounded down or up, the gray chosen for a colored
#   color or on a tie, a gray slot off by one, cube indices in another order
law color_to256_spec:
  for c: Co.Rgb
  {Co.to256(c) == th.to256(c) : U32}

# LAW color_to256_example: anchors: red 250 is the cube's red (196), not 215 (160); a
# near-neutral (160, 155, 164) is the gray 158 (247); white is 231
# EXCLUDES: a reading of color_to256_spec the human did not mean
law color_to256_example:
  {[Co.to256(Co.Rgb{250, 0, 0}), Co.to256(Co.Rgb{160, 155, 164}), Co.to256(Co.Rgb{255, 255, 255})] == [196, 247, 231] : List<&2, U32>} & {FCo.ffi("0,1,250,0,0,") == "1,196," : String}

# the contrast test with the luminances la and lb: the darker plus the
# flare (0.05) times num, at most the lighter plus the flare times den
def th.ratio.if(lt: Bool, +la: U32, +lb: U32, +num: U32, +den: U32) -> Bool:
  match lt:
    case True{}:
      U32.is_le(((la + 5000000) * num : U32), ((lb + 5000000) * den : U32))
    case False{}:
      U32.is_le(((lb + 5000000) * num : U32), ((la + 5000000) * den : U32))

# the WCAG contrast ratio of a and b, (L_light + 0.05) / (L_dark + 0.05),
# is at least num / den
def th.contrast(+a: Co.Rgb, +b: Co.Rgb, +num: U32, +den: U32) -> Bool:
  th.ratio.if(U32.is_lt(th.lum(a), th.lum(b)), th.lum(a), th.lum(b), num, den)

# LAW color_contrast_spec: the contrast test is the WCAG ratio (L_light + 0.05) / (L_dark +
# 0.05) at least num / den, compared exactly on integers, for every two
# colors and ratio
# EXCLUDES: a test that passes any two different colors, the ratio upside
#   down, the flare left out
law color_contrast_spec:
  for +a: Co.Rgb
  for +b: Co.Rgb
  for +num: U32
  for +den: U32
  {Co.contrast_ge(a, b, num, den) == th.contrast(a, b, num, den) : Bool}

# x is a code from lo to hi
def th.within(+x: U32, lo: U32, hi: U32) -> Bool:
  Bool.and(U32.is_ge(x, lo), U32.is_le(x, hi))

def th.hexv.up(upper: Bool, +x: U32) -> Maybe<&2, U32>:
  match upper:
    case True{}:
      Some{(x - 55 : U32)}
    case False{}:
      None{}

def th.hexv.low(lower: Bool, +x: U32) -> Maybe<&2, U32>:
  match lower:
    case True{}:
      Some{(x - 87 : U32)}
    case False{}:
      th.hexv.up(th.within(x, 65, 70), x)

def th.hexv.dec(digit: Bool, +x: U32) -> Maybe<&2, U32>:
  match digit:
    case True{}:
      Some{(x - 48 : U32)}
    case False{}:
      th.hexv.low(th.within(x, 97, 102), x)

# the value of a hex digit: '0'-'9' (codes 48-57) are 0-9, 'a'-'f'
# (97-102) and 'A'-'F' (65-70) are 10-15; every other char is none
def th.hexv(c: Char) -> Maybe<&2, U32>:
  match c:
    case Chr{+x}:
      th.hexv.dec(th.within(x, 48, 57), x)

# LAW color_hexd_spec (R1): every char reads as a hex digit exactly as the spec says: 0-9,
# a-f, A-F their values, every other char none
# EXCLUDES: a char outside the three ranges read as a digit (a "#hhhhhh"
#   read as a color), a digit's value off
law color_hexd_spec:
  for c: Char
  {Co.hexd(c) == th.hexv(c) : Maybe<&2, U32>}

# LAW color_hex_letters_example (R1): anchor: "#hhhhhh" and "#GGGGGG" are no colors
# EXCLUDES: letters past f read as digits
law color_hex_letters_example:
  {[Co.hex("#hhhhhh"), Co.hex("#GGGGGG")] == [None{}, None{}] : List<&2, Maybe<&2, Co.Rgb>>}

def th.ansi16() -> List<&2, Co.Rgb>:
  [Co.Rgb{0, 0, 0}, Co.Rgb{128, 0, 0}, Co.Rgb{0, 128, 0}, Co.Rgb{128, 128, 0}, Co.Rgb{0, 0, 128}, Co.Rgb{128, 0, 128}, Co.Rgb{0, 128, 128}, Co.Rgb{192, 192, 192}, Co.Rgb{128, 128, 128}, Co.Rgb{255, 0, 0}, Co.Rgb{0, 255, 0}, Co.Rgb{255, 255, 0}, Co.Rgb{0, 0, 255}, Co.Rgb{255, 0, 255}, Co.Rgb{0, 255, 255}, Co.Rgb{255, 255, 255}]

def th.level.if(zero: Bool, +n: U32) -> U32:
  match zero:
    case True{}:
      0
    case False{}:
      (55 + 40 * n : U32)

# the cube level n: 0, then 55 + 40 n
def th.level(+n: U32) -> U32:
  th.level.if(U32.is_zero(n), n)

def th.ansi.if(low: Bool, cube: Bool, +i: U32) -> Co.Rgb:
  match low:
    case True{}:
      Maybe.default(&2, Co.Rgb, List.get(&2, Co.Rgb, th.ansi16(), U32.to_nat(i)), Co.Rgb{0, 0, 0})
    case False{}:
      match cube:
        case True{}:
          Co.Rgb{th.level(U32.div((i - 16 : U32), 36)), th.level(U32.mod(U32.div((i - 16 : U32), 6), 6)), th.level(U32.mod((i - 16 : U32), 6))}
        case False{}:
          Co.Rgb{(8 + 10 * (i - 232) : U32), (8 + 10 * (i - 232) : U32), (8 + 10 * (i - 232) : U32)}

# the xterm-256 color of index i: the 16 ANSI colors, the 6x6x6 cube
# (index 16 + 36 r + 6 g + b), the 24 grays
def th.ansi(+i: U32) -> Co.Rgb:
  th.ansi.if(U32.is_lt(i, 16), U32.is_lt(i, 232), i)

# every index from i on, k of them, has its xterm-256 color
def th.ansi_ok(k: Nat, +i: U32) -> Bool:
  match k:
    case 0n:
      True{}
    case 1n+p:
      Bool.and(Co.eq(Co.ansi256(i), th.ansi(i)), th.ansi_ok(p, (i + 1 : U32)))

# LAW color_ansi256_low: the xterm-256 colors of indices 0-127 (two laws: all 256 at once is a
# long closed check)
# EXCLUDES: a wrong ANSI-16 color, a cube level or channel order off
law color_ansi256_low:
  {th.ansi_ok(128n, 0) == True{} : Bool}

# LAW color_ansi256_high: the xterm-256 colors of indices 128-255
# EXCLUDES: a cube level off, a gray ramp off by a step
law color_ansi256_high:
  {th.ansi_ok(128n, 128) == True{} : Bool}

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
