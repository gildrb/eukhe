# eukhe: the laws of area color: the linear channel, light or dark, the palette, every color function

import Base
import ../../bend/color.bend as Co
import ../../bend/ffi_color.bend as FCo
import ../../spec/theme/color.bend as Cm

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

# LAW color_lum_grey: a gray's luminance is its linear channel: for every channel c,
# Rgb(c, c, c) has luminance 10000 lin(c) (units of 1/100000000), the three
# channel weights sum to one (WCAG 2.x relative luminance:
# https://www.w3.org/TR/WCAG22/#dfn-relative-luminance)
# EXCLUDES: weights that do not sum to one, an offset folded into the
#   luminance, a gray read from one channel or a channel mean that rounds
law color_lum_grey:
  for +c: U32
  {Co.lum(Co.Rgb{c, c, c}) == (10000 * Co.lin(c) : U32) : U32}

# LAW color_lum_order: one channel alone weighs green most, then red, then blue: for every
# channel c, the luminance of Rgb(0, 0, c) is at most that of Rgb(c, 0, 0),
# which is at most that of Rgb(0, c, 0) (WCAG's 0.0722 < 0.2126 < 0.7152)
# EXCLUDES: swapped channels, the weights in another order
law color_lum_order:
  for +c: U32
  {Bool.and(U32.is_le(Co.lum(Co.Rgb{0, 0, c}), Co.lum(Co.Rgb{c, 0, 0})), U32.is_le(Co.lum(Co.Rgb{c, 0, 0}), Co.lum(Co.Rgb{0, c, 0}))) == True{} : Bool}

# LAW color_lum_rises: the luminance never falls where no linear channel falls: for every two
# colors whose red, green and blue each linearize at least as high in the
# second, the second's luminance is at least the first's; with
# color_lin_rises, raising any channel of a color (0 to 255) never lowers
# its luminance
# EXCLUDES: a negative weight, a term that falls as its channel rises, a
#   sum or product that wraps past 2^32
law color_lum_rises:
  for +r: U32
  for +g: U32
  for +b: U32
  for +r2: U32
  for +g2: U32
  for +b2: U32
  for hr: {U32.is_le(Co.lin(r), Co.lin(r2)) == True{} : Bool}
  for hg: {U32.is_le(Co.lin(g), Co.lin(g2)) == True{} : Bool}
  for hb: {U32.is_le(Co.lin(b), Co.lin(b2)) == True{} : Bool}
  {U32.is_le(Co.lum(Co.Rgb{r, g, b}), Co.lum(Co.Rgb{r2, g2, b2})) == True{} : Bool}

# LAW color_lum_wcag_example: anchors from the WCAG 2.x relative luminance
# (https://www.w3.org/TR/WCAG22/#dfn-relative-luminance, computed with the
# exact transfer function, not lin's table): the primaries are exactly
# 0.2126, 0.7152 and 0.0722; gray 128 is 0.21586050, #336699 0.12506457 and
# orange (255, 165, 0) 0.48170267, each matched within 0.00005 (lin rounds
# each channel to 1/10000, so the weighted sum is off by at most half that)
# EXCLUDES: another weighting of the channels, swapped channels, another
#   transfer function
law color_lum_wcag_example:
  {[Co.lum(Co.Rgb{255, 0, 0}), Co.lum(Co.Rgb{0, 255, 0}), Co.lum(Co.Rgb{0, 0, 255})] == [21260000, 71520000, 7220000] : List<&2, U32>} & {[Bool.and(U32.is_le(21581050, Co.lum(Co.Rgb{128, 128, 128})), U32.is_le(Co.lum(Co.Rgb{128, 128, 128}), 21591050)), Bool.and(U32.is_le(12501457, Co.lum(Co.Rgb{51, 102, 153})), U32.is_le(Co.lum(Co.Rgb{51, 102, 153}), 12511457)), Bool.and(U32.is_le(48165267, Co.lum(Co.Rgb{255, 165, 0})), U32.is_le(Co.lum(Co.Rgb{255, 165, 0}), 48175267))] == [True{}, True{}, True{}] : List<&2, Bool>}

# LAW color_contrast_wcag_example: the contrast ratios WCAG documents
# (https://www.w3.org/TR/WCAG22/#dfn-contrast-ratio: "ratios can range from
# 1 to 21"): black on white, either way round, is exactly 21:1 (it meets
# 21/1 but not 21.00001), which holds only with the flare 0.05; gray
# #767676 on white is 4.54:1 and meets AA's 4.5:1, #777777 is 4.48:1 and
# does not (the WCAG formula, as WebAIM's contrast checker reports)
# EXCLUDES: a flare other than 0.05 or none, the ratio upside down, a
#   threshold met by rounding
law color_contrast_wcag_example:
  {[Co.contrast_ge(Co.Rgb{0, 0, 0}, Co.Rgb{255, 255, 255}, 21, 1), Co.contrast_ge(Co.Rgb{255, 255, 255}, Co.Rgb{0, 0, 0}, 21, 1), Co.contrast_ge(Co.Rgb{0, 0, 0}, Co.Rgb{255, 255, 255}, 2100001, 100000), Co.contrast_ge(Co.Rgb{118, 118, 118}, Co.Rgb{255, 255, 255}, 9, 2), Co.contrast_ge(Co.Rgb{119, 119, 119}, Co.Rgb{255, 255, 255}, 9, 2)] == [True{}, True{}, False{}, True{}, False{}] : List<&2, Bool>}

# LAW color_flare_example: anchors: the luminance of black, white and (128, 64, 200) is 0, 1 and
# 0.12429282; plus the flare, 0.05, 1.05 and 0.17429282
# EXCLUDES: a flare other than 0.05 or folded into the luminance, a
#   luminance off at these colors
law color_flare_example:
  {[Co.lum(Co.Rgb{0, 0, 0}), Co.lum(Co.Rgb{255, 255, 255}), Co.lum(Co.Rgb{128, 64, 200}), (Co.lum(Co.Rgb{0, 0, 0}) + Co.flare() : U32), (Co.lum(Co.Rgb{255, 255, 255}) + Co.flare() : U32), (Co.lum(Co.Rgb{128, 64, 200}) + Co.flare() : U32)] == [0, 100000000, 12429282, 5000000, 105000000, 17429282] : List<&2, U32>}

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

# every channel of c is at most 255 (a color the entries read or paint)
def th.byte3(c: Co.Rgb) -> Bool:
  match c:
    case Co.Rgb{r, g, b}:
      Bool.and(U32.is_le(r, 255), Bool.and(U32.is_le(g, 255), U32.is_le(b, 255)))

# LAW color_dist_spec: the distance of two colors weighs the squared channel distances 299,
# 587 and 114 per mille, for every two colors with channels at most 255
# (the sum stays below 2^32 there, so the spec's U32 arithmetic is exact)
# EXCLUDES: another weighting, unsquared or swapped channel distances
law color_dist_spec:
  for a: Co.Rgb
  for b: Co.Rgb
  for bytes: {Bool.and(th.byte3(a), th.byte3(b)) == True{} : Bool}
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

# LAW color_to256_spec: the xterm-256 index of every color with channels at most 255 (the
# colors the entries read or paint; the spec's U32 sums stay below 2^32
# there): its nearest cube color, or its nearest gray when the color is
# near-neutral and that gray is strictly closer
# EXCLUDES: cube levels rounded down or up, the gray chosen for a colored
#   color or on a tie, a gray slot off by one, cube indices in another order
law color_to256_spec:
  for c: Co.Rgb
  for bytes: {th.byte3(c) == True{} : Bool}
  {Co.to256(c) == th.to256(c) : U32}

# LAW color_to256_example: anchors: red 250 is the cube's red (196), not 215 (160); a
# near-neutral (160, 155, 164) is the gray 158 (247); white is 231
# EXCLUDES: a reading of color_to256_spec the human did not mean
law color_to256_example:
  {[Co.to256(Co.Rgb{250, 0, 0}), Co.to256(Co.Rgb{160, 155, 164}), Co.to256(Co.Rgb{255, 255, 255})] == [196, 247, 231] : List<&2, U32>} & {FCo.ffi("0,1,250,0,0,") == "1,196," : String}

# the contrast test with the luminances la and lb: the darker plus the
# flare (0.05) times num, at most the lighter plus the flare times den; a
# luminance is at most 1e8 and num, den at most 40 (the law's domain), so
# no product passes 2^32: the comparison is exact
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
# colors and every ratio of terms up to 40 (the ratios the themes ask:
# 9/2, 3/1); past 40 the anchors of color_contrast_no_wrap_example
# EXCLUDES: a test that passes any two different colors, the ratio upside
#   down, the flare left out
law color_contrast_spec:
  for +a: Co.Rgb
  for +b: Co.Rgb
  for +num: U32
  for +den: U32
  for small: {Bool.and(U32.is_le(num, 40), U32.is_le(den, 40)) == True{} : Bool}
  {Co.contrast_ge(a, b, num, den) == th.contrast(a, b, num, den) : Bool}

# LAW color_contrast_no_wrap_example: past terms of 40 the test stays exact: white on white (1:1)
# meets neither 45/10 nor 41/40 but meets 40/40; black on white (21:1)
# meets 41/40 and 4200000000/200000000 (21:1) but not 4200000001/200000000
# EXCLUDES: contrast arithmetic that wraps past 2^32
law color_contrast_no_wrap_example:
  {[Co.contrast_ge(Co.Rgb{255, 255, 255}, Co.Rgb{255, 255, 255}, 45, 10), Co.contrast_ge(Co.Rgb{255, 255, 255}, Co.Rgb{255, 255, 255}, 41, 40), Co.contrast_ge(Co.Rgb{255, 255, 255}, Co.Rgb{255, 255, 255}, 40, 40), Co.contrast_ge(Co.Rgb{0, 0, 0}, Co.Rgb{255, 255, 255}, 41, 40), Co.contrast_ge(Co.Rgb{0, 0, 0}, Co.Rgb{255, 255, 255}, 4200000000, 200000000), Co.contrast_ge(Co.Rgb{0, 0, 0}, Co.Rgb{255, 255, 255}, 4200000001, 200000000)] == [False{}, False{}, True{}, True{}, True{}, False{}] : List<&2, Bool>}

# the exact contrast test with the luminances la and lb, on naturals: the
# darker plus the flare (0.05) times num, at most the lighter plus the
# flare times den (a luminance is at most 1e8, so its sum with the flare
# stays far below 2^32)
def th.exact.if(lt: Bool, +la: U32, +lb: U32, +num: U32, +den: U32) -> Bool:
  match lt:
    case True{}:
      Nat.is_le(Nat.mul(U32.to_nat((la + 5000000 : U32)), U32.to_nat(num)), Nat.mul(U32.to_nat((lb + 5000000 : U32)), U32.to_nat(den)))
    case False{}:
      Nat.is_le(Nat.mul(U32.to_nat((lb + 5000000 : U32)), U32.to_nat(num)), Nat.mul(U32.to_nat((la + 5000000 : U32)), U32.to_nat(den)))

# the WCAG contrast ratio of a and b, (L_light + 0.05) / (L_dark + 0.05),
# is at least num / den, compared on naturals, for every ratio
def th.contrast_exact(+a: Co.Rgb, +b: Co.Rgb, +num: U32, +den: U32) -> Bool:
  th.exact.if(U32.is_lt(th.lum(a), th.lum(b)), th.lum(a), th.lum(b), num, den)

# LAW color_contrast_exact_wide: past terms of 40 the contrast test is exact for every U32 ratio:
# (L_dark + 0.05)·num <= (L_light + 0.05)·den on naturals
# EXCLUDES: contrast arithmetic that wraps, drops a carry or a partial
#   product past 2^32 (the old mul64 carry bug class)
law color_contrast_exact_wide:
  for +a: Co.Rgb
  for +b: Co.Rgb
  for +num: U32
  for +den: U32
  for wide: {Bool.and(U32.is_le(num, 40), U32.is_le(den, 40)) == False{} : Bool}
  {Co.contrast_ge(a, b, num, den) == th.contrast_exact(a, b, num, den) : Bool}

# LAW color_contrast_carry_example: at the old carry bug's inputs: white on white (1:1) meets
# 65536/65537 and 65536/65536 but not 65537/65536; black on white (21:1)
# meets 1376256/65536 (21:1) but not 1376257/65536
# EXCLUDES: a contrast past 2^16 that adds or drops a carry of the
#   partial products
law color_contrast_carry_example:
  {[Co.contrast_ge(Co.Rgb{255, 255, 255}, Co.Rgb{255, 255, 255}, 65536, 65537), Co.contrast_ge(Co.Rgb{255, 255, 255}, Co.Rgb{255, 255, 255}, 65536, 65536), Co.contrast_ge(Co.Rgb{255, 255, 255}, Co.Rgb{255, 255, 255}, 65537, 65536), Co.contrast_ge(Co.Rgb{0, 0, 0}, Co.Rgb{255, 255, 255}, 1376256, 65536), Co.contrast_ge(Co.Rgb{0, 0, 0}, Co.Rgb{255, 255, 255}, 1376257, 65536)] == [True{}, True{}, False{}, True{}, False{}] : List<&2, Bool>}

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

# Every color function, exactly
# -----------------------------
# The laws above fix lin on 0-255 and quantization, light and contrast
# over the luminance; these pin, for every input, the remaining color
# functions the theme's laws and specs read (equality, lin past 255, the
# palette past 255, the #rrggbb and index texts), each to a spec here that
# does not call bend/color.bend.

def th.eq3(a: Co.Rgb, b: Co.Rgb) -> Bool:
  match a b:
    case Co.Rgb{ar, ag, ab} Co.Rgb{br, bg, bb}:
      Bool.and(U32.is_eq(ar, br), Bool.and(U32.is_eq(ag, bg), U32.is_eq(ab, bb)))

# LAW color_eq_spec: two colors are equal exactly when their three channels are
# EXCLUDES: an equality that ignores a channel or always holds
law color_eq_spec:
  for a: Co.Rgb
  for b: Co.Rgb
  {Co.eq(a, b) == th.eq3(a, b) : Bool}

# LAW color_lin_spec: the linear channel of every U32 is the table entry of its low eight
# bits (spec/theme/color.bend)
# EXCLUDES: a channel past 255 linearized otherwise than its low byte
law color_lin_spec:
  for +c: U32
  {Co.lin(c) == Cm.lin(c) : U32}

# LAW color_past_255_example: anchors past the channel and index range: channel 384 linearizes
# as 128 (its low byte), index 256 is the gray 248
# EXCLUDES: a reading of color_lin_spec or color_ansi256_spec the human did
#   not mean
law color_past_255_example:
  {[Co.lin(384), Co.lin(128)] == [2159, 2159] : List<&2, U32>} & {Co.ansi256(256) == Co.Rgb{248, 248, 248} : Co.Rgb}

def th.join(+b: U32, hi: Maybe<&2, U32>, lo: Maybe<&2, U32>) -> Maybe<&2, U32>:
  match hi:
    case None{}:
      None{}
    case Some{x}:
      match lo:
        case None{}:
          None{}
        case Some{y}:
          Some{(x * b + y : U32)}

def th.rgb3(r: Maybe<&2, U32>, g: Maybe<&2, U32>, b: Maybe<&2, U32>) -> Maybe<&2, Co.Rgb>:
  match r:
    case None{}:
      None{}
    case Some{x}:
      match g:
        case None{}:
          None{}
        case Some{y}:
          match b:
            case None{}:
              None{}
            case Some{z}:
              Some{Co.Rgb{x, y, z}}

def th.sharp(ok: Bool, m: Maybe<&2, Co.Rgb>) -> Maybe<&2, Co.Rgb>:
  match ok:
    case True{}:
      m
    case False{}:
      None{}

def th.hex7(+h: Char, a: Char, b: Char, c: Char, d: Char, e: Char, f: Char) -> Maybe<&2, Co.Rgb>:
  th.sharp(Char.is_eq(h, '#'), th.rgb3(th.join(16, th.hexv(a), th.hexv(b)), th.join(16, th.hexv(c), th.hexv(d)), th.join(16, th.hexv(e), th.hexv(f))))

# the color text s writes: exactly '#' and six hex digits, each pair a
# channel, high digit first; none for any other text
def th.hex(s: String) -> Maybe<&2, Co.Rgb>:
  match s:
    case SNil{}:
      None{}
    case SCon{h, s1}:
      match s1:
        case SNil{}:
          None{}
        case SCon{a, s2}:
          match s2:
            case SNil{}:
              None{}
            case SCon{b, s3}:
              match s3:
                case SNil{}:
                  None{}
                case SCon{c, s4}:
                  match s4:
                    case SNil{}:
                      None{}
                    case SCon{d, s5}:
                      match s5:
                        case SNil{}:
                          None{}
                        case SCon{e, s6}:
                          match s6:
                            case SNil{}:
                              None{}
                            case SCon{f, s7}:
                              match s7:
                                case SNil{}:
                                  th.hex7(h, a, b, c, d, e, f)
                                case SCon{g, s8}:
                                  None{}

# LAW color_hex_spec (R1): every text reads as a color exactly as the spec says
# EXCLUDES: a text of another length or without '#' read as a color, a
#   non-digit read, digits in another order
law color_hex_spec:
  for s: String
  {Co.hex(s) == th.hex(s) : Maybe<&2, Co.Rgb>}

def th.digit(ok: Bool, +x: U32, +base: U32) -> Maybe<&2, U32>:
  match ok:
    case True{}:
      Some{(x - base : U32)}
    case False{}:
      None{}

# a decimal digit, and a leading one (1-9)
def th.decd(c: Char) -> Maybe<&2, U32>:
  match c:
    case Chr{+x}:
      th.digit(th.within(x, 48, 57), x, 48)

def th.decl(c: Char) -> Maybe<&2, U32>:
  match c:
    case Chr{+x}:
      th.digit(th.within(x, 49, 57), x, 48)

def th.cap(m: Maybe<&2, U32>) -> Maybe<&2, U32>:
  match m:
    case None{}:
      None{}
    case Some{+x}:
      th.digit(U32.is_le(x, 255), x, 0)

# the index text s writes: one to three decimal digits, no leading zero,
# at most 255; none for any other text
def th.num(s: String) -> Maybe<&2, U32>:
  match s:
    case SNil{}:
      None{}
    case SCon{a, s1}:
      match s1:
        case SNil{}:
          th.decd(a)
        case SCon{b, s2}:
          match s2:
            case SNil{}:
              th.join(10, th.decl(a), th.decd(b))
            case SCon{c, s3}:
              match s3:
                case SNil{}:
                  th.cap(th.join(10, th.join(10, th.decl(a), th.decd(b)), th.decd(c)))
                case SCon{d, s4}:
                  None{}

# LAW color_num_spec (R1): every text reads as an index exactly as the spec says
# EXCLUDES: a sign, a leading zero, a fourth digit or a value past 255 read
law color_num_spec:
  for s: String
  {Co.num(s) == th.num(s) : Maybe<&2, U32>}

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

def th.ansi_any.if(low: Bool, cube: Bool, +i: U32) -> Co.Rgb:
  match low:
    case True{}:
      Maybe.default(&2, Co.Rgb, List.get(&2, Co.Rgb, th.ansi16(), U32.to_nat(i)), Co.Rgb{0, 0, 0})
    case False{}:
      match cube:
        case True{}:
          Co.Rgb{th.at(th.levels(), U32.div((i - 16 : U32), 36)), th.at(th.levels(), U32.mod(U32.div((i - 16 : U32), 6), 6)), th.at(th.levels(), U32.mod((i - 16 : U32), 6))}
        case False{}:
          Co.Rgb{(8 + (i - 232) * 10 : U32), (8 + (i - 232) * 10 : U32), (8 + (i - 232) * 10 : U32)}

# the xterm-256 color of any U32 index: the ANSI-16 table below 16, the
# cube below 232, else the gray ramp (past 255 it goes on wrapping)
def th.ansi_any(+i: U32) -> Co.Rgb:
  th.ansi_any.if(U32.is_lt(i, 16), U32.is_lt(i, 232), i)

# LAW color_ansi256_spec: the palette color of every U32 index, the indices past 255 included
# EXCLUDES: a palette that differs past the indices color_ansi256_low/high check
law color_ansi256_spec:
  for +i: U32
  {Co.ansi256(i) == th.ansi_any(i) : Co.Rgb}
