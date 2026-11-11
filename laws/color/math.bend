# eukhe: the laws of area color: the linear channel, light or dark, the palette, every color function

import Base
import ../../bend/color.bend as Co
import ../../bend/ffi_color.bend as FCo

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

# LAW color_light_rises: light follows the luminance: of any two colors, when the first is
# light and the second's WCAG relative luminance (Co.lum: the laws
# color_lum_* state it) is at least the first's, the second is light too.
# With color_light_edge_example this is "light exactly when the luminance
# is above one half" for every color; the luminance sums the linear
# channels as the table above rounds them (1/10000), as eukhe always did,
# so a color within about 0.0001 of one half can fall the other way than
# with exact WCAG arithmetic
# EXCLUDES: a light read from anything but the luminance (the channel sum,
#   Rec. 601 weights, one channel), a light that falls as the luminance
#   rises
law color_light_rises:
  for +a: Co.Rgb
  for +b: Co.Rgb
  for le: {U32.is_le(Co.lum(a), Co.lum(b)) == True{} : Bool}
  for la: {Co.light(a) == True{} : Bool}
  {Co.light(b) == True{} : Bool}

# LAW color_light_edge_example: the two colors nearest one half: (223, 177, 169), luminance
# 0.49999994, is dark and (78, 213, 93), luminance 0.50000010, is light.
# No color's luminance lies between the two (an exact search of every
# color over lin's 256 values), so with color_light_rises every color of
# luminance at most 0.49999994 is dark and every color of at least
# 0.50000010 is light
# EXCLUDES: a threshold other than one half
law color_light_edge_example:
  {[Co.lum(Co.Rgb{223, 177, 169}), Co.lum(Co.Rgb{78, 213, 93})] == [49999994, 50000010] : List<&2, U32>} & {[Co.light(Co.Rgb{223, 177, 169}), Co.light(Co.Rgb{78, 213, 93})] == [False{}, True{}] : List<&2, Bool>}

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

# every value of ys is strictly farther from v than x is
def th.farther(+v: U32, +x: U32, ys: List<&2, U32>) -> Bool:
  match ys:
    case Nil{}:
      True{}
    case y <> t:
      Bool.and(U32.is_lt(th.absd(v, x), th.absd(v, y)), th.farther(v, x, t))

# every value of ys is at least as far from v as x is
def th.as_far(+v: U32, +x: U32, ys: List<&2, U32>) -> Bool:
  match ys:
    case Nil{}:
      True{}
    case y <> t:
      Bool.and(U32.is_le(th.absd(v, x), th.absd(v, y)), th.as_far(v, x, t))

# the index of the value that follows the values xs, the first of them at
# index at
def th.index(xs: List<&2, U32>, at: U32) -> U32:
  match xs:
    case Nil{}:
      at
    case x <> t:
      th.index(t, (at + 1 : U32))

# LAW color_near_first_nearest: near answers the index of the first value at the smallest
# distance: for every value v and every list that holds x after values
# all strictly farther from v than x and before values all at least as
# far, near(v, list) is the index of x (the count of the values before
# it). The distance of two values is the larger less the smaller
# EXCLUDES: rounding down or up instead of to the nearest, a later value
#   on a tie, a distance measured otherwise, an index off by one or
#   counted from another start
law color_near_first_nearest:
  for +v: U32
  for +pre: List<&2, U32>
  for +x: U32
  for +post: List<&2, U32>
  for far: {th.farther(v, x, pre) == True{} : Bool}
  for rest: {th.as_far(v, x, post) == True{} : Bool}
  {Co.near(v, List.append(&2, U32, pre, x <> post)) == th.index(pre, 0) : U32}

# LAW color_dist_symmetric: the distance of two colors is the same either way round, for every
# two colors
# EXCLUDES: a channel distance that depends on which color is the larger,
#   a channel of one color measured against another channel of the other
law color_dist_symmetric:
  for +a: Co.Rgb
  for +b: Co.Rgb
  {Co.dist(a, b) == Co.dist(b, a) : U32}

# LAW color_dist_example: anchors of the weighted squared distance: one step of red, green
# or blue alone weighs 299, 587 or 114 (per mille), either way round;
# three steps of one channel weigh nine times that (the square); the
# channels add: (1, 2, 3) from black is 299 + 587·4 + 114·9 = 3673; a color
# is at distance 0 from itself
# EXCLUDES: another weighting, unsquared or swapped channel distances, a
#   channel left out
law color_dist_example:
  {[Co.dist(Co.Rgb{1, 0, 0}, Co.Rgb{0, 0, 0}), Co.dist(Co.Rgb{0, 1, 0}, Co.Rgb{0, 0, 0}), Co.dist(Co.Rgb{0, 0, 1}, Co.Rgb{0, 0, 0}), Co.dist(Co.Rgb{0, 0, 0}, Co.Rgb{1, 0, 0}), Co.dist(Co.Rgb{0, 0, 0}, Co.Rgb{0, 1, 0}), Co.dist(Co.Rgb{0, 0, 0}, Co.Rgb{0, 0, 1}), Co.dist(Co.Rgb{3, 0, 0}, Co.Rgb{0, 0, 0}), Co.dist(Co.Rgb{10, 20, 30}, Co.Rgb{10, 23, 30}), Co.dist(Co.Rgb{10, 20, 33}, Co.Rgb{10, 20, 30}), Co.dist(Co.Rgb{1, 2, 3}, Co.Rgb{0, 0, 0}), Co.dist(Co.Rgb{7, 8, 9}, Co.Rgb{7, 8, 9})] == [299, 587, 114, 299, 587, 114, 2691, 5283, 1026, 3673, 0] : List<&2, U32>}

# every gray slot from k on, n of them: the gray to256 weighs against the
# cube color (Co.grays) is the palette's gray of that slot (index 232 + k),
# and the slot's target (Co.gray.targets) is that gray's lightness,
# weighted as a color's is (299, 587 and 114 of its three equal channels)
def th.gray_slots(n: Nat, +k: U32) -> Bool:
  match n:
    case 0n:
      True{}
    case 1n+p:
      Bool.and(Bool.and(Co.eq(Co.ansi256((232 + k : U32)), Co.Rgb{Co.at(Co.grays(), k), Co.at(Co.grays(), k), Co.at(Co.grays(), k)}), U32.is_eq(Co.at(Co.gray.targets(), k), (299 * Co.at(Co.grays(), k) + 587 * Co.at(Co.grays(), k) + 114 * Co.at(Co.grays(), k) : U32))), th.gray_slots(p, (k + 1 : U32)))

# LAW color_gray_slots: the 24 grays to256 chooses among are the palette's grays (indices
# 232-255), slot by slot, and each slot's target lightness is its gray's
# EXCLUDES: a gray or a target off by a step or a unit, a slot that answers
#   another index than its gray's
law color_gray_slots:
  {th.gray_slots(24n, 0) == True{} : Bool}

# LAW color_to256_example: anchors: red 250 is the cube's red (196), not 215 (160); a
# near-neutral (160, 155, 164) is the gray 158 (247); white is 231
# EXCLUDES: the cube's next lower red for 250, a cube color for the
#   near-neutral, a gray for white
law color_to256_example:
  {[Co.to256(Co.Rgb{250, 0, 0}), Co.to256(Co.Rgb{160, 155, 164}), Co.to256(Co.Rgb{255, 255, 255})] == [196, 247, 231] : List<&2, U32>} & {FCo.ffi("0,1,250,0,0,") == "1,196," : String}

# LAW color_to256_edges_example: anchors at the edges of the rule: red 115, midway between the
# cube levels 95 and 135, takes the lower (52); (4, 4, 4), as far from the
# gray 8 as from black, is black (16: the gray must be strictly closer);
# (13, 13, 13), its lightness 13000 midway between the grays 8 and 18,
# takes the lower gray (232) and (15, 12, 13), lightness 13011, the gray
# 18 (233); (160, 154, 164), nearer the gray 158 than any cube color but
# with channels 10 apart, is not near-neutral and stays in the cube (139),
# where (160, 155, 164) of color_to256_example, 9 apart, is the gray
# EXCLUDES: a tie to the higher level or gray, the gray on a tie with the
#   cube, a near-neutral bound other than 10 or a spread other than the
#   largest channel less the smallest, a lightness weighted otherwise than
#   299, 587, 114
law color_to256_edges_example:
  {[Co.to256(Co.Rgb{115, 0, 0}), Co.to256(Co.Rgb{4, 4, 4}), Co.to256(Co.Rgb{13, 13, 13}), Co.to256(Co.Rgb{15, 12, 13}), Co.to256(Co.Rgb{160, 154, 164})] == [52, 16, 232, 233, 139] : List<&2, U32>}

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

# LAW color_hex_letters_example (R1): anchor: "#hhhhhh" and "#GGGGGG" are no colors
# EXCLUDES: letters past f read as digits
law color_hex_letters_example:
  {[Co.hex("#hhhhhh"), Co.hex("#GGGGGG")] == [None{}, None{}] : List<&2, Maybe<&2, Co.Rgb>>}

# Color equality
# --------------
# What the theme's rules compare two colors with.

# LAW color_eq_same: every color equals itself
# EXCLUDES: an equality that never holds, one that compares a channel with
#   another channel
law color_eq_same:
  for +a: Co.Rgb
  {Co.eq(a, a) == True{} : Bool}

# LAW color_eq_sound: two colors that compare equal are the same color, channel for
# channel
# EXCLUDES: an equality that ignores a channel or always holds
law color_eq_sound:
  for +a: Co.Rgb
  for +b: Co.Rgb
  for same: {Co.eq(a, b) == True{} : Bool}
  {a == b : Co.Rgb}

# LAW color_past_255_example: anchors past the channel and index range: channel 384 linearizes
# as 128 (its low byte), index 256 is the gray 248
# EXCLUDES: a channel past 255 linearized as anything but its low byte at
#   384, a gray ramp that ends at index 255
law color_past_255_example:
  {[Co.lin(384), Co.lin(128)] == [2159, 2159] : List<&2, U32>} & {Co.ansi256(256) == Co.Rgb{248, 248, 248} : Co.Rgb}

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
