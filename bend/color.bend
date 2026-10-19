# color: the color math of the themes (crates/eukhe-theme/src/color.rs,
# laws in laws/themes.bend, docs/interface.md Themes). Every function here
# is on U32 and exact; the bridge test in eukhe-core
# (crates/eukhe-core/src/export_html/theme_bridge.rs) runs the Rust
# functions and this model on the same inputs.
#
# - lin(c): the sRGB channel c (0..255) linearized, in units of 1/10000,
#   rounded to nearest. A table: the Rust function computes it, and the
#   bridge pins all 256 entries.
# - lum(c): the WCAG relative luminance, 2126·R + 7152·G + 722·B over the
#   linear channels, in units of 1/1e8.
# - contrast_ge(a, b, num, den): the WCAG contrast ratio of a and b,
#   (L_light + 0.05) / (L_dark + 0.05), is at least num/den. Exact: the
#   comparison is (L_dark + F)·num <= (L_light + F)·den with F = 0.05 in
#   lum units, on U32 (no overflow for num <= 40).
# - light(c): lum(c) is above one half.
# - ansi256(i): the color of xterm-256 index i; to256(c): the index a
#   256-color terminal paints for c.

import Base

type Rgb is Data:
  Rgb{r: U32, g: U32, b: U32}

def eq(+a: Rgb, +b: Rgb) -> Bool:
  match a b:
    case Rgb{ar, ag, ab} Rgb{br, bg, bb}:
      Bool.and(U32.is_eq(ar, br), Bool.and(U32.is_eq(ag, bg), U32.is_eq(ab, bb)))

# the first of two values when c holds, else the second
def sel(c: Bool, a: U32, b: U32) -> U32:
  match c:
    case True{}:
      a
    case False{}:
      b

def absdiff(+a: U32, +b: U32) -> U32:
  sel(U32.is_ge(a, b), (a - b : U32), (b - a : U32))

# Linearization
# -------------

type LinT is Data:
  Leaf{v: U32}
  Node{lo: LinT, hi: LinT}

# the leaf the bits select, most significant first
def lin.go(t: LinT, bs: List<&2, Bool>) -> U32:
  match t:
    case Leaf{v}:
      v
    case Node{lo, hi}:
      match bs:
        case Nil{}:
          0
        case Con{b, rest}:
          match b:
            case True{}:
              lin.go(hi, rest)
            case False{}:
              lin.go(lo, rest)

def bit(+c: U32, k: U32) -> Bool:
  Bool.not(U32.is_zero((c .&. k : U32)))

def bits(+c: U32) -> List<&2, Bool>:
  [bit(c, 128), bit(c, 64), bit(c, 32), bit(c, 16), bit(c, 8), bit(c, 4), bit(c, 2), bit(c, 1)]

def lin.t0() -> LinT:
  Node{Node{Node{Node{Leaf{0}, Leaf{3}}, Node{Leaf{6}, Leaf{9}}}, Node{Node{Leaf{12}, Leaf{15}}, Node{Leaf{18}, Leaf{21}}}}, Node{Node{Node{Leaf{24}, Leaf{27}}, Node{Leaf{30}, Leaf{33}}}, Node{Node{Leaf{37}, Leaf{40}}, Node{Leaf{44}, Leaf{48}}}}}

def lin.t1() -> LinT:
  Node{Node{Node{Node{Leaf{52}, Leaf{56}}, Node{Leaf{60}, Leaf{65}}}, Node{Node{Leaf{70}, Leaf{75}}, Node{Leaf{80}, Leaf{86}}}}, Node{Node{Node{Leaf{91}, Leaf{97}}, Node{Leaf{103}, Leaf{110}}}, Node{Node{Leaf{116}, Leaf{123}}, Node{Leaf{130}, Leaf{137}}}}}

def lin.t2() -> LinT:
  Node{Node{Node{Node{Leaf{144}, Leaf{152}}, Node{Leaf{160}, Leaf{168}}}, Node{Node{Leaf{176}, Leaf{185}}, Node{Leaf{194}, Leaf{203}}}}, Node{Node{Node{Leaf{212}, Leaf{222}}, Node{Leaf{232}, Leaf{242}}}, Node{Node{Leaf{252}, Leaf{262}}, Node{Leaf{273}, Leaf{284}}}}}

def lin.t3() -> LinT:
  Node{Node{Node{Node{Leaf{296}, Leaf{307}}, Node{Leaf{319}, Leaf{331}}}, Node{Node{Leaf{343}, Leaf{356}}, Node{Leaf{369}, Leaf{382}}}}, Node{Node{Node{Leaf{395}, Leaf{409}}, Node{Leaf{423}, Leaf{437}}}, Node{Node{Leaf{452}, Leaf{467}}, Node{Leaf{482}, Leaf{497}}}}}

def lin.t4() -> LinT:
  Node{Node{Node{Node{Leaf{513}, Leaf{529}}, Node{Leaf{545}, Leaf{561}}}, Node{Node{Leaf{578}, Leaf{595}}, Node{Leaf{612}, Leaf{630}}}}, Node{Node{Node{Leaf{648}, Leaf{666}}, Node{Leaf{685}, Leaf{704}}}, Node{Node{Leaf{723}, Leaf{742}}, Node{Leaf{762}, Leaf{782}}}}}

def lin.t5() -> LinT:
  Node{Node{Node{Node{Leaf{802}, Leaf{823}}, Node{Leaf{844}, Leaf{865}}}, Node{Node{Leaf{887}, Leaf{908}}, Node{Leaf{931}, Leaf{953}}}}, Node{Node{Node{Leaf{976}, Leaf{999}}, Node{Leaf{1022}, Leaf{1046}}}, Node{Node{Leaf{1070}, Leaf{1095}}, Node{Leaf{1119}, Leaf{1144}}}}}

def lin.t6() -> LinT:
  Node{Node{Node{Node{Leaf{1170}, Leaf{1195}}, Node{Leaf{1221}, Leaf{1248}}}, Node{Node{Leaf{1274}, Leaf{1301}}, Node{Leaf{1329}, Leaf{1356}}}}, Node{Node{Node{Leaf{1384}, Leaf{1413}}, Node{Leaf{1441}, Leaf{1470}}}, Node{Node{Leaf{1500}, Leaf{1529}}, Node{Leaf{1559}, Leaf{1590}}}}}

def lin.t7() -> LinT:
  Node{Node{Node{Node{Leaf{1620}, Leaf{1651}}, Node{Leaf{1683}, Leaf{1714}}}, Node{Node{Leaf{1746}, Leaf{1779}}, Node{Leaf{1812}, Leaf{1845}}}}, Node{Node{Node{Leaf{1878}, Leaf{1912}}, Node{Leaf{1946}, Leaf{1981}}}, Node{Node{Leaf{2016}, Leaf{2051}}, Node{Leaf{2086}, Leaf{2122}}}}}

def lin.t8() -> LinT:
  Node{Node{Node{Node{Leaf{2159}, Leaf{2195}}, Node{Leaf{2232}, Leaf{2270}}}, Node{Node{Leaf{2307}, Leaf{2346}}, Node{Leaf{2384}, Leaf{2423}}}}, Node{Node{Node{Leaf{2462}, Leaf{2502}}, Node{Leaf{2542}, Leaf{2582}}}, Node{Node{Leaf{2623}, Leaf{2664}}, Node{Leaf{2705}, Leaf{2747}}}}}

def lin.t9() -> LinT:
  Node{Node{Node{Node{Leaf{2789}, Leaf{2831}}, Node{Leaf{2874}, Leaf{2918}}}, Node{Node{Leaf{2961}, Leaf{3005}}, Node{Leaf{3050}, Leaf{3095}}}}, Node{Node{Node{Leaf{3140}, Leaf{3185}}, Node{Leaf{3231}, Leaf{3278}}}, Node{Node{Leaf{3325}, Leaf{3372}}, Node{Leaf{3419}, Leaf{3467}}}}}

def lin.t10() -> LinT:
  Node{Node{Node{Node{Leaf{3515}, Leaf{3564}}, Node{Leaf{3613}, Leaf{3663}}}, Node{Node{Leaf{3712}, Leaf{3763}}, Node{Leaf{3813}, Leaf{3864}}}}, Node{Node{Node{Leaf{3916}, Leaf{3968}}, Node{Leaf{4020}, Leaf{4072}}}, Node{Node{Leaf{4125}, Leaf{4179}}, Node{Leaf{4233}, Leaf{4287}}}}}

def lin.t11() -> LinT:
  Node{Node{Node{Node{Leaf{4342}, Leaf{4397}}, Node{Leaf{4452}, Leaf{4508}}}, Node{Node{Leaf{4564}, Leaf{4621}}, Node{Leaf{4678}, Leaf{4735}}}}, Node{Node{Node{Leaf{4793}, Leaf{4851}}, Node{Leaf{4910}, Leaf{4969}}}, Node{Node{Leaf{5029}, Leaf{5089}}, Node{Leaf{5149}, Leaf{5210}}}}}

def lin.t12() -> LinT:
  Node{Node{Node{Node{Leaf{5271}, Leaf{5333}}, Node{Leaf{5395}, Leaf{5457}}}, Node{Node{Leaf{5520}, Leaf{5583}}, Node{Leaf{5647}, Leaf{5711}}}}, Node{Node{Node{Leaf{5776}, Leaf{5841}}, Node{Leaf{5906}, Leaf{5972}}}, Node{Node{Leaf{6038}, Leaf{6105}}, Node{Leaf{6172}, Leaf{6240}}}}}

def lin.t13() -> LinT:
  Node{Node{Node{Node{Leaf{6308}, Leaf{6376}}, Node{Leaf{6445}, Leaf{6514}}}, Node{Node{Leaf{6584}, Leaf{6654}}, Node{Leaf{6724}, Leaf{6795}}}}, Node{Node{Node{Leaf{6867}, Leaf{6939}}, Node{Leaf{7011}, Leaf{7084}}}, Node{Node{Leaf{7157}, Leaf{7231}}, Node{Leaf{7305}, Leaf{7379}}}}}

def lin.t14() -> LinT:
  Node{Node{Node{Node{Leaf{7454}, Leaf{7529}}, Node{Leaf{7605}, Leaf{7682}}}, Node{Node{Leaf{7758}, Leaf{7835}}, Node{Leaf{7913}, Leaf{7991}}}}, Node{Node{Node{Leaf{8070}, Leaf{8148}}, Node{Leaf{8228}, Leaf{8308}}}, Node{Node{Leaf{8388}, Leaf{8469}}, Node{Leaf{8550}, Leaf{8632}}}}}

def lin.t15() -> LinT:
  Node{Node{Node{Node{Leaf{8714}, Leaf{8796}}, Node{Leaf{8879}, Leaf{8963}}}, Node{Node{Leaf{9047}, Leaf{9131}}, Node{Leaf{9216}, Leaf{9301}}}}, Node{Node{Node{Leaf{9387}, Leaf{9473}}, Node{Leaf{9560}, Leaf{9647}}}, Node{Node{Leaf{9734}, Leaf{9823}}, Node{Leaf{9911}, Leaf{10000}}}}}

def lin.table() -> LinT:
  Node{Node{Node{Node{lin.t0(), lin.t1()}, Node{lin.t2(), lin.t3()}}, Node{Node{lin.t4(), lin.t5()}, Node{lin.t6(), lin.t7()}}}, Node{Node{Node{lin.t8(), lin.t9()}, Node{lin.t10(), lin.t11()}}, Node{Node{lin.t12(), lin.t13()}, Node{lin.t14(), lin.t15()}}}}

def lin(+c: U32) -> U32:
  lin.go(lin.table(), bits(c))

# Luminance and contrast
# ----------------------

def lum(c: Rgb) -> U32:
  match c:
    case Rgb{r, g, b}:
      (2126 * lin(r) + 7152 * lin(g) + 722 * lin(b) : U32)

# F, 0.05 in lum units
def flare() -> U32:
  5000000

def contrast_ge(+a: Rgb, +b: Rgb, num: U32, den: U32) -> Bool:
  +la = lum(a)
  +lb = lum(b)
  +light = U32.max(la, lb)
  +dark = U32.min(la, lb)
  U32.is_le(((dark + flare()) * num : U32), ((light + flare()) * den : U32))

def light(+c: Rgb) -> Bool:
  U32.is_gt(lum(c), 50000000)

# The xterm-256 palette
# ---------------------

def ansi16() -> List<&2, Rgb>:
  [Rgb{0, 0, 0}, Rgb{128, 0, 0}, Rgb{0, 128, 0}, Rgb{128, 128, 0}, Rgb{0, 0, 128}, Rgb{128, 0, 128}, Rgb{0, 128, 128}, Rgb{192, 192, 192}, Rgb{128, 128, 128}, Rgb{255, 0, 0}, Rgb{0, 255, 0}, Rgb{255, 255, 0}, Rgb{0, 0, 255}, Rgb{255, 0, 255}, Rgb{0, 255, 255}, Rgb{255, 255, 255}]

def levels() -> List<&2, U32>:
  [0, 95, 135, 175, 215, 255]

def grays() -> List<&2, U32>:
  [8, 18, 28, 38, 48, 58, 68, 78, 88, 98, 108, 118, 128, 138, 148, 158, 168, 178, 188, 198, 208, 218, 228, 238]

def at(xs: List<&2, U32>, +i: U32) -> U32:
  Maybe.default(&2, U32, List.get(&2, U32, xs, U32.to_nat(i)), 0)

def ansi256.cube(+s: U32) -> Rgb:
  Rgb{at(levels(), U32.div(s, 36)), at(levels(), U32.mod(U32.div(s, 6), 6)), at(levels(), U32.mod(s, 6))}

def ansi256.gray(+g: U32) -> Rgb:
  Rgb{g, g, g}

def ansi256.pick(lo: Bool, cube: Bool, +i: U32) -> Rgb:
  match lo:
    case True{}:
      Maybe.default(&2, Rgb, List.get(&2, Rgb, ansi16(), U32.to_nat(i)), Rgb{0, 0, 0})
    case False{}:
      match cube:
        case True{}:
          ansi256.cube((i - 16 : U32))
        case False{}:
          ansi256.gray((8 + (i - 232) * 10 : U32))

def ansi256(+i: U32) -> Rgb:
  ansi256.pick(U32.is_lt(i, 16), U32.is_lt(i, 232), i)

# the index of the value of xs nearest v (the first on a tie), from at
def near.go(+v: U32, xs: List<&2, U32>, +at: U32, +best: U32, +bestd: U32) -> U32:
  match xs:
    case Nil{}:
      best
    case Con{x, rest}:
      +d = absdiff(v, x)
      +closer = U32.is_lt(d, bestd)
      near.go(v, rest, (at + 1 : U32), sel(closer, at, best), sel(closer, d, bestd))

def near(+v: U32, xs: List<&2, U32>) -> U32:
  near.go(v, xs, 0, 0, 4294967295)

def sq(+x: U32) -> U32:
  (x * x : U32)

# the weighted squared distance of two colors (weights per mille)
def dist(+a: Rgb, +b: Rgb) -> U32:
  match a b:
    case Rgb{ar, ag, ab} Rgb{br, bg, bb}:
      (299 * sq(absdiff(ar, br)) + 587 * sq(absdiff(ag, bg)) + 114 * sq(absdiff(ab, bb)) : U32)

def to256.pick(gray: Bool, +gi: U32, +ci: U32) -> U32:
  sel(gray, (232 + gi : U32), ci)

def to256(+c: Rgb) -> U32:
  match c:
    case Rgb{r, g, b}:
      +ri = near(r, levels())
      +gi = near(g, levels())
      +bi = near(b, levels())
      +cube = {Rgb{at(levels(), ri), at(levels(), gi), at(levels(), bi)} : Rgb}
      +lightness = (299 * r + 587 * g + 114 * b : U32)
      +slot = near(lightness, [8000, 18000, 28000, 38000, 48000, 58000, 68000, 78000, 88000, 98000, 108000, 118000, 128000, 138000, 148000, 158000, 168000, 178000, 188000, 198000, 208000, 218000, 228000, 238000])
      +gv = at(grays(), slot)
      +gray = {Rgb{gv, gv, gv} : Rgb}
      +spread = (U32.max(r, U32.max(g, b)) - U32.min(r, U32.min(g, b)) : U32)
      +ci = (16 + 36 * ri + 6 * gi + bi : U32)
      to256.pick(Bool.and(U32.is_lt(spread, 10), U32.is_lt(dist(Rgb{r, g, b}, gray), dist(Rgb{r, g, b}, cube))), slot, ci)
