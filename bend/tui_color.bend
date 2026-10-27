# tui_color: the colors that the terminal UI computes from a theme
# (crates/eukhe-tui/src/theme.rs, crates/eukhe-tui/src/status_line.rs);
# laws in laws/tui_color.bend (T3).
# The bridge test crates/eukhe-tui/src/theme/bridge.rs runs the Rust code
# and this model (through bridge/bridge_tui_color.bend) on the same
# scenarios.
#
# - The effort ramp. A model offers a ladder of n effort levels (any n).
#   The theme gives two colors, effortLow (42) and effortHigh (43). Rung k
#   (1..n) of the ramp takes, in each channel from a (effortLow) to b
#   (effortHigh), the lower end plus floor(d * w / n), with d = |b - a|:
#   w is k when a <= b and n - k when a > b. So rung n is effortHigh, and
#   the ramp starts one step above effortLow.
# - The usage bands. The window that the daemon serves holds w tokens and
#   the context holds t. Band i is reached when w > 0 and t/w is at least
#   the fraction num/den of band i, exactly: w * num <= t * den. The tone
#   is the number of bands reached: 0 dim, 1 warning, 2 contextHigh,
#   3 error.
# - The roles. Every color slot of the terminal UI, as its token index in
#   bend/theme/: the ink slots, the surface slots, then the ramp ends,
#   the lift ends and the canvas.

import Base
import ./theme/file.bend as TFile
import ./theme/palette.bend as TPalette
import ./theme/bundled.bend as TBundled
import ./color.bend as Co
import ./effort.bend as Ef

# Colors
# ------

# a color with Nat channels
type Px is Data:
  Px{r: Nat, g: Nat, b: Nat}

def px.of(c: Co.Rgb) -> Px:
  match c:
    case Co.Rgb{r, g, b}:
      Px{U32.to_nat(r), U32.to_nat(g), U32.to_nat(b)}

def px.eq(a: Px, b: Px) -> Bool:
  match a b:
    case Px{ar, ag, ab} Px{br, bg, bb}:
      Bool.and(Nat.is_eq(ar, br), Bool.and(Nat.is_eq(ag, bg), Nat.is_eq(ab, bb)))

# The effort ramp
# ---------------

# the distance from a to b
def gap.pick(up: Bool, +a: Nat, +b: Nat) -> Nat:
  match up:
    case True{}:
      Nat.sub(b, a)
    case False{}:
      Nat.sub(a, b)

def gap(+a: Nat, +b: Nat) -> Nat:
  gap.pick(Nat.is_le(a, b), a, b)

# one channel of a rung: the lower end plus floor(d * w / n), w = wu when
# the channel rises (a <= b), else wd (Nat.div runs native: one step,
# whatever the width)
def chan.pick(up: Bool, +a: Nat, +b: Nat, +wu: Nat, +wd: Nat, +n: Nat) -> Nat:
  match up:
    case True{}:
      Nat.add(a, Nat.div(Nat.mul(wu, Nat.sub(b, a)), n))
    case False{}:
      Nat.add(b, Nat.div(Nat.mul(wd, Nat.sub(a, b)), n))

def chan(+a: Nat, +b: Nat, +wu: Nat, +wd: Nat, +n: Nat) -> Nat:
  chan.pick(Nat.is_le(a, b), a, b, wu, wd, n)

def rung(+lo: Px, +hi: Px, +wu: Nat, +wd: Nat, +n: Nat) -> Px:
  match lo hi:
    case Px{lr, lg, lb} Px{hr, hg, hb}:
      Px{chan(lr, hr, wu, wd, n), chan(lg, hg, wu, wd, n), chan(lb, hb, wu, wd, n)}

# the rungs after the first done ones, left of them to go
def ramp.go(+left: Nat, +done: Nat, +lo: Px, +hi: Px, +n: Nat) -> List<&2, Px>:
  match left:
    case 0n:
      Nil{}
    case 1n+l:
      rung(lo, hi, 1n+done, l, n) <> ramp.go(l, 1n+done, lo, hi, n)

# the n rungs of the ramp from lo to hi
def ramp(+lo: Px, +hi: Px, +n: Nat) -> List<&2, Px>:
  ramp.go(n, 0n, lo, hi, n)

# the widest channel distance of lo and hi
def span(lo: Px, hi: Px) -> Nat:
  match lo hi:
    case Px{lr, lg, lb} Px{hr, hg, hb}:
      Nat.max(gap(lr, hr), Nat.max(gap(lg, hg), gap(lb, hb)))

# a channel goes from x to y toward b: up when a <= b, else down
def step.pick(up: Bool, +x: Nat, +y: Nat) -> Bool:
  match up:
    case True{}:
      Nat.is_le(x, y)
    case False{}:
      Nat.is_le(y, x)

def step(+a: Nat, +b: Nat, +x: Nat, +y: Nat) -> Bool:
  step.pick(Nat.is_le(a, b), x, y)

# every channel goes from x to y toward hi
def moves(lo: Px, hi: Px, x: Px, y: Px) -> Bool:
  match lo hi x y:
    case Px{lr, lg, lb} Px{hr, hg, hb} Px{xr, xg, xb} Px{yr, yg, yb}:
      Bool.and(step(lr, hr, xr, yr), Bool.and(step(lg, hg, xg, yg), step(lb, hb, xb, yb)))

def ordered.from(ys: List<&2, Px>, +x: Px, +lo: Px, +hi: Px) -> Bool:
  match ys:
    case Nil{}:
      True{}
    case Con{+y, rest}:
      Bool.and(moves(lo, hi, x, y), ordered.from(rest, y, lo, hi))

# along the rungs, every channel moves from lo toward hi
def ordered(+lo: Px, +hi: Px, xs: List<&2, Px>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{x, rest}:
      ordered.from(rest, x, lo, hi)

def notin(+x: Px, ys: List<&2, Px>) -> Bool:
  match ys:
    case Nil{}:
      True{}
    case Con{y, rest}:
      Bool.and(Bool.not(px.eq(x, y)), notin(x, rest))

# no two rungs are the same color
def distinct(xs: List<&2, Px>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{+x, +rest}:
      Bool.and(notin(x, rest), distinct(rest))

# the effort ramp ends of a shipped theme
def shipped.lo(s: TBundled.Shipped) -> Px:
  px.of(TPalette.at(TBundled.table(s), 42n))

def shipped.hi(s: TBundled.Shipped) -> Px:
  px.of(TPalette.at(TBundled.table(s), 43n))

# the longest ladder: every level of the vocabulary
def ladder.max() -> Nat:
  List.length(&2, Ef.Lv, Ef.ladder())

# The usage bands
# ---------------

type Frac is Data:
  Frac{num: Nat, den: Nat}

def bands() -> List<&2, Frac>:
  [Frac{1n, 2n}, Frac{7n, 10n}, Frac{9n, 10n}]

# t of w tokens reach the fraction f of the window
def reached(f: Frac, +t: Nat, +w: Nat) -> Bool:
  match f:
    case Frac{num, den}:
      Bool.and(Nat.is_lt(0n, w), Nat.is_le(Nat.mul(w, num), Nat.mul(t, den)))

def one(b: Bool) -> Nat:
  match b:
    case True{}:
      1n
    case False{}:
      0n

def band.go(fs: List<&2, Frac>, +t: Nat, +w: Nat) -> Nat:
  match fs:
    case Nil{}:
      0n
    case Con{f, rest}:
      Nat.add(one(reached(f, t, w)), band.go(rest, t, w))

# the usage tone of t of w tokens: the number of bands reached
def band(+t: Nat, +w: Nat) -> Nat:
  band.go(bands(), t, w)

# a fraction is above zero and at most the whole window
def frac.ok(f: Frac) -> Bool:
  match f:
    case Frac{+num, den}:
      Bool.and(Nat.is_lt(0n, num), Nat.is_le(num, den))

# a is below b: a.num / a.den < b.num / b.den
def frac.lt(a: Frac, b: Frac) -> Bool:
  match a b:
    case Frac{an, ad} Frac{bn, bd}:
      Nat.is_lt(Nat.mul(an, bd), Nat.mul(bn, ad))

def ascend.from(fs: List<&2, Frac>, +f: Frac) -> Bool:
  match fs:
    case Nil{}:
      True{}
    case Con{+g, rest}:
      Bool.and(frac.lt(f, g), ascend.from(rest, g))

def ascend.ok(fs: List<&2, Frac>) -> Bool:
  match fs:
    case Nil{}:
      True{}
    case Con{f, rest}:
      Bool.and(frac.ok(f), ascend.ok(rest))

# every band is a fraction of the window, and each is above the one before
def ascend(+fs: List<&2, Frac>) -> Bool:
  match fs:
    case Nil{}:
      True{}
    case Con{+f, +rest}:
      Bool.and(ascend.ok(f <> rest), ascend.from(rest, f))

# The roles
# ---------

# every color slot of the terminal UI, as a token index: the ink slots,
# the surface slots, the ramp ends, the lift ends, the canvas
def roles() -> List<&2, Nat>:
  [0n, 1n, 2n, 3n, 4n, 5n, 6n, 7n, 8n, 9n, 10n, 11n, 12n, 13n, 14n, 15n, 16n, 17n, 18n, 19n, 20n, 21n, 22n, 23n, 24n, 25n, 26n, 27n, 28n, 29n, 30n, 31n, 32n, 33n, 34n, 35n, 36n, 37n, 38n, 39n, 40n, 41n, 44n, 47n, 48n, 49n, 50n, 51n, 52n, 53n, 54n, 55n, 56n, 42n, 43n, 45n, 46n, 57n]

def found(-A: Data, m: Maybe<&2, Maybe<&2, A>>) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{v}:
      Maybe.is_some(&2, A, v)

# every role has a value in the palette p
def resolves(+p: List<&2, Maybe<&2, TFile.Val>>, rs: List<&2, Nat>) -> Bool:
  match rs:
    case Nil{}:
      True{}
    case Con{r, rest}:
      Bool.and(found(TFile.Val, List.get(&2, Maybe<&2, TFile.Val>, p, r)), resolves(p, rest))

# every role paints a color in the table xs
def paints(+xs: List<&2, Co.Rgb>, rs: List<&2, Nat>) -> Bool:
  match rs:
    case Nil{}:
      True{}
    case Con{r, rest}:
      Bool.and(Maybe.is_some(&2, Co.Rgb, List.get(&2, Co.Rgb, xs, r)), paints(xs, rest))
