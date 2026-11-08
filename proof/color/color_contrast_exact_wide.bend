# eukhe: the proof of LAW color_contrast_exact_wide: the luminances are the
# spec's (cx.lum); with a term past 40 the test takes the wide path; its
# split at 2^16 compares the same naturals as the spec (cx.wide, from the
# lemmas of ./color_contrast_exact_wide/nat.bend at the base 1 + 65535);
# whichever luminance is lower, min and max pick the same darker and
# lighter as the spec (cx.b, a case split on the comparison)

import Base
import ../../bend/color.bend as Co
import ../../laws/color/math.bend as Color
import ./color_contrast_exact_wide/nat.bend as LCw

def cx.lum(c: Co.Rgb) -> {Co.lum(c) == Color.th.lum(c) : U32}:
  match c:
    case Co.Rgb{r, g, b}:
      {==}

# the wide path is d·n <= l·e on naturals
def cx.wide(+d: Nat, +n: Nat, +l: Nat, +e: Nat) -> {Co.contrast.wide(d, n, l, e) == Nat.is_le(Nat.mul(d, n), Nat.mul(l, e)) : Bool}:
  LCw.cw.split_le(d, n, l, e, 65535n)

def cx.b(t: Bool, +x: U32, +y: U32, +num: U32, +den: U32) -> {Co.contrast.wide(U32.to_nat((Bool.pick(U32, t, x, y) + Co.flare() : U32)), U32.to_nat(num), U32.to_nat((Bool.pick(U32, t, y, x) + Co.flare() : U32)), U32.to_nat(den)) == Color.th.exact.if(t, x, y, num, den) : Bool}:
  match t:
    case True{}:
      cx.wide(U32.to_nat((x + Co.flare() : U32)), U32.to_nat(num), U32.to_nat((y + Co.flare() : U32)), U32.to_nat(den))
    case False{}:
      cx.wide(U32.to_nat((y + Co.flare() : U32)), U32.to_nat(num), U32.to_nat((x + Co.flare() : U32)), U32.to_nat(den))

def cx.go(la: U32, lb: U32, +num: U32, +den: U32) -> {Co.contrast.wide(U32.to_nat((U32.min(la, lb) + Co.flare() : U32)), U32.to_nat(num), U32.to_nat((U32.max(la, lb) + Co.flare() : U32)), U32.to_nat(den)) == Color.th.exact.if(U32.is_lt(la, lb), la, lb, num, den) : Bool}:
  match la lb:
    case U32{+x} U32{+y}:
      cx.b(U32.is_lt(U32{x}, U32{y}), U32{x}, U32{y}, num, den)

def Color.color_contrast_exact_wide(a, b, num, den, wide):
  %cx.lum(a) : {Co.contrast_ge(a, b, num, den) == Color.th.exact.if(U32.is_lt(_, Color.th.lum(b)), _, Color.th.lum(b), num, den) : Bool}
  %cx.lum(b) : {Co.contrast_ge(a, b, num, den) == Color.th.exact.if(U32.is_lt(Co.lum(a), _), Co.lum(a), _, num, den) : Bool}
  %Equal.sym(Bool, Bool.and(U32.is_le(num, 40), U32.is_le(den, 40)), False{}, wide) : {Co.contrast.pick(_, (U32.min(Co.lum(a), Co.lum(b)) + Co.flare() : U32), (U32.max(Co.lum(a), Co.lum(b)) + Co.flare() : U32), num, den) == Color.th.exact.if(U32.is_lt(Co.lum(a), Co.lum(b)), Co.lum(a), Co.lum(b), num, den) : Bool}
  cx.go(Co.lum(a), Co.lum(b), num, den)
