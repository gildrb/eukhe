# eukhe: a contrast test past terms of 40, decided on bits: by LAW
# color_contrast_exact_wide it is the spec's comparison of naturals, and
# that comparison is the one of the bit products (./bin.bend), which the
# checker computes for any U32 inputs. The closed contrast laws rewrite
# each such test with cd.wide before they compute.

import Base
import ../../../bend/color.bend as Co
import ../../../laws/color/math.bend as Color
import ../color_contrast_exact_wide.bend as PColorContrastExactWide
import ./bin.bend as LCb

# the spec's exact test with luminances la and lb, on bits
def cd.if(lt: Bool, +la: U32, +lb: U32, +num: U32, +den: U32) -> Bool:
  match lt:
    case True{}:
      LCb.cb.le((la + 5000000 : U32), num, (lb + 5000000 : U32), den)
    case False{}:
      LCb.cb.le((lb + 5000000 : U32), num, (la + 5000000 : U32), den)

def cd.decide(+a: Co.Rgb, +b: Co.Rgb, +num: U32, +den: U32) -> Bool:
  cd.if(U32.is_lt(Color.th.lum(a), Color.th.lum(b)), Color.th.lum(a), Color.th.lum(b), num, den)

def cd.if_eq(lt: Bool, +la: U32, +lb: U32, +num: U32, +den: U32) -> {Color.th.exact.if(lt, la, lb, num, den) == cd.if(lt, la, lb, num, den) : Bool}:
  match lt:
    case True{}:
      LCb.cb.le_nat((la + 5000000 : U32), num, (lb + 5000000 : U32), den)
    case False{}:
      LCb.cb.le_nat((lb + 5000000 : U32), num, (la + 5000000 : U32), den)

# a test past terms of 40 is its decision on bits
def cd.wide(+a: Co.Rgb, +b: Co.Rgb, +num: U32, +den: U32, wide: {Bool.and(U32.is_le(num, 40), U32.is_le(den, 40)) == False{} : Bool}) -> {cd.decide(a, b, num, den) == Co.contrast_ge(a, b, num, den) : Bool}:
  Equal.sym(Bool, Co.contrast_ge(a, b, num, den), cd.decide(a, b, num, den),
    Equal.trans(Bool, Co.contrast_ge(a, b, num, den), Color.th.contrast_exact(a, b, num, den), cd.decide(a, b, num, den),
      Color.color_contrast_exact_wide(a, b, num, den, wide),
      cd.if_eq(U32.is_lt(Color.th.lum(a), Color.th.lum(b)), Color.th.lum(a), Color.th.lum(b), num, den)))
