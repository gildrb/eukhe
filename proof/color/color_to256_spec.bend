# eukhe: the proof of LAW color_to256_spec: the four nearest indices are
# the spec's (LAW color_near_spec), then the same choice with the spec's
# distance (LAW color_dist_spec) and select (PNear.cn.sel)

import Base
import ../../bend/color.bend as Co
import ../../laws/color.bend as Color
import ./color_near_spec.bend as PNear
import ./color_dist_spec.bend as PDist

def ct.of(+r: U32, +g: U32, +b: U32, +ri: U32, +gi: U32, +bi: U32, +slot: U32) -> {Co.to256.of(r, g, b, ri, gi, bi, slot) == Color.th.to256.of(r, g, b, ri, gi, bi, slot) : U32}:
  +c = {Co.Rgb{r, g, b} : Co.Rgb}
  +gv = Co.at(Co.grays(), slot)
  +gray = {Co.Rgb{gv, gv, gv} : Co.Rgb}
  +cube = {Co.Rgb{Co.at(Co.levels(), ri), Co.at(Co.levels(), gi), Co.at(Co.levels(), bi)} : Co.Rgb}
  +spread = (U32.max(r, U32.max(g, b)) - U32.min(r, U32.min(g, b)) : U32)
  +lhs = Co.to256.of(r, g, b, ri, gi, bi, slot)
  %Color.color_dist_spec(c, gray) : {lhs == Color.th.pick(Bool.and(U32.is_lt(spread, 10), U32.is_lt(_, Color.th.dist(c, cube))), (232 + slot : U32), (16 + 36 * ri + 6 * gi + bi : U32)) : U32}
  %Color.color_dist_spec(c, cube) : {lhs == Color.th.pick(Bool.and(U32.is_lt(spread, 10), U32.is_lt(Co.dist(c, gray), _)), (232 + slot : U32), (16 + 36 * ri + 6 * gi + bi : U32)) : U32}
  PNear.cn.sel(Bool.and(U32.is_lt(spread, 10), U32.is_lt(Co.dist(c, gray), Co.dist(c, cube))), (232 + slot : U32), (16 + 36 * ri + 6 * gi + bi : U32))

def Color.color_to256_spec(c):
  match c:
    case Co.Rgb{+r, +g, +b}:
      +l = (299 * r + 587 * g + 114 * b : U32)
      +lhs = Co.to256(Co.Rgb{r, g, b})
      %Color.color_near_spec(r, Co.levels()) : {lhs == Color.th.to256.of(r, g, b, _, Color.th.nearest(g, Color.th.levels()), Color.th.nearest(b, Color.th.levels()), Color.th.nearest(l, Color.th.targets())) : U32}
      %Color.color_near_spec(g, Co.levels()) : {lhs == Color.th.to256.of(r, g, b, Co.near(r, Co.levels()), _, Color.th.nearest(b, Color.th.levels()), Color.th.nearest(l, Color.th.targets())) : U32}
      %Color.color_near_spec(b, Co.levels()) : {lhs == Color.th.to256.of(r, g, b, Co.near(r, Co.levels()), Co.near(g, Co.levels()), _, Color.th.nearest(l, Color.th.targets())) : U32}
      %Color.color_near_spec(l, Co.gray.targets()) : {lhs == Color.th.to256.of(r, g, b, Co.near(r, Co.levels()), Co.near(g, Co.levels()), Co.near(b, Co.levels()), _) : U32}
      ct.of(r, g, b, Co.near(r, Co.levels()), Co.near(g, Co.levels()), Co.near(b, Co.levels()), Co.near(l, Co.gray.targets()))
