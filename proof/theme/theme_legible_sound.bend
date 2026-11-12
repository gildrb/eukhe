# eukhe: the proof of LAW theme_legible_sound: the test is a conjunction
# over the pairs, so it holding holds each pair's contrast (pl.go); the
# code's table lookup is the laws' (pl.at)

import Base
import ../../bend/color.bend as Co
import ../../bend/theme/bundled.bend as TBundled
import ../../bend/theme/palette.bend as TPalette
import ../../spec/theme/rules.bend as Ts
import ../../laws/theme.bend as Theme
import ./base.bend as LA

def pl.at(xs: List<&2, Co.Rgb>, k: Nat) -> {TPalette.at(xs, k) == Ts.get(xs, k) : Co.Rgb}:
  match xs k:
    case Nil{} q:
      {==}
    case Con{x, t} 0n:
      {==}
    case Con{x, t} 1n+p:
      pl.at(t, p)

def pl.go(+xs: List<&2, Co.Rgb>, pre: List<&2, TBundled.Duo>, +d: TBundled.Duo, +post: List<&2, TBundled.Duo>, h: {TBundled.legible.go(xs, List.append(&2, TBundled.Duo, pre, d <> post)) == True{} : Bool}) -> {TBundled.meets(xs, d) == True{} : Bool}:
  match pre:
    case Nil{}:
      LA.themes.pt.and_l(TBundled.meets(xs, d), TBundled.legible.go(xs, post), h)
    case Con{p, +rest}:
      pl.go(xs, rest, d, post, LA.themes.pt.and_r(TBundled.meets(xs, p), TBundled.legible.go(xs, List.append(&2, TBundled.Duo, rest, d <> post)), h))

def pl.sound(+xs: List<&2, Co.Rgb>, +pre: List<&2, TBundled.Duo>, +fg: Nat, +bg: Nat, +num: U32, +den: U32, +post: List<&2, TBundled.Duo>, at: {TBundled.pairs() == List.append(&2, TBundled.Duo, pre, TBundled.Duo{fg, bg, num, den} <> post) : List<&2, TBundled.Duo>}, ok: {TBundled.legible(xs) == True{} : Bool})
  -> {Co.contrast_ge(Ts.get(xs, fg), Ts.get(xs, bg), num, den) == True{} : Bool}:
  +l = List.append(&2, TBundled.Duo, pre, TBundled.Duo{fg, bg, num, den} <> post)
  +c = Equal.cong(List<&2, TBundled.Duo>, Bool, ps => TBundled.legible.go(xs, ps), TBundled.pairs(), l, at)
  +h = Equal.trans(Bool, TBundled.legible.go(xs, l), TBundled.legible.go(xs, TBundled.pairs()), True{}, Equal.sym(Bool, TBundled.legible.go(xs, TBundled.pairs()), TBundled.legible.go(xs, l), c), ok)
  %pl.at(xs, fg) : {Co.contrast_ge(_, Ts.get(xs, bg), num, den) == True{} : Bool}
  %pl.at(xs, bg) : {Co.contrast_ge(TPalette.at(xs, fg), _, num, den) == True{} : Bool}
  pl.go(xs, pre, TBundled.Duo{fg, bg, num, den}, post, h)

def Theme.theme_legible_sound(xs, pre, fg, bg, num, den, post, at, ok):
  pl.sound(xs, pre, fg, bg, num, den, post, at, ok)
