# eukhe: the proof of LAW theme_status_sound: the test is the conjunction
# of the six pairs' differences, each the laws' th.apart once the code's
# table lookup is the laws' (PL.pl.at)

import Base
import ../../bend/color.bend as Co
import ../../bend/theme/bundled.bend as TBundled
import ../../bend/theme/palette.bend as TPalette
import ../../spec/theme/rules.bend as Ts
import ../../laws/theme.bend as Theme
import ./base.bend as LA
import ./theme_legible_sound.bend as PL

def ps.ne(+xs: List<&2, Co.Rgb>, +a: Nat, +b: Nat, h: {U32.is_ne(Co.to256(TPalette.at(xs, a)), Co.to256(TPalette.at(xs, b))) == True{} : Bool}) -> {Theme.th.apart(xs, a, b) == True{} : Bool}:
  %PL.pl.at(xs, a) : {Bool.not(U32.is_eq(Co.to256(_), Co.to256(Ts.get(xs, b)))) == True{} : Bool}
  %PL.pl.at(xs, b) : {Bool.not(U32.is_eq(Co.to256(TPalette.at(xs, a)), Co.to256(_))) == True{} : Bool}
  h

def ps.sound(+xs: List<&2, Co.Rgb>, +ok: {TBundled.status_distinct(xs) == True{} : Bool})
  -> {[Theme.th.apart(xs, 0n, 4n), Theme.th.apart(xs, 0n, 6n), Theme.th.apart(xs, 0n, 5n), Theme.th.apart(xs, 4n, 6n), Theme.th.apart(xs, 4n, 5n), Theme.th.apart(xs, 6n, 5n)] == [True{}, True{}, True{}, True{}, True{}, True{}] : List<&2, Bool>}:
  +a = Co.to256(TPalette.at(xs, 0n))
  +b = Co.to256(TPalette.at(xs, 4n))
  +c = Co.to256(TPalette.at(xs, 6n))
  +d = Co.to256(TPalette.at(xs, 5n))
  +na = Bool.and(U32.is_ne(a, b), Bool.and(U32.is_ne(a, c), Bool.and(U32.is_ne(a, d), True{})))
  +nb = Bool.and(U32.is_ne(b, c), Bool.and(U32.is_ne(b, d), True{}))
  +nc = Bool.and(U32.is_ne(c, d), True{})
  +rest = Bool.and(nb, Bool.and(nc, Bool.and(True{}, True{})))
  +ha = LA.themes.pt.and_l(na, rest, ok)
  +hr = LA.themes.pt.and_r(na, rest, ok)
  +hb = LA.themes.pt.and_l(nb, Bool.and(nc, Bool.and(True{}, True{})), hr)
  +hc = LA.themes.pt.and_l(nc, Bool.and(True{}, True{}), LA.themes.pt.and_r(nb, Bool.and(nc, Bool.and(True{}, True{})), hr))
  +ab = LA.themes.pt.and_l(U32.is_ne(a, b), Bool.and(U32.is_ne(a, c), Bool.and(U32.is_ne(a, d), True{})), ha)
  +ha2 = LA.themes.pt.and_r(U32.is_ne(a, b), Bool.and(U32.is_ne(a, c), Bool.and(U32.is_ne(a, d), True{})), ha)
  +ac = LA.themes.pt.and_l(U32.is_ne(a, c), Bool.and(U32.is_ne(a, d), True{}), ha2)
  +ad = LA.themes.pt.and_l(U32.is_ne(a, d), True{}, LA.themes.pt.and_r(U32.is_ne(a, c), Bool.and(U32.is_ne(a, d), True{}), ha2))
  +bc = LA.themes.pt.and_l(U32.is_ne(b, c), Bool.and(U32.is_ne(b, d), True{}), hb)
  +bd = LA.themes.pt.and_l(U32.is_ne(b, d), True{}, LA.themes.pt.and_r(U32.is_ne(b, c), Bool.and(U32.is_ne(b, d), True{}), hb))
  +cd = LA.themes.pt.and_l(U32.is_ne(c, d), True{}, hc)
  %Equal.sym(Bool, Theme.th.apart(xs, 0n, 4n), True{}, ps.ne(xs, 0n, 4n, ab)) : {[_, Theme.th.apart(xs, 0n, 6n), Theme.th.apart(xs, 0n, 5n), Theme.th.apart(xs, 4n, 6n), Theme.th.apart(xs, 4n, 5n), Theme.th.apart(xs, 6n, 5n)] == [True{}, True{}, True{}, True{}, True{}, True{}] : List<&2, Bool>}
  %Equal.sym(Bool, Theme.th.apart(xs, 0n, 6n), True{}, ps.ne(xs, 0n, 6n, ac)) : {[True{}, _, Theme.th.apart(xs, 0n, 5n), Theme.th.apart(xs, 4n, 6n), Theme.th.apart(xs, 4n, 5n), Theme.th.apart(xs, 6n, 5n)] == [True{}, True{}, True{}, True{}, True{}, True{}] : List<&2, Bool>}
  %Equal.sym(Bool, Theme.th.apart(xs, 0n, 5n), True{}, ps.ne(xs, 0n, 5n, ad)) : {[True{}, True{}, _, Theme.th.apart(xs, 4n, 6n), Theme.th.apart(xs, 4n, 5n), Theme.th.apart(xs, 6n, 5n)] == [True{}, True{}, True{}, True{}, True{}, True{}] : List<&2, Bool>}
  %Equal.sym(Bool, Theme.th.apart(xs, 4n, 6n), True{}, ps.ne(xs, 4n, 6n, bc)) : {[True{}, True{}, True{}, _, Theme.th.apart(xs, 4n, 5n), Theme.th.apart(xs, 6n, 5n)] == [True{}, True{}, True{}, True{}, True{}, True{}] : List<&2, Bool>}
  %Equal.sym(Bool, Theme.th.apart(xs, 4n, 5n), True{}, ps.ne(xs, 4n, 5n, bd)) : {[True{}, True{}, True{}, True{}, _, Theme.th.apart(xs, 6n, 5n)] == [True{}, True{}, True{}, True{}, True{}, True{}] : List<&2, Bool>}
  %Equal.sym(Bool, Theme.th.apart(xs, 6n, 5n), True{}, ps.ne(xs, 6n, 5n, cd)) : {[True{}, True{}, True{}, True{}, True{}, _] == [True{}, True{}, True{}, True{}, True{}, True{}] : List<&2, Bool>}
  {==}

def Theme.theme_status_sound(xs, ok):
  ps.sound(xs, ok)
