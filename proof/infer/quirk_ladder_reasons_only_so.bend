# eukhe: the proof of LAW quirk_ladder_reasons_only_so

import Base
import ../../bend/effort.bend as Ef
import ../../bend/infer.bend as If
import ../../laws/infer.bend as Infer
import ../base/logic/logic.bend as LLogicLogic

# a level of m with a wire entry
def ro.G(m: Ef.LvMap) -> Type:
  &l: Ef.Lv -> {Ef.entry(l, m) == Ef.Wire{} : Ef.Ent}

# the scan of the map from max: a wire entry is found
def ro.f6(o: Ef.Ent, mi: Ef.Ent, lo: Ef.Ent, me: Ef.Ent, hi: Ef.Ent, xh: Ef.Ent, mx: Ef.Ent, h: {If.lad.wired.e(mx) == True{} : Bool}) -> ro.G(Ef.LvMap{o, mi, lo, me, hi, xh, mx}):
  match mx:
    case Ef.Wire{}:
      (Ef.Max{}, {==})
    case Ef.Missing{}:
      LLogicLogic.absurd(ro.G(Ef.LvMap{o, mi, lo, me, hi, xh, Ef.Missing{}}), h)
    case Ef.Null{}:
      LLogicLogic.absurd(ro.G(Ef.LvMap{o, mi, lo, me, hi, xh, Ef.Null{}}), h)

def ro.f5(o: Ef.Ent, mi: Ef.Ent, lo: Ef.Ent, me: Ef.Ent, hi: Ef.Ent, xh: Ef.Ent, mx: Ef.Ent, h: {Bool.or(If.lad.wired.e(xh), If.lad.wired.e(mx)) == True{} : Bool}) -> ro.G(Ef.LvMap{o, mi, lo, me, hi, xh, mx}):
  match xh:
    case Ef.Wire{}:
      (Ef.Xhigh{}, {==})
    case Ef.Missing{}:
      ro.f6(o, mi, lo, me, hi, Ef.Missing{}, mx, h)
    case Ef.Null{}:
      ro.f6(o, mi, lo, me, hi, Ef.Null{}, mx, h)

def ro.f4(o: Ef.Ent, mi: Ef.Ent, lo: Ef.Ent, me: Ef.Ent, hi: Ef.Ent, xh: Ef.Ent, mx: Ef.Ent, h: {Bool.or(If.lad.wired.e(hi), Bool.or(If.lad.wired.e(xh), If.lad.wired.e(mx))) == True{} : Bool}) -> ro.G(Ef.LvMap{o, mi, lo, me, hi, xh, mx}):
  match hi:
    case Ef.Wire{}:
      (Ef.High{}, {==})
    case Ef.Missing{}:
      ro.f5(o, mi, lo, me, Ef.Missing{}, xh, mx, h)
    case Ef.Null{}:
      ro.f5(o, mi, lo, me, Ef.Null{}, xh, mx, h)

def ro.f3(o: Ef.Ent, mi: Ef.Ent, lo: Ef.Ent, me: Ef.Ent, hi: Ef.Ent, xh: Ef.Ent, mx: Ef.Ent, h: {Bool.or(If.lad.wired.e(me), Bool.or(If.lad.wired.e(hi), Bool.or(If.lad.wired.e(xh), If.lad.wired.e(mx)))) == True{} : Bool}) -> ro.G(Ef.LvMap{o, mi, lo, me, hi, xh, mx}):
  match me:
    case Ef.Wire{}:
      (Ef.Medium{}, {==})
    case Ef.Missing{}:
      ro.f4(o, mi, lo, Ef.Missing{}, hi, xh, mx, h)
    case Ef.Null{}:
      ro.f4(o, mi, lo, Ef.Null{}, hi, xh, mx, h)

def ro.f2(o: Ef.Ent, mi: Ef.Ent, lo: Ef.Ent, me: Ef.Ent, hi: Ef.Ent, xh: Ef.Ent, mx: Ef.Ent, h: {Bool.or(If.lad.wired.e(lo), Bool.or(If.lad.wired.e(me), Bool.or(If.lad.wired.e(hi), Bool.or(If.lad.wired.e(xh), If.lad.wired.e(mx))))) == True{} : Bool}) -> ro.G(Ef.LvMap{o, mi, lo, me, hi, xh, mx}):
  match lo:
    case Ef.Wire{}:
      (Ef.Low{}, {==})
    case Ef.Missing{}:
      ro.f3(o, mi, Ef.Missing{}, me, hi, xh, mx, h)
    case Ef.Null{}:
      ro.f3(o, mi, Ef.Null{}, me, hi, xh, mx, h)

def ro.f1(o: Ef.Ent, mi: Ef.Ent, lo: Ef.Ent, me: Ef.Ent, hi: Ef.Ent, xh: Ef.Ent, mx: Ef.Ent, h: {Bool.or(If.lad.wired.e(mi), Bool.or(If.lad.wired.e(lo), Bool.or(If.lad.wired.e(me), Bool.or(If.lad.wired.e(hi), Bool.or(If.lad.wired.e(xh), If.lad.wired.e(mx)))))) == True{} : Bool}) -> ro.G(Ef.LvMap{o, mi, lo, me, hi, xh, mx}):
  match mi:
    case Ef.Wire{}:
      (Ef.Minimal{}, {==})
    case Ef.Missing{}:
      ro.f2(o, Ef.Missing{}, lo, me, hi, xh, mx, h)
    case Ef.Null{}:
      ro.f2(o, Ef.Null{}, lo, me, hi, xh, mx, h)

def ro.f0(o: Ef.Ent, mi: Ef.Ent, lo: Ef.Ent, me: Ef.Ent, hi: Ef.Ent, xh: Ef.Ent, mx: Ef.Ent, h: {If.lad.wired(Ef.LvMap{o, mi, lo, me, hi, xh, mx}) == True{} : Bool}) -> ro.G(Ef.LvMap{o, mi, lo, me, hi, xh, mx}):
  match o:
    case Ef.Wire{}:
      (Ef.Off{}, {==})
    case Ef.Missing{}:
      ro.f1(Ef.Missing{}, mi, lo, me, hi, xh, mx, h)
    case Ef.Null{}:
      ro.f1(Ef.Null{}, mi, lo, me, hi, xh, mx, h)

def ro.goal(bm: Bool, ex: Maybe<&2, Ef.LvMap>) -> Type:
  &m: Ef.LvMap -> &l: Ef.Lv -> {(bm, (ex, Ef.entry(l, m))) == (True{}, (Some{m}, Ef.Wire{})) : Bool & (Maybe<&2, Ef.LvMap> & Ef.Ent)}

def ro.eq(+M: Ef.LvMap, +l: Ef.Lv, e: {Ef.entry(l, M) == Ef.Wire{} : Ef.Ent}) -> {(True{}, (Some{M}, Ef.entry(l, M))) == (True{}, (Some{M}, Ef.Wire{})) : Bool & (Maybe<&2, Ef.LvMap> & Ef.Ent)}:
  %Equal.sym(Ef.Ent, Ef.entry(l, M), Ef.Wire{}, e) : {(True{}, (Some{M}, _)) == (True{}, (Some{M}, Ef.Wire{})) : Bool & (Maybe<&2, Ef.LvMap> & Ef.Ent)}
  {==}

def ro.at(+M: Ef.LvMap, g: ro.G(M)) -> ro.goal(True{}, Some{M}):
  (+l, e) = g
  (M, (l, ro.eq(M, l, e)))

def ro.main(bm: Bool, ex: Maybe<&2, Ef.LvMap>, ok: {If.lad.reasons(False{}, bm, ex) == True{} : Bool}) -> ro.goal(bm, ex):
  match bm:
    case False{}:
      LLogicLogic.absurd(ro.goal(False{}, ex), ok)
    case True{}:
      match ex:
        case None{}:
          LLogicLogic.absurd(ro.goal(True{}, None{}), ok)
        case Some{m}:
          match m:
            case Ef.LvMap{+o, +mi, +lo, +me, +hi, +xh, +mx}:
              ro.at(Ef.LvMap{o, mi, lo, me, hi, xh, mx}, ro.f0(o, mi, lo, me, hi, xh, mx, ok))

def Infer.quirk_ladder_reasons_only_so(bm, ex, ok):
  ro.main(bm, ex, ok)
