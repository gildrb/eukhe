# eukhe: the proof of LAW theme_hit_witness: induction on the candidates;
# the candidate that makes hit true is valid and named n, so src splits
# around it (the split of the rest, extended by one candidate, otherwise)

import Base
import ../../bend/theme/name.bend as TName
import ../../laws/theme_pick.bend as ThemePick
import ../theme/base.bend as LA

def hw.cons(+c: TName.Cand, -rest: List<&2, TName.Cand>, -n: String, w: ThemePick.th.HitAt(rest, n)) -> ThemePick.th.HitAt(c <> rest, n):
  match w:
    case (pre, w1):
      match w1:
        case (nm, w2):
          match w2:
            case (id, w3):
              match w3:
                case (post, w4):
                  match w4:
                    case (e, s):
                      (c <> pre, (nm, (id, (post, (Equal.cong(List<&2, TName.Cand>, List<&2, TName.Cand>, xs => c <> xs, rest, List.append(&2, TName.Cand, pre, TName.Cand{nm, True{}, id} <> post), e), s)))))

def hw.here(b: Bool, +nm: String, +id: U32, +rest: List<&2, TName.Cand>, +n: String, hb: {String.eq(nm, n) == b : Bool}, h: {Bool.or(b, TName.hit(rest, n)) == True{} : Bool}, ih: {TName.hit(rest, n) == True{} : Bool} -> ThemePick.th.HitAt(rest, n)) -> ThemePick.th.HitAt(TName.Cand{nm, True{}, id} <> rest, n):
  match b:
    case True{}:
      (Nil{}, (nm, (id, (rest, ({==}, hb)))))
    case False{}:
      hw.cons(TName.Cand{nm, True{}, id}, rest, n, ih(h))

def hw.valid(v: Bool, +nm: String, +id: U32, +rest: List<&2, TName.Cand>, +n: String, h: {Bool.or(Bool.and(v, String.eq(nm, n)), TName.hit(rest, n)) == True{} : Bool}, ih: {TName.hit(rest, n) == True{} : Bool} -> ThemePick.th.HitAt(rest, n)) -> ThemePick.th.HitAt(TName.Cand{nm, v, id} <> rest, n):
  match v:
    case True{}:
      hw.here(String.eq(nm, n), nm, id, rest, n, {==}, h, ih)
    case False{}:
      hw.cons(TName.Cand{nm, False{}, id}, rest, n, ih(h))

def hw.wit(src: List<&2, TName.Cand>, +n: String, h: {TName.hit(src, n) == True{} : Bool}) -> ThemePick.th.HitAt(src, n):
  match src:
    case Nil{}:
      LA.themes.pt.absurdF(ThemePick.th.HitAt(Nil{}, n), h)
    case Con{c, +rest}:
      match c:
        case TName.Cand{+nm, v, +id}:
          hw.valid(v, nm, id, rest, n, h, hr => hw.wit(rest, n, hr))

def ThemePick.theme_hit_witness(src, n, h):
  hw.wit(src, n, h)
