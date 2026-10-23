# eukhe: lemmas the proofs of two or more areas share: effort

import Base
import ../../bend/effort.bend as Ef
import ../../bend/infer.bend as If

def pq.lad_kb(+l: Ef.Lv, b: Bool) -> {Ef.keep.e(l, If.lad.ent(b)) == b : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def pq.lad_kf(+l: Ef.Lv, e: Ef.Ent, +dl: List<&2, Ef.Lv>) -> {Ef.keep.e(l, If.lad.fill.e(l, e, dl)) == If.lad.keep(l, e, dl) : Bool}:
  match e:
    case Ef.Missing{}:
      pq.lad_kb(l, Ef.has(dl, l))
    case Ef.Null{}:
      {==}
    case Ef.Wire{}:
      {==}

# the filled map keeps a level exactly when the ladder rule does
def pq.lad_fill_keep(map: Ef.LvMap, +dl: List<&2, Ef.Lv>, l: Ef.Lv) -> {Ef.keep(If.lad.fill(map, dl), l) == If.lad.keep(l, Ef.entry(l, map), dl) : Bool}:
  match map:
    case Ef.LvMap{o, mi, lo, me, hi, xh, mx}:
      match l:
        case Ef.Off{}:
          pq.lad_kf(Ef.Off{}, o, dl)
        case Ef.Minimal{}:
          pq.lad_kf(Ef.Minimal{}, mi, dl)
        case Ef.Low{}:
          pq.lad_kf(Ef.Low{}, lo, dl)
        case Ef.Medium{}:
          pq.lad_kf(Ef.Medium{}, me, dl)
        case Ef.High{}:
          pq.lad_kf(Ef.High{}, hi, dl)
        case Ef.Xhigh{}:
          pq.lad_kf(Ef.Xhigh{}, xh, dl)
        case Ef.Max{}:
          pq.lad_kf(Ef.Max{}, mx, dl)
