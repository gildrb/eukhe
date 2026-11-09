# eukhe: the proof of LAW quirk_ladder_map_reasons

import Base
import ../../bend/effort.bend as Ef
import ../../bend/infer.bend as If
import ../../laws/infer.bend as Infer

# the tails of the scan of a map, from xhigh back to minimal
def mr.t5(xh: Ef.Ent, mx: Ef.Ent) -> Bool:
  Bool.or(If.lad.wired.e(xh), If.lad.wired.e(mx))

def mr.t4(hi: Ef.Ent, xh: Ef.Ent, mx: Ef.Ent) -> Bool:
  Bool.or(If.lad.wired.e(hi), mr.t5(xh, mx))

def mr.t3(me: Ef.Ent, hi: Ef.Ent, xh: Ef.Ent, mx: Ef.Ent) -> Bool:
  Bool.or(If.lad.wired.e(me), mr.t4(hi, xh, mx))

def mr.t2(lo: Ef.Ent, me: Ef.Ent, hi: Ef.Ent, xh: Ef.Ent, mx: Ef.Ent) -> Bool:
  Bool.or(If.lad.wired.e(lo), mr.t3(me, hi, xh, mx))

def mr.t1(mi: Ef.Ent, lo: Ef.Ent, me: Ef.Ent, hi: Ef.Ent, xh: Ef.Ent, mx: Ef.Ent) -> Bool:
  Bool.or(If.lad.wired.e(mi), mr.t2(lo, me, hi, xh, mx))

# an or whose right side holds holds
def mr.or_t(a: Bool, -b: Bool, h: {b == True{} : Bool}) -> {Bool.or(a, b) == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      h

# a wire entry makes the scan from it hold
def mr.hit(e: Ef.Ent, -b: Bool, w: {e == Ef.Wire{} : Ef.Ent}) -> {Bool.or(If.lad.wired.e(e), b) == True{} : Bool}:
  %Equal.sym(Ef.Ent, e, Ef.Wire{}, w) : {Bool.or(If.lad.wired.e(_), b) == True{} : Bool}
  {==}

def mr.last(e: Ef.Ent, w: {e == Ef.Wire{} : Ef.Ent}) -> {If.lad.wired.e(e) == True{} : Bool}:
  %Equal.sym(Ef.Ent, e, Ef.Wire{}, w) : {If.lad.wired.e(_) == True{} : Bool}
  {==}

# a map that gives level l a wire string gives some level one
def mr.wired(m: Ef.LvMap, l: Ef.Lv, w: {Ef.entry(l, m) == Ef.Wire{} : Ef.Ent}) -> {If.lad.wired(m) == True{} : Bool}:
  match m:
    case Ef.LvMap{o, mi, lo, me, hi, xh, mx}:
      match l:
        case Ef.Off{}:
          mr.hit(o, mr.t1(mi, lo, me, hi, xh, mx), w)
        case Ef.Minimal{}:
          mr.or_t(If.lad.wired.e(o), mr.t1(mi, lo, me, hi, xh, mx), mr.hit(mi, mr.t2(lo, me, hi, xh, mx), w))
        case Ef.Low{}:
          mr.or_t(If.lad.wired.e(o), mr.t1(mi, lo, me, hi, xh, mx), mr.or_t(If.lad.wired.e(mi), mr.t2(lo, me, hi, xh, mx), mr.hit(lo, mr.t3(me, hi, xh, mx), w)))
        case Ef.Medium{}:
          mr.or_t(If.lad.wired.e(o), mr.t1(mi, lo, me, hi, xh, mx), mr.or_t(If.lad.wired.e(mi), mr.t2(lo, me, hi, xh, mx), mr.or_t(If.lad.wired.e(lo), mr.t3(me, hi, xh, mx), mr.hit(me, mr.t4(hi, xh, mx), w))))
        case Ef.High{}:
          mr.or_t(If.lad.wired.e(o), mr.t1(mi, lo, me, hi, xh, mx), mr.or_t(If.lad.wired.e(mi), mr.t2(lo, me, hi, xh, mx), mr.or_t(If.lad.wired.e(lo), mr.t3(me, hi, xh, mx), mr.or_t(If.lad.wired.e(me), mr.t4(hi, xh, mx), mr.hit(hi, mr.t5(xh, mx), w)))))
        case Ef.Xhigh{}:
          mr.or_t(If.lad.wired.e(o), mr.t1(mi, lo, me, hi, xh, mx), mr.or_t(If.lad.wired.e(mi), mr.t2(lo, me, hi, xh, mx), mr.or_t(If.lad.wired.e(lo), mr.t3(me, hi, xh, mx), mr.or_t(If.lad.wired.e(me), mr.t4(hi, xh, mx), mr.or_t(If.lad.wired.e(hi), mr.t5(xh, mx), mr.hit(xh, If.lad.wired.e(mx), w))))))
        case Ef.Max{}:
          mr.or_t(If.lad.wired.e(o), mr.t1(mi, lo, me, hi, xh, mx), mr.or_t(If.lad.wired.e(mi), mr.t2(lo, me, hi, xh, mx), mr.or_t(If.lad.wired.e(lo), mr.t3(me, hi, xh, mx), mr.or_t(If.lad.wired.e(me), mr.t4(hi, xh, mx), mr.or_t(If.lad.wired.e(hi), mr.t5(xh, mx), mr.or_t(If.lad.wired.e(xh), If.lad.wired.e(mx), mr.last(mx, w)))))))

def Infer.quirk_ladder_map_reasons(f, m, l, w):
  match f:
    case True{}:
      {==}
    case False{}:
      mr.wired(m, l, w)
