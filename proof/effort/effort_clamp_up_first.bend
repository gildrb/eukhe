# eukhe: the proof of LAW effort_clamp_up_first
#
# The clamp scans l, then up the ladder from l, then down from the level
# below l to off: the scan meets k after passed-over levels only
# (cn.cov_scan, a closed table over every l and k), and a passed-over level
# of a clear list is not offered (cn.clear_out), so the scan stops at k.
# When the scan meets no level the clamp falls to the first offered level,
# which is off (cn.first_off). An offered l is k itself (cn.self_eq).

import Base
import ../../bend/effort.bend as Ef
import ../../laws/effort/depth.bend as Effort
import ./base.bend as LA

# y equal to a skipped x yet not skipped: impossible
def cn.contra(+l: Ef.Lv, +k: Ef.Lv, -y: Ef.Lv, -x: Ef.Lv, eq: {y == x : Ef.Lv}, hy: {Bool.not(Effort.effort_skipped(l, k, y)) == True{} : Bool}, sk: {Effort.effort_skipped(l, k, x) == True{} : Bool}) -> {False{} == True{} : Bool}:
  %sk : {Bool.not(_) == True{} : Bool}
  %eq : {Bool.not(Effort.effort_skipped(l, k, _)) == True{} : Bool}
  hy

def cn.clear_out.at(+y: Ef.Lv, +x: Ef.Lv, b: Bool, e: {Ef.Lv.eq(y, x) == b : Bool}, rest: List<&2, Ef.Lv>, +l: Ef.Lv, +k: Ef.Lv, hy: {Bool.not(Effort.effort_skipped(l, k, y)) == True{} : Bool}, sk: {Effort.effort_skipped(l, k, x) == True{} : Bool}, ih: {Ef.has(rest, x) == False{} : Bool}) -> {Bool.or(Ef.Lv.eq(y, x), Ef.has(rest, x)) == False{} : Bool}:
  match b:
    case True{}:
      LA.pe.absurdF({Bool.or(Ef.Lv.eq(y, x), Ef.has(rest, x)) == False{} : Bool}, cn.contra(l, k, y, x, LA.pe.lv_true(y, x, e), hy, sk))
    case False{}:
      %Equal.sym(Bool, Ef.Lv.eq(y, x), False{}, e) : {Bool.or(_, Ef.has(rest, x)) == False{} : Bool}
      ih

# a skipped level of a clear list is not in it
def cn.clear_out(xs: List<&2, Ef.Lv>, +l: Ef.Lv, +k: Ef.Lv, +x: Ef.Lv, +c: {Effort.effort_clear(xs, l, k) == True{} : Bool}, +sk: {Effort.effort_skipped(l, k, x) == True{} : Bool}) -> {Ef.has(xs, x) == False{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case +y <> +rest:
      +hy = LA.pe.and_l(Bool.not(Effort.effort_skipped(l, k, y)), Effort.effort_clear(rest, l, k), c)
      +hr = LA.pe.and_r(Bool.not(Effort.effort_skipped(l, k, y)), Effort.effort_clear(rest, l, k), c)
      cn.clear_out.at(y, x, Ef.Lv.eq(y, x), {==}, rest, l, k, hy, sk, cn.clear_out(rest, l, k, x, hr, sk))

# the levels of xs up to the first k, each but k skipped from l to k
def cn.cov(xs: List<&2, Ef.Lv>, +l: Ef.Lv, +k: Ef.Lv) -> Bool:
  match xs:
    case Nil{}:
      Ef.Lv.eq(k, Ef.Off{})
    case +x <> rest:
      Bool.or(Ef.Lv.eq(x, k), Bool.and(Effort.effort_skipped(l, k, x), cn.cov(rest, l, k)))

# the scan from l meets k after skipped levels only
def cn.cov_scan(l: Ef.Lv, k: Ef.Lv) -> {cn.cov(Ef.scan(l), l, k) == True{} : Bool}:
  match l:
    case Ef.Off{}:
      match k:
        case Ef.Off{}:
          {==}
        case Ef.Minimal{}:
          {==}
        case Ef.Low{}:
          {==}
        case Ef.Medium{}:
          {==}
        case Ef.High{}:
          {==}
        case Ef.Xhigh{}:
          {==}
        case Ef.Max{}:
          {==}
    case Ef.Minimal{}:
      match k:
        case Ef.Off{}:
          {==}
        case Ef.Minimal{}:
          {==}
        case Ef.Low{}:
          {==}
        case Ef.Medium{}:
          {==}
        case Ef.High{}:
          {==}
        case Ef.Xhigh{}:
          {==}
        case Ef.Max{}:
          {==}
    case Ef.Low{}:
      match k:
        case Ef.Off{}:
          {==}
        case Ef.Minimal{}:
          {==}
        case Ef.Low{}:
          {==}
        case Ef.Medium{}:
          {==}
        case Ef.High{}:
          {==}
        case Ef.Xhigh{}:
          {==}
        case Ef.Max{}:
          {==}
    case Ef.Medium{}:
      match k:
        case Ef.Off{}:
          {==}
        case Ef.Minimal{}:
          {==}
        case Ef.Low{}:
          {==}
        case Ef.Medium{}:
          {==}
        case Ef.High{}:
          {==}
        case Ef.Xhigh{}:
          {==}
        case Ef.Max{}:
          {==}
    case Ef.High{}:
      match k:
        case Ef.Off{}:
          {==}
        case Ef.Minimal{}:
          {==}
        case Ef.Low{}:
          {==}
        case Ef.Medium{}:
          {==}
        case Ef.High{}:
          {==}
        case Ef.Xhigh{}:
          {==}
        case Ef.Max{}:
          {==}
    case Ef.Xhigh{}:
      match k:
        case Ef.Off{}:
          {==}
        case Ef.Minimal{}:
          {==}
        case Ef.Low{}:
          {==}
        case Ef.Medium{}:
          {==}
        case Ef.High{}:
          {==}
        case Ef.Xhigh{}:
          {==}
        case Ef.Max{}:
          {==}
    case Ef.Max{}:
      match k:
        case Ef.Off{}:
          {==}
        case Ef.Minimal{}:
          {==}
        case Ef.Low{}:
          {==}
        case Ef.Medium{}:
          {==}
        case Ef.High{}:
          {==}
        case Ef.Xhigh{}:
          {==}
        case Ef.Max{}:
          {==}

# l is k or skipped from l to k
def cn.self(l: Ef.Lv, k: Ef.Lv) -> {Bool.or(Ef.Lv.eq(l, k), Effort.effort_skipped(l, k, l)) == True{} : Bool}:
  match l:
    case Ef.Off{}:
      match k:
        case Ef.Off{}:
          {==}
        case Ef.Minimal{}:
          {==}
        case Ef.Low{}:
          {==}
        case Ef.Medium{}:
          {==}
        case Ef.High{}:
          {==}
        case Ef.Xhigh{}:
          {==}
        case Ef.Max{}:
          {==}
    case Ef.Minimal{}:
      match k:
        case Ef.Off{}:
          {==}
        case Ef.Minimal{}:
          {==}
        case Ef.Low{}:
          {==}
        case Ef.Medium{}:
          {==}
        case Ef.High{}:
          {==}
        case Ef.Xhigh{}:
          {==}
        case Ef.Max{}:
          {==}
    case Ef.Low{}:
      match k:
        case Ef.Off{}:
          {==}
        case Ef.Minimal{}:
          {==}
        case Ef.Low{}:
          {==}
        case Ef.Medium{}:
          {==}
        case Ef.High{}:
          {==}
        case Ef.Xhigh{}:
          {==}
        case Ef.Max{}:
          {==}
    case Ef.Medium{}:
      match k:
        case Ef.Off{}:
          {==}
        case Ef.Minimal{}:
          {==}
        case Ef.Low{}:
          {==}
        case Ef.Medium{}:
          {==}
        case Ef.High{}:
          {==}
        case Ef.Xhigh{}:
          {==}
        case Ef.Max{}:
          {==}
    case Ef.High{}:
      match k:
        case Ef.Off{}:
          {==}
        case Ef.Minimal{}:
          {==}
        case Ef.Low{}:
          {==}
        case Ef.Medium{}:
          {==}
        case Ef.High{}:
          {==}
        case Ef.Xhigh{}:
          {==}
        case Ef.Max{}:
          {==}
    case Ef.Xhigh{}:
      match k:
        case Ef.Off{}:
          {==}
        case Ef.Minimal{}:
          {==}
        case Ef.Low{}:
          {==}
        case Ef.Medium{}:
          {==}
        case Ef.High{}:
          {==}
        case Ef.Xhigh{}:
          {==}
        case Ef.Max{}:
          {==}
    case Ef.Max{}:
      match k:
        case Ef.Off{}:
          {==}
        case Ef.Minimal{}:
          {==}
        case Ef.Low{}:
          {==}
        case Ef.Medium{}:
          {==}
        case Ef.High{}:
          {==}
        case Ef.Xhigh{}:
          {==}
        case Ef.Max{}:
          {==}

def cn.refl_t(+y: Ef.Lv, r: List<&2, Ef.Lv>) -> {True{} == Bool.or(Ef.Lv.eq(y, y), Ef.has(r, y)) : Bool}:
  %LA.pe.lv_refl(y) : {True{} == Bool.or(_, Ef.has(r, y)) : Bool}
  {==}

def cn.refl_contra(+y: Ef.Lv, +r: List<&2, Ef.Lv>, hy: {Bool.or(Ef.Lv.eq(y, y), Ef.has(r, y)) == False{} : Bool}) -> {True{} == False{} : Bool}:
  Equal.trans(Bool, True{}, Bool.or(Ef.Lv.eq(y, y), Ef.has(r, y)), False{}, cn.refl_t(y, r), hy)

# l is off and lad has off but not l: impossible
def cn.off_contra(+lad: List<&2, Ef.Lv>, -l: Ef.Lv, el: {l == Ef.Off{} : Ef.Lv}, hl: {Ef.has(lad, l) == False{} : Bool}, ho: {Ef.has(lad, Ef.Off{}) == True{} : Bool}) -> {False{} == True{} : Bool}:
  %hl : {_ == True{} : Bool}
  %Equal.sym(Ef.Lv, l, Ef.Off{}, el) : {Ef.has(lad, _) == True{} : Bool}
  ho

def cn.sk_off(l: Ef.Lv, y: Ef.Lv, el: {Ef.Lv.eq(l, Ef.Off{}) == False{} : Bool}, ey: {Ef.Lv.eq(y, Ef.Off{}) == False{} : Bool}) -> {Effort.effort_skipped(l, Ef.Off{}, y) == True{} : Bool}:
  match l:
    case Ef.Off{}:
      match y:
        case Ef.Off{}:
          LA.pe.absurd({Effort.effort_skipped(Ef.Off{}, Ef.Off{}, Ef.Off{}) == True{} : Bool}, el)
        case Ef.Minimal{}:
          LA.pe.absurd({Effort.effort_skipped(Ef.Off{}, Ef.Off{}, Ef.Minimal{}) == True{} : Bool}, el)
        case Ef.Low{}:
          LA.pe.absurd({Effort.effort_skipped(Ef.Off{}, Ef.Off{}, Ef.Low{}) == True{} : Bool}, el)
        case Ef.Medium{}:
          LA.pe.absurd({Effort.effort_skipped(Ef.Off{}, Ef.Off{}, Ef.Medium{}) == True{} : Bool}, el)
        case Ef.High{}:
          LA.pe.absurd({Effort.effort_skipped(Ef.Off{}, Ef.Off{}, Ef.High{}) == True{} : Bool}, el)
        case Ef.Xhigh{}:
          LA.pe.absurd({Effort.effort_skipped(Ef.Off{}, Ef.Off{}, Ef.Xhigh{}) == True{} : Bool}, el)
        case Ef.Max{}:
          LA.pe.absurd({Effort.effort_skipped(Ef.Off{}, Ef.Off{}, Ef.Max{}) == True{} : Bool}, el)
    case Ef.Minimal{}:
      match y:
        case Ef.Off{}:
          LA.pe.absurd({Effort.effort_skipped(Ef.Minimal{}, Ef.Off{}, Ef.Off{}) == True{} : Bool}, ey)
        case Ef.Minimal{}:
          {==}
        case Ef.Low{}:
          {==}
        case Ef.Medium{}:
          {==}
        case Ef.High{}:
          {==}
        case Ef.Xhigh{}:
          {==}
        case Ef.Max{}:
          {==}
    case Ef.Low{}:
      match y:
        case Ef.Off{}:
          LA.pe.absurd({Effort.effort_skipped(Ef.Low{}, Ef.Off{}, Ef.Off{}) == True{} : Bool}, ey)
        case Ef.Minimal{}:
          {==}
        case Ef.Low{}:
          {==}
        case Ef.Medium{}:
          {==}
        case Ef.High{}:
          {==}
        case Ef.Xhigh{}:
          {==}
        case Ef.Max{}:
          {==}
    case Ef.Medium{}:
      match y:
        case Ef.Off{}:
          LA.pe.absurd({Effort.effort_skipped(Ef.Medium{}, Ef.Off{}, Ef.Off{}) == True{} : Bool}, ey)
        case Ef.Minimal{}:
          {==}
        case Ef.Low{}:
          {==}
        case Ef.Medium{}:
          {==}
        case Ef.High{}:
          {==}
        case Ef.Xhigh{}:
          {==}
        case Ef.Max{}:
          {==}
    case Ef.High{}:
      match y:
        case Ef.Off{}:
          LA.pe.absurd({Effort.effort_skipped(Ef.High{}, Ef.Off{}, Ef.Off{}) == True{} : Bool}, ey)
        case Ef.Minimal{}:
          {==}
        case Ef.Low{}:
          {==}
        case Ef.Medium{}:
          {==}
        case Ef.High{}:
          {==}
        case Ef.Xhigh{}:
          {==}
        case Ef.Max{}:
          {==}
    case Ef.Xhigh{}:
      match y:
        case Ef.Off{}:
          LA.pe.absurd({Effort.effort_skipped(Ef.Xhigh{}, Ef.Off{}, Ef.Off{}) == True{} : Bool}, ey)
        case Ef.Minimal{}:
          {==}
        case Ef.Low{}:
          {==}
        case Ef.Medium{}:
          {==}
        case Ef.High{}:
          {==}
        case Ef.Xhigh{}:
          {==}
        case Ef.Max{}:
          {==}
    case Ef.Max{}:
      match y:
        case Ef.Off{}:
          LA.pe.absurd({Effort.effort_skipped(Ef.Max{}, Ef.Off{}, Ef.Off{}) == True{} : Bool}, ey)
        case Ef.Minimal{}:
          {==}
        case Ef.Low{}:
          {==}
        case Ef.Medium{}:
          {==}
        case Ef.High{}:
          {==}
        case Ef.Xhigh{}:
          {==}
        case Ef.Max{}:
          {==}

def cn.first_off.y(+y: Ef.Lv, +r: List<&2, Ef.Lv>, +l: Ef.Lv, c: Bool, ec: {Ef.Lv.eq(y, Ef.Off{}) == c : Bool}, el: {Ef.Lv.eq(l, Ef.Off{}) == False{} : Bool}, hc: {Effort.effort_clear(y <> r, l, Ef.Off{}) == True{} : Bool}) -> {y == Ef.Off{} : Ef.Lv}:
  match c:
    case True{}:
      LA.pe.lv_true(y, Ef.Off{}, ec)
    case False{}:
      +hy = cn.clear_out(y <> r, l, Ef.Off{}, y, hc, cn.sk_off(l, y, el, ec))
      LA.pe.absurd({y == Ef.Off{} : Ef.Lv}, cn.refl_contra(y, r, hy))

# with every level but off skipped, and l not in lad, lad starts at off
def cn.first_off(lad: List<&2, Ef.Lv>, +l: Ef.Lv, c: Bool, ec: {Ef.Lv.eq(l, Ef.Off{}) == c : Bool}, hc: {Effort.effort_clear(lad, l, Ef.Off{}) == True{} : Bool}, hl: {Ef.has(lad, l) == False{} : Bool}, ho: {Ef.has(lad, Ef.Off{}) == True{} : Bool}) -> {Ef.first(lad, Ef.Off{}) == Ef.Off{} : Ef.Lv}:
  match lad:
    case Nil{}:
      {==}
    case +y <> +r:
      match c:
        case True{}:
          LA.pe.absurdF({Ef.first(y <> r, Ef.Off{}) == Ef.Off{} : Ef.Lv}, cn.off_contra(y <> r, l, LA.pe.lv_true(l, Ef.Off{}, ec), hl, ho))
        case False{}:
          cn.first_off.y(y, r, l, Ef.Lv.eq(y, Ef.Off{}), {==}, ec, hc)

def cn.tr_has(+lad: List<&2, Ef.Lv>, -k: Ef.Lv, ek: {k == Ef.Off{} : Ef.Lv}, hk: {Ef.has(lad, k) == True{} : Bool}) -> {Ef.has(lad, Ef.Off{}) == True{} : Bool}:
  %ek : {Ef.has(lad, _) == True{} : Bool}
  hk

def cn.tr_clear(lad: List<&2, Ef.Lv>, +l: Ef.Lv, -k: Ef.Lv, ek: {k == Ef.Off{} : Ef.Lv}, hc: {Effort.effort_clear(lad, l, k) == True{} : Bool}) -> {Effort.effort_clear(lad, l, Ef.Off{}) == True{} : Bool}:
  %ek : {Effort.effort_clear(lad, l, _) == True{} : Bool}
  hc

# the scan stops at the first level of lad, which is k when only skipped levels come before it
def cn.find(xs: List<&2, Ef.Lv>, +lad: List<&2, Ef.Lv>, +l: Ef.Lv, +k: Ef.Lv, b: Bool, eb: {Ef.at(xs, k) == b : Bool}, +hk: {Ef.has(lad, k) == True{} : Bool}, +hc: {Effort.effort_clear(lad, l, k) == True{} : Bool}, +hl: {Ef.has(lad, l) == False{} : Bool}, +cv: {cn.cov(xs, l, k) == True{} : Bool}) -> {Ef.find.go(xs, lad, Ef.first(lad, Ef.Off{}), Ef.in.at(xs, lad)) == k : Ef.Lv}:
  match xs:
    case Nil{}:
      +ek = LA.pe.lv_true(k, Ef.Off{}, cv)
      %Equal.sym(Ef.Lv, k, Ef.Off{}, ek) : {Ef.first(lad, Ef.Off{}) == _ : Ef.Lv}
      cn.first_off(lad, l, Ef.Lv.eq(l, Ef.Off{}), {==}, cn.tr_clear(lad, l, k, ek, hc), hl, cn.tr_has(lad, k, ek, hk))
    case +x <> +rest:
      match b:
        case True{}:
          %Equal.sym(Ef.Lv, x, k, LA.pe.lv_true(x, k, eb)) : {Ef.find.go(_ <> rest, lad, Ef.first(lad, Ef.Off{}), Ef.has(lad, _)) == k : Ef.Lv}
          %Equal.sym(Bool, Ef.has(lad, k), True{}, hk) : {Ef.find.go(k <> rest, lad, Ef.first(lad, Ef.Off{}), _) == k : Ef.Lv}
          {==}
        case False{}:
          +h2 = LA.pe.or_l_false(Ef.Lv.eq(x, k), Bool.and(Effort.effort_skipped(l, k, x), cn.cov(rest, l, k)), eb, cv)
          +sk = LA.pe.and_l(Effort.effort_skipped(l, k, x), cn.cov(rest, l, k), h2)
          +cr = LA.pe.and_r(Effort.effort_skipped(l, k, x), cn.cov(rest, l, k), h2)
          +hx = cn.clear_out(lad, l, k, x, hc, sk)
          %Equal.sym(Bool, Ef.has(lad, x), False{}, hx) : {Ef.find.go(x <> rest, lad, Ef.first(lad, Ef.Off{}), _) == k : Ef.Lv}
          cn.find(rest, lad, l, k, Ef.at(rest, k), {==}, hk, hc, hl, cr)

def cn.self_eq(+lad: List<&2, Ef.Lv>, +l: Ef.Lv, +k: Ef.Lv, c: Bool, ec: {Ef.Lv.eq(l, k) == c : Bool}, eb: {Ef.has(lad, l) == True{} : Bool}, +hc: {Effort.effort_clear(lad, l, k) == True{} : Bool}) -> {l == k : Ef.Lv}:
  match c:
    case True{}:
      LA.pe.lv_true(l, k, ec)
    case False{}:
      +sk = LA.pe.or_l_false(Ef.Lv.eq(l, k), Effort.effort_skipped(l, k, l), ec, cn.self(l, k))
      +hx = cn.clear_out(lad, l, k, l, hc, sk)
      LA.pe.absurdF({l == k : Ef.Lv}, Equal.trans(Bool, False{}, Ef.has(lad, l), True{}, Equal.sym(Bool, Ef.has(lad, l), False{}, hx), eb))

def cn.clamp_at(b: Bool, +lad: List<&2, Ef.Lv>, +l: Ef.Lv, +k: Ef.Lv, eb: {Ef.has(lad, l) == b : Bool}, +hk: {Ef.has(lad, k) == True{} : Bool}, +hc: {Effort.effort_clear(lad, l, k) == True{} : Bool}) -> {Ef.clamp.at(b, l, lad) == k : Ef.Lv}:
  match b:
    case True{}:
      cn.self_eq(lad, l, k, Ef.Lv.eq(l, k), {==}, eb, hc)
    case False{}:
      cn.find(Ef.scan(l), lad, l, k, Ef.at(Ef.scan(l), k), {==}, hk, hc, eb, cn.cov_scan(l, k))

# the clamp lands where effort_lands says
def cn.near_clamp(+lad: List<&2, Ef.Lv>, +l: Ef.Lv, +k: Ef.Lv, +near: {Effort.effort_lands(lad, l, k) == True{} : Bool}) -> {Ef.clamp.in(lad, l) == k : Ef.Lv}:
  +hk = LA.pe.and_l(Ef.has(lad, k), Effort.effort_clear(lad, l, k), near)
  +hc = LA.pe.and_r(Ef.has(lad, k), Effort.effort_clear(lad, l, k), near)
  cn.clamp_at(Ef.has(lad, l), lad, l, k, {==}, hk, hc)

def Effort.effort_clamp_up_first(m, l, k, near):
  cn.near_clamp(Ef.offered(m), l, k, near)
