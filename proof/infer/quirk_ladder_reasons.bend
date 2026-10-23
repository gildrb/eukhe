# eukhe: the proof of LAW quirk_ladder_reasons

import Base
import ../../bend/infer.bend as If
import ../../bend/effort.bend as Ef
import ../../LAWS.bend as Laws
import ../base.bend as L

# The ladder model and the strict plan
# -----------------------------------

def w2.we(e: Ef.Ent) -> {Laws.ladder.is_wire(e) == If.lad.wired.e(e) : Bool}:
  match e:
    case Ef.Missing{}:
      {==}
    case Ef.Null{}:
      {==}
    case Ef.Wire{}:
      {==}

def w2.or_false(b: Bool) -> {Bool.or(b, False{}) == b : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def w2.wired(+m: Ef.LvMap) -> {If.lad.wired(m) == Laws.ladder.wired.go(Ef.ladder(), m) : Bool}:
  match m:
    case Ef.LvMap{+o, +mi, +lo, +me, +hi, +xh, +mx}:
      %w2.we(o) : {Bool.or(_, Bool.or(If.lad.wired.e(mi), Bool.or(If.lad.wired.e(lo), Bool.or(If.lad.wired.e(me), Bool.or(If.lad.wired.e(hi), Bool.or(If.lad.wired.e(xh), If.lad.wired.e(mx))))))) == Laws.ladder.wired.go(Ef.ladder(), Ef.LvMap{o, mi, lo, me, hi, xh, mx}) : Bool}
      %w2.we(mi) : {Bool.or(Laws.ladder.is_wire(o), Bool.or(_, Bool.or(If.lad.wired.e(lo), Bool.or(If.lad.wired.e(me), Bool.or(If.lad.wired.e(hi), Bool.or(If.lad.wired.e(xh), If.lad.wired.e(mx))))))) == Laws.ladder.wired.go(Ef.ladder(), Ef.LvMap{o, mi, lo, me, hi, xh, mx}) : Bool}
      %w2.we(lo) : {Bool.or(Laws.ladder.is_wire(o), Bool.or(Laws.ladder.is_wire(mi), Bool.or(_, Bool.or(If.lad.wired.e(me), Bool.or(If.lad.wired.e(hi), Bool.or(If.lad.wired.e(xh), If.lad.wired.e(mx))))))) == Laws.ladder.wired.go(Ef.ladder(), Ef.LvMap{o, mi, lo, me, hi, xh, mx}) : Bool}
      %w2.we(me) : {Bool.or(Laws.ladder.is_wire(o), Bool.or(Laws.ladder.is_wire(mi), Bool.or(Laws.ladder.is_wire(lo), Bool.or(_, Bool.or(If.lad.wired.e(hi), Bool.or(If.lad.wired.e(xh), If.lad.wired.e(mx))))))) == Laws.ladder.wired.go(Ef.ladder(), Ef.LvMap{o, mi, lo, me, hi, xh, mx}) : Bool}
      %w2.we(hi) : {Bool.or(Laws.ladder.is_wire(o), Bool.or(Laws.ladder.is_wire(mi), Bool.or(Laws.ladder.is_wire(lo), Bool.or(Laws.ladder.is_wire(me), Bool.or(_, Bool.or(If.lad.wired.e(xh), If.lad.wired.e(mx))))))) == Laws.ladder.wired.go(Ef.ladder(), Ef.LvMap{o, mi, lo, me, hi, xh, mx}) : Bool}
      %w2.we(xh) : {Bool.or(Laws.ladder.is_wire(o), Bool.or(Laws.ladder.is_wire(mi), Bool.or(Laws.ladder.is_wire(lo), Bool.or(Laws.ladder.is_wire(me), Bool.or(Laws.ladder.is_wire(hi), Bool.or(_, If.lad.wired.e(mx))))))) == Laws.ladder.wired.go(Ef.ladder(), Ef.LvMap{o, mi, lo, me, hi, xh, mx}) : Bool}
      %w2.we(mx) : {Bool.or(Laws.ladder.is_wire(o), Bool.or(Laws.ladder.is_wire(mi), Bool.or(Laws.ladder.is_wire(lo), Bool.or(Laws.ladder.is_wire(me), Bool.or(Laws.ladder.is_wire(hi), Bool.or(Laws.ladder.is_wire(xh), _)))))) == Laws.ladder.wired.go(Ef.ladder(), Ef.LvMap{o, mi, lo, me, hi, xh, mx}) : Bool}
      %w2.or_false(Laws.ladder.is_wire(mx)) : {Bool.or(Laws.ladder.is_wire(o), Bool.or(Laws.ladder.is_wire(mi), Bool.or(Laws.ladder.is_wire(lo), Bool.or(Laws.ladder.is_wire(me), Bool.or(Laws.ladder.is_wire(hi), Bool.or(Laws.ladder.is_wire(xh), _)))))) == Laws.ladder.wired.go(Ef.ladder(), Ef.LvMap{o, mi, lo, me, hi, xh, mx}) : Bool}
      {==}

def Laws.quirk_ladder_reasons(f, bm, L.explicit):
  match f bm:
    case True{} _:
      {==}
    case False{} False{}:
      {==}
    case False{} True{}:
      match L.explicit:
        case None{}:
          {==}
        case Some{+m}:
          w2.wired(m)
