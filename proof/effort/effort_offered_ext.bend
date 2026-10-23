# eukhe: the proof of LAW effort_offered_ext

import Base
import ../../bend/effort.bend as Ef
import ../../LAWS.bend as Laws
import ./base.bend as LA

def pe.not_t(b: Bool, h: {Bool.not(b) == True{} : Bool}) -> {b == False{} : Bool}:
  match b:
    case True{}:
      LA.pe.absurdF({True{} == False{} : Bool}, h)
    case False{}:
      {==}

# a level in the filter's result passes the filter
def pe.offer_in.at(+map: Ef.LvMap, +xs: List<&2, Ef.Lv>, +l: Ef.Lv, k: Bool, ek: {Ef.keep(map, l) == k : Bool}, h: {Ef.has(Ef.offer(map, xs), l) == True{} : Bool}) -> {Ef.keep(map, l) == True{} : Bool}:
  match k:
    case True{}:
      ek
    case False{}:
      +out = LA.pe.offer_out(map, xs, l, LA.pe.kat(map, xs), {==}, Ef.at(xs, l), {==}, ek)
      LA.pe.absurd({Ef.keep(map, l) == True{} : Bool}, Equal.trans(Bool, True{}, Ef.has(Ef.offer(map, xs), l), False{}, Equal.sym(Bool, Ef.has(Ef.offer(map, xs), l), True{}, h), out))

def pe.offer_in(+map: Ef.LvMap, +xs: List<&2, Ef.Lv>, +l: Ef.Lv, h: {Ef.has(Ef.offer(map, xs), l) == True{} : Bool}) -> {Ef.keep(map, l) == True{} : Bool}:
  pe.offer_in.at(map, xs, l, Ef.keep(map, l), {==}, h)

# a level kept with entry e that is xhigh or max has a wire entry
def pe.wire(+l: Ef.Lv, e: Ef.Ent, x: {Ef.ext(l) == True{} : Bool}, k: {Ef.keep.e(l, e) == True{} : Bool}) -> {e == Ef.Wire{} : Ef.Ent}:
  match e:
    case Ef.Missing{}:
      +nx = pe.not_t(Ef.ext(l), k)
      LA.pe.absurd({Ef.Missing{} == Ef.Wire{} : Ef.Ent}, Equal.trans(Bool, True{}, Ef.ext(l), False{}, Equal.sym(Bool, Ef.ext(l), True{}, x), nx))
    case Ef.Null{}:
      LA.pe.absurdF({Ef.Null{} == Ef.Wire{} : Ef.Ent}, k)
    case Ef.Wire{}:
      {==}

def pe.or_false_t(c: Bool, h: {Bool.or(c, False{}) == True{} : Bool}) -> {c == True{} : Bool}:
  match c:
    case True{}:
      {==}
    case False{}:
      h

def pe.effort_offered_ext(r: Bool, +map: Ef.LvMap, +l: Ef.Lv, x: {Ef.ext(l) == True{} : Bool}, in: {Ef.has(Ef.offered(Ef.Mdl{r, map}), l) == True{} : Bool}) -> {Ef.entry(l, map) == Ef.Wire{} : Ef.Ent}:
  match r:
    case True{}:
      pe.wire(l, Ef.entry(l, map), x, pe.offer_in(map, Ef.ladder(), l, in))
    case False{}:
      +same = Equal.cong(Ef.Lv, Bool, v => Ef.ext(v), Ef.Off{}, l, LA.pe.lv_true(Ef.Off{}, l, pe.or_false_t(Ef.Lv.eq(Ef.Off{}, l), in)))
      LA.pe.absurdF({Ef.entry(l, map) == Ef.Wire{} : Ef.Ent}, Equal.trans(Bool, False{}, Ef.ext(l), True{}, same, x))

def Laws.effort_offered_ext(r, map, l, x, in):
  pe.effort_offered_ext(r, map, l, x, in)
