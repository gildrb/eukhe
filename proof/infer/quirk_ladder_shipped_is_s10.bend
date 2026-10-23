# eukhe: the proof of LAW quirk_ladder_shipped_is_s10

import Base
import ../../bend/infer.bend as If
import ../../bend/effort.bend as Ef
import ../../LAWS.bend as Laws
import ../base.bend as L

# with the shipped default ladder, the ladder rule keeps what S10 keeps
def pq.lad_ship_e(e: Ef.Ent, l: Ef.Lv) -> {If.lad.keep(l, e, If.Defaults.reasoning(If.lad.shipped())) == Ef.keep.e(l, e) : Bool}:
  match e l:
    case Ef.Null{} _:
      {==}
    case Ef.Wire{} _:
      {==}
    case Ef.Missing{} Ef.Off{}:
      {==}
    case Ef.Missing{} Ef.Minimal{}:
      {==}
    case Ef.Missing{} Ef.Low{}:
      {==}
    case Ef.Missing{} Ef.Medium{}:
      {==}
    case Ef.Missing{} Ef.High{}:
      {==}
    case Ef.Missing{} Ef.Xhigh{}:
      {==}
    case Ef.Missing{} Ef.Max{}:
      {==}

def pq.lad_ks(+map: Ef.LvMap, +l: Ef.Lv) -> {Ef.keep(If.lad.fill(map, If.Defaults.reasoning(If.lad.shipped())), l) == Ef.keep(map, l) : Bool}:
  +S = If.Defaults.reasoning(If.lad.shipped())
  Equal.trans(Bool, Ef.keep(If.lad.fill(map, S), l), If.lad.keep(l, Ef.entry(l, map), S), Ef.keep(map, l), L.pq.lad_fill_keep(map, S, l), pq.lad_ship_e(Ef.entry(l, map), l))

def pq.lad_offer_fill(+map: Ef.LvMap, xs: List<&2, Ef.Lv>) -> {Ef.offer(If.lad.fill(map, If.Defaults.reasoning(If.lad.shipped())), xs) == Ef.offer(map, xs) : List<&2, Ef.Lv>}:
  match xs:
    case Nil{}:
      {==}
    case +x <> rest:
      +F = If.lad.fill(map, If.Defaults.reasoning(If.lad.shipped()))
      %pq.lad_ks(map, x) : {Ef.cons_if(Ef.keep(F, x), x, Ef.offer(F, rest)) == Ef.cons_if(_, x, Ef.offer(map, rest)) : List<&2, Ef.Lv>}
      %pq.lad_offer_fill(map, rest) : {Ef.cons_if(Ef.keep(F, x), x, Ef.offer(F, rest)) == Ef.cons_if(Ef.keep(F, x), x, _) : List<&2, Ef.Lv>}
      {==}

def pq.quirk_ladder_shipped_is_s10(r: Bool, +map: Ef.LvMap) -> {If.lad.offered.of(r, map, If.lad.shipped()) == Ef.offered(Ef.Mdl{r, map}) : List<&2, Ef.Lv>}:
  match r:
    case True{}:
      pq.lad_offer_fill(map, Ef.ladder())
    case False{}:
      {==}

def Laws.quirk_ladder_shipped_is_s10(r, map):
  pq.quirk_ladder_shipped_is_s10(r, map)
