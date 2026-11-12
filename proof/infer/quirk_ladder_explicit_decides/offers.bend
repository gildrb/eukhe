# eukhe: the lemma of LAW quirk_ladder_explicit_decides, quirk_ladder_rule_decides and
# quirk_ladder_default_decides: a reasoning model with the chosen map C
# offers a level exactly as the table `ladder.offers` reads C's entry

import Base
import ../../../bend/effort.bend as Ef
import ../../../bend/infer.bend as If
import ../../../laws/infer.bend as Infer
import ../../base/effort.bend as LEffort
import ../../effort/base.bend as LEB

# the code's rule for one entry is the table's row
def ld.keep(e: Ef.Ent, +l: Ef.Lv, +dl: List<&2, Ef.Lv>) -> {If.lad.keep(l, e, dl) == Infer.ladder.offers(e, Ef.has(dl, l)) : Bool}:
  match e:
    case Ef.Missing{}:
      {==}
    case Ef.Null{}:
      {==}
    case Ef.Wire{}:
      {==}

# the offer of the map C filled with the default ladder D lists l exactly
# when the table keeps C's entry of l
def ld.offers(+C: Ef.LvMap, +D: List<&2, Ef.Lv>, +l: Ef.Lv) -> {Ef.has(Ef.offer(If.lad.fill(C, D), Ef.ladder()), l) == Infer.ladder.offers(Ef.entry(l, C), Ef.has(D, l)) : Bool}:
  +F = If.lad.fill(C, D)
  +E = Ef.entry(l, C)
  Equal.trans(Bool, Ef.has(Ef.offer(F, Ef.ladder()), l), Ef.keep(F, l), Infer.ladder.offers(E, Ef.has(D, l)), LEB.pq.lad_has_keep(F, l),
    Equal.trans(Bool, Ef.keep(F, l), If.lad.keep(l, E, D), Infer.ladder.offers(E, Ef.has(D, l)), LEffort.pq.lad_fill_keep(C, D, l), ld.keep(E, l, D)))

# a map with no entry leaves every level to the default ladder
def ld.none(l: Ef.Lv, b: Bool) -> {Infer.ladder.offers(Ef.entry(l, Ef.LvMap.none()), b) == b : Bool}:
  match l:
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
