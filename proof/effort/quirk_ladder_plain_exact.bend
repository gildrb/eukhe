# eukhe: the proof of LAW quirk_ladder_plain_exact

import Base
import ../../bend/effort.bend as Ef
import ../../bend/infer.bend as If
import ../../laws/effort.bend as Effort
import ../base/effort.bend as LEffort
import ../base/fsmode.bend as LFsmode
import ./base.bend as LA

# a map with no entry leaves every level to the default ladder
def pq.lad_none(l: Ef.Lv, +dl: List<&2, Ef.Lv>) -> {If.lad.keep(l, Ef.entry(l, Ef.LvMap.none()), dl) == Ef.has(dl, l) : Bool}:
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

def pq.quirk_ladder_plain_exact(+explicit: Maybe<&2, Ef.LvMap>, +rule: Maybe<&2, Ef.LvMap>, +d: If.Defaults, +l: Ef.Lv) -> {Ef.has(If.lad.offered(False{}, explicit, rule, d), l) == Ef.has(If.Defaults.plain(d), l) : Bool}:
  +P = If.Defaults.plain(d)
  +N = Ef.LvMap.none()
  +F = If.lad.fill(N, P)
  +k = Equal.trans(Bool, Ef.keep(F, l), If.lad.keep(l, Ef.entry(l, N), P), Ef.has(P, l), LEffort.pq.lad_fill_keep(N, P, l), pq.lad_none(l, P))
  Equal.trans(Bool, Ef.has(Ef.offer(F, Ef.ladder()), l), Ef.keep(F, l), Ef.has(P, l), LA.pq.lad_has_keep(F, l), k)

def Effort.quirk_ladder_plain_exact(LFsmode.explicit, rule, d, l):
  pq.quirk_ladder_plain_exact(LFsmode.explicit, rule, d, l)
