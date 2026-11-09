# eukhe: the proof of LAW quirk_ladder_default_decides

import Base
import ../../bend/effort.bend as Ef
import ../../bend/infer.bend as If
import ../../laws/infer.bend as Infer
import ./quirk_ladder_explicit_decides/offers.bend as LD

def Infer.quirk_ladder_default_decides(d, l):
  +D = If.Defaults.reasoning(d)
  +N = Ef.LvMap.none()
  Equal.trans(Bool, Ef.has(Ef.offer(If.lad.fill(N, D), Ef.ladder()), l), Infer.ladder.offers(Ef.entry(l, N), Ef.has(D, l)), Ef.has(D, l), LD.ld.offers(N, D, l), LD.ld.none(l, Ef.has(D, l)))
