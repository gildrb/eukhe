# eukhe: the proof of LAW facts_bedrock_effort_oracle
#
# PROOF: at every level but xhigh both read the map's entry with the same
# default (eo.of); at xhigh a model on the id list keeps the promise, so
# its map sends 5.

import Base
import ../../bend/facts.bend as Fx
import ../../laws/facts/model.bend as Facts
import ../base/logic/logic.bend as LLogicLogic
import ../base/nat.bend as LNat
import ../base/logic/nat.bend as LLogicNat
import ./base.bend as LA

# the model's effort of an entry is the old rule's, with the level's default d
def eo.of(+e: Maybe<&2, Maybe<&2, Nat>>, +l: Fx.ELv, +d: Nat, +hd: {Fx.effort.default(l) == d : Nat}) -> {Fx.effort.of(e, l) == Facts.effort_old.mapped(e, d) : Nat}:
  match e:
    case None{}:
      hd
    case Some{w}:
      match w:
        case None{}:
          hd
        case Some{v}:
          {==}

# a native-xhigh model whose map keeps the promise sends 5 at xhigh
def eo.xhigh(+xh: Maybe<&2, Maybe<&2, Nat>>, +ok: {Facts.effort_old.five(xh) == True{} : Bool}) -> {Fx.effort.of(xh, Fx.EXhigh{}) == 5n : Nat}:
  match xh:
    case None{}:
      LLogicLogic.pf.absurd_ft({Fx.effort.of(None{}, Fx.EXhigh{}) == 5n : Nat}, ok)
    case Some{w}:
      match w:
        case None{}:
          LLogicLogic.pf.absurd_ft({Fx.effort.of(Some{None{}}, Fx.EXhigh{}) == 5n : Nat}, ok)
        case Some{v}:
          LLogicNat.pq.eq_true(v, 5n, ok)

# off the id list: the map's entry with the old default at every level
def eo.off(+m: Fx.EMap, +l: Fx.ELv) -> {Fx.effort(m, l) == Facts.effort_old(False{}, Facts.effort_spec.at(m, l), l) : Nat}:
  match m:
    case Fx.EMap{mi, lo, me, hi, xh, mx}:
      match l:
        case Fx.EMinimal{}:
          eo.of(mi, Fx.EMinimal{}, 2n, {==})
        case Fx.ELow{}:
          eo.of(lo, Fx.ELow{}, 2n, {==})
        case Fx.EMedium{}:
          eo.of(me, Fx.EMedium{}, 3n, {==})
        case Fx.EHigh{}:
          eo.of(hi, Fx.EHigh{}, 4n, {==})
        case Fx.EXhigh{}:
          eo.of(xh, Fx.EXhigh{}, 4n, {==})
        case Fx.EMax{}:
          eo.of(mx, Fx.EMax{}, 4n, {==})

# on the id list: as off it, but 5 at xhigh, which a map that keeps the
# promise sends
def eo.on(+m: Fx.EMap, +l: Fx.ELv, +ok: {Facts.effort_old.kept(True{}, m) == True{} : Bool}) -> {Fx.effort(m, l) == Facts.effort_old(True{}, Facts.effort_spec.at(m, l), l) : Nat}:
  match m:
    case Fx.EMap{mi, lo, me, hi, xh, mx}:
      match l:
        case Fx.EMinimal{}:
          eo.of(mi, Fx.EMinimal{}, 2n, {==})
        case Fx.ELow{}:
          eo.of(lo, Fx.ELow{}, 2n, {==})
        case Fx.EMedium{}:
          eo.of(me, Fx.EMedium{}, 3n, {==})
        case Fx.EHigh{}:
          eo.of(hi, Fx.EHigh{}, 4n, {==})
        case Fx.EXhigh{}:
          eo.xhigh(xh, ok)
        case Fx.EMax{}:
          eo.of(mx, Fx.EMax{}, 4n, {==})

def eo.main(+native: Bool, +m: Fx.EMap, +l: Fx.ELv, +ok: {Facts.effort_old.kept(native, m) == True{} : Bool}) -> {Fx.effort(m, l) == Facts.effort_old(native, Facts.effort_spec.at(m, l), l) : Nat}:
  match native:
    case False{}:
      eo.off(m, l)
    case True{}:
      eo.on(m, l, ok)

def Facts.facts_bedrock_effort_oracle(native, m, l, ok):
  eo.main(native, m, l, ok)
