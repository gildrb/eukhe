# eukhe: the proof of LAW facts_effort_exact
# The entry of the level is the same field of the map; a missing or null
# entry takes the same default.

import Base
import ../../bend/facts.bend as Fx
import ../../laws/facts.bend as Facts

def fee.of(e: Maybe<&2, Maybe<&2, Nat>>, l: Fx.ELv) -> {Fx.effort.of(e, l) == Facts.effort_spec.of(e, Facts.effort_spec.dflt(l)) : Nat}:
  match e:
    case None{}:
      match l:
        case Fx.EMinimal{}:
          {==}
        case Fx.ELow{}:
          {==}
        case Fx.EMedium{}:
          {==}
        case Fx.EHigh{}:
          {==}
        case Fx.EXhigh{}:
          {==}
        case Fx.EMax{}:
          {==}
    case Some{w}:
      match w:
        case None{}:
          match l:
            case Fx.EMinimal{}:
              {==}
            case Fx.ELow{}:
              {==}
            case Fx.EMedium{}:
              {==}
            case Fx.EHigh{}:
              {==}
            case Fx.EXhigh{}:
              {==}
            case Fx.EMax{}:
              {==}
        case Some{v}:
          {==}

def Facts.facts_effort_exact(m, l):
  match m:
    case Fx.EMap{mi, lo, me, hi, xh, mx}:
      match l:
        case Fx.EMinimal{}:
          fee.of(mi, Fx.EMinimal{})
        case Fx.ELow{}:
          fee.of(lo, Fx.ELow{})
        case Fx.EMedium{}:
          fee.of(me, Fx.EMedium{})
        case Fx.EHigh{}:
          fee.of(hi, Fx.EHigh{})
        case Fx.EXhigh{}:
          fee.of(xh, Fx.EXhigh{})
        case Fx.EMax{}:
          fee.of(mx, Fx.EMax{})
