# eukhe: the proof of LAW orphan_sound_iff
# By cases on the state, then on the exit's abort flag, busy flag and work.

import Base
import ../../bend/orphan.bend as Or
import ../../laws/orphan.bend as Orphan
import ../base/terms.bend as LT

def osi.If(b: Bool, A: Type) -> Type:
  match b:
    case True{}:
      Unit
    case False{}:
      A

def osi.absurd(-A: Type, e: {True{} == False{} : Bool}) -> A:
  %e : osi.If(_, A)
  Unit{}

def osi.sound_in(+e: Or.Exit, aborted: Bool, busy: Bool, work: Or.Work, h: Or.Sound(Or.Exited{Or.Out{e, work, busy, aborted}})) -> {Orphan.sound_spec(Or.Exited{Or.Out{e, work, busy, aborted}}) == True{} : Bool}:
  match aborted:
    case True{}:
      (h1, h2) = h
      osi.absurd({Orphan.sound_spec(Or.Exited{Or.Out{e, work, busy, True{}}}) == True{} : Bool}, h1)
    case False{}:
      match busy:
        case True{}:
          match work:
            case Or.Idle{}:
              (h1, h2) = h
              osi.absurd({Orphan.sound_spec(Or.Exited{Or.Out{e, Or.Idle{}, True{}, False{}}}) == True{} : Bool}, h2)
            case Or.Ongoing{}:
              {==}
        case False{}:
          match work:
            case Or.Idle{}:
              {==}
            case Or.Ongoing{}:
              (h1, h2) = h
              LT.lt.absurd({Orphan.sound_spec(Or.Exited{Or.Out{e, Or.Ongoing{}, False{}, False{}}}) == True{} : Bool}, h2)

def osi.sound_out(+e: Or.Exit, aborted: Bool, busy: Bool, work: Or.Work, c: {Orphan.sound_spec(Or.Exited{Or.Out{e, work, busy, aborted}}) == True{} : Bool}) -> Or.Sound(Or.Exited{Or.Out{e, work, busy, aborted}}):
  match aborted:
    case True{}:
      LT.lt.absurd(Or.Sound(Or.Exited{Or.Out{e, work, busy, True{}}}), c)
    case False{}:
      match busy:
        case True{}:
          match work:
            case Or.Idle{}:
              LT.lt.absurd(Or.Sound(Or.Exited{Or.Out{e, Or.Idle{}, True{}, False{}}}), c)
            case Or.Ongoing{}:
              ({==}, {==})
        case False{}:
          match work:
            case Or.Idle{}:
              ({==}, {==})
            case Or.Ongoing{}:
              LT.lt.absurd(Or.Sound(Or.Exited{Or.Out{e, Or.Ongoing{}, False{}, False{}}}), c)

# Orphan

def Orphan.orphan_sound_iff(s):
  match s:
    case Or.Live{w}:
      (x => {==}, c => Unit{})
    case Or.Exited{d}:
      match d:
        case Or.Out{+e, +work, +busy, +aborted}:
          (h => osi.sound_in(e, aborted, busy, work, h), c => osi.sound_out(e, aborted, busy, work, c))
