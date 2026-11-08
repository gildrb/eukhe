# eukhe: the proof of LAW facts_reasoning_exact
# By the shape; GPT by the entry, then the level (each default is a
# literal); gpt-oss by the level.

import Base
import ../../bend/facts.bend as Fx
import ../../laws/facts/model.bend as Facts

def fre.dflt(l: Fx.ELv) -> {Fx.RNested{Fx.gpt.default(l)} == Fx.RNested{Facts.reasoning_spec.gpt(l)} : Fx.RFields}:
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

def fre.gpt(e: Maybe<&2, Maybe<&2, Nat>>, +l: Fx.ELv) -> {Fx.RNested{Fx.gpt.of(e, l)} == Fx.RNested{Facts.reasoning_spec.wire(e, Facts.reasoning_spec.gpt(l))} : Fx.RFields}:
  match e:
    case None{}:
      fre.dflt(l)
    case Some{w}:
      match w:
        case None{}:
          fre.dflt(l)
        case Some{v}:
          {==}

def fre.oss(l: Fx.ELv) -> {Fx.RFlat{Fx.oss.effort(l)} == Fx.RFlat{Nat.min(4n, Facts.reasoning_spec.gpt(l))} : Fx.RFields}:
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

def Facts.facts_reasoning_exact(s, e, l):
  match s:
    case None{}:
      {==}
    case Some{x}:
      match x:
        case Fx.SClaude{}:
          {==}
        case Fx.SGpt{}:
          fre.gpt(e, l)
        case Fx.SGptOss{}:
          fre.oss(l)
