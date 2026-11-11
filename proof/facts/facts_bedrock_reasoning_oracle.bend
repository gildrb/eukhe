# eukhe: the proof of LAW facts_bedrock_reasoning_oracle
# By the old checks in their order; each effort table by the level, GPT's
# by the entry first.

import Base
import ../../bend/facts.bend as Fx
import ../../laws/facts/model.bend as Facts

def fbro.table(l: Fx.ELv) -> {Fx.RNested{Fx.reasoning.old.table(l)} == Fx.RNested{Fx.gpt.default(l)} : Fx.RFields}:
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

def fbro.gpt(e: Maybe<&2, Maybe<&2, Nat>>, +l: Fx.ELv) -> {Fx.RNested{Fx.reasoning.old.gpt(e, l)} == Fx.RNested{Fx.gpt.of(e, l)} : Fx.RFields}:
  match e:
    case None{}:
      fbro.table(l)
    case Some{w}:
      match w:
        case None{}:
          fbro.table(l)
        case Some{v}:
          {==}

def fbro.oss(l: Fx.ELv) -> {Fx.RFlat{Fx.reasoning.old.oss(l)} == Fx.RFlat{Fx.oss.effort(l)} : Fx.RFields}:
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

def Facts.facts_bedrock_reasoning_oracle(cl, oss, gpt, e, l):
  match cl:
    case True{}:
      {==}
    case False{}:
      match oss:
        case True{}:
          fbro.oss(l)
        case False{}:
          match gpt:
            case True{}:
              fbro.gpt(e, l)
            case False{}:
              {==}
