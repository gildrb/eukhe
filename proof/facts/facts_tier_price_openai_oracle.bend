# eukhe: the proof of LAW facts_tier_price_openai_oracle

import Base
import ../../bend/facts.bend as Fx
import ../../LAWS.bend as Laws

def pf.facts_tier_price_openai_oracle(m: Nat, t: Nat) -> {Maybe.default(&2, Nat, Fx.price(Fx.prices.openai(), m, t), 100n) == Fx.price.old.openai(m, t) : Nat}:
  match m t:
    case 0n 0n:
      {==}
    case 0n 1n+a:
      match a:
        case 0n:
          {==}
        case 1n+b:
          match b:
            case 0n:
              {==}
            case 1n+c:
              match c:
                case 0n:
                  {==}
                case 1n+d:
                  {==}
    case 1n+p 0n:
      {==}
    case 1n+p 1n+a:
      match a:
        case 0n:
          {==}
        case 1n+b:
          match b:
            case 0n:
              {==}
            case 1n+c:
              match c:
                case 0n:
                  {==}
                case 1n+d:
                  {==}

def Laws.facts_tier_price_openai_oracle(m, t):
  pf.facts_tier_price_openai_oracle(m, t)
