# eukhe: the proof of LAW facts_tier_price_codex_oracle

import Base
import ../../bend/facts.bend as Fx
import ../../laws/facts.bend as Facts

def pf.facts_tier_price_codex_oracle(m: Nat, t: Nat) -> {Maybe.default(&2, Nat, Fx.price(Fx.prices.codex(), m, t), 100n) == Fx.price.old.codex(m, t) : Nat}:
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
              {==}

def Facts.facts_tier_price_codex_oracle(m, t):
  pf.facts_tier_price_codex_oracle(m, t)
