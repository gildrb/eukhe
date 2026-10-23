# eukhe: lemmas the proofs of area admission share: admission/ended

import Base
import ../../../../bend/admission.bend as Ad
import ../logic.bend as LALogic

def ad.end_mark(t: List<&2, Ad.Tk>, +c: Ad.Cls, k: Nat, e: {Ad.ended(Ad.get(t, k)) == True{} : Bool}) -> {Ad.ended(Ad.get(Ad.mark(c, t), k)) == True{} : Bool}:
  match t:
    case Nil{}:
      e
    case Ad.Tk{+hc, +hs} <> +r:
      match hc hs:
        case Ad.Ia{} Ad.Queued{}:
          match c k:
            case Ad.Ia{} 0n:
              LALogic.ad.absurd({Ad.ended(Some{Ad.Tk{Ad.Ia{}, Ad.Granted{}}}) == True{} : Bool}, e)
            case Ad.Ia{} 1n+p:
              e
            case Ad.Bg{} 0n:
              e
            case Ad.Bg{} 1n+p:
              ad.end_mark(r, Ad.Bg{}, p, e)
        case Ad.Bg{} Ad.Queued{}:
          match c k:
            case Ad.Bg{} 0n:
              LALogic.ad.absurd({Ad.ended(Some{Ad.Tk{Ad.Bg{}, Ad.Granted{}}}) == True{} : Bool}, e)
            case Ad.Bg{} 1n+p:
              e
            case Ad.Ia{} 0n:
              e
            case Ad.Ia{} 1n+p:
              ad.end_mark(r, Ad.Ia{}, p, e)
        case _ Ad.Granted{}:
          match k:
            case 0n:
              e
            case 1n+p:
              ad.end_mark(r, c, p, e)
        case _ Ad.Held{}:
          match k:
            case 0n:
              e
            case 1n+p:
              ad.end_mark(r, c, p, e)
        case _ Ad.Preempted{}:
          match k:
            case 0n:
              e
            case 1n+p:
              ad.end_mark(r, c, p, e)
        case _ Ad.Ended{}:
          match k:
            case 0n:
              e
            case 1n+p:
              ad.end_mark(r, c, p, e)

def ad.end_grant_k(n: Nat, d: Maybe<&2, Ad.Cls>, +l: Ad.Lim, +t: List<&2, Ad.Tk>, +k: Nat, e: {Ad.ended(Ad.get(t, k)) == True{} : Bool}) -> {Ad.ended(Ad.get(Ad.grant.go(n, d, l, t), k)) == True{} : Bool}:
  match n d:
    case 0n _:
      e
    case 1n+f None{}:
      e
    case 1n+f Some{+c}:
      ad.end_grant_k(f, Ad.pick(l, Ad.mark(c, t)), l, Ad.mark(c, t), k, ad.end_mark(t, c, k, e))
