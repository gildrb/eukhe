# eukhe: the proof of LAW call_blocks_at_most_budget

import Base
import ../../bend/job.bend as Jb
import ../../laws/job.bend as Job
import ../base/bool/misc.bend as LBoolMisc

# Blocking calls
# --------------

def pj.blocks(es: List<&2, Jb.JEv>, +b: Nat, long: {Nat.is_le(b, Jb.ticks(es)) == True{} : Bool}) -> {Maybe.is_some(&2, Jb.Wait, Jb.wait(es, b)) == True{} : Bool}:
  match es:
    case Nil{}:
      match b:
        case 0n:
          {==}
        case 1n+l:
          LBoolMisc.pj.absurdF({Maybe.is_some(&2, Jb.Wait, Jb.wait(Nil{}, 1n+l)) == True{} : Bool}, long)
    case e <> rest:
      match e:
        case Jb.Out{n}:
          match b:
            case 0n:
              {==}
            case 1n+l:
              pj.blocks(rest, 1n+l, long)
        case Jb.Quit{q}:
          match b:
            case 0n:
              {==}
            case 1n+l:
              {==}
        case Jb.Kill{}:
          match b:
            case 0n:
              {==}
            case 1n+l:
              {==}
        case Jb.Tick{}:
          match b:
            case 0n:
              {==}
            case 1n+l:
              pj.blocks(rest, l, long)

def pj.call_blocks_at_most_budget(+b: Nat, +es: List<&2, Jb.JEv>, long: {Nat.is_le(b, Jb.ticks(es)) == True{} : Bool}) -> {Maybe.is_some(&2, Jb.Wait, Jb.wait(es, b)) == True{} : Bool}:
  pj.blocks(es, b, long)

def Job.call_blocks_at_most_budget(b, es, long):
  pj.call_blocks_at_most_budget(b, es, long)
