# eukhe: the proof of LAW tx_gapless

import Base
import ../../bend/screen.bend as Sc
import ../../laws/screen.bend as Screen
import ../base/logic/logic.bend as LLogicLogic

# a new active block at the end changes no gap
def ps.gapp(bs: List<&2, Sc.Blk>, +i: Nat, +l: Nat, +seen: Bool) -> {Sc.gapless.go(bs, seen) == Sc.gapless.go(List.append(&2, Sc.Blk, bs, [Sc.Blk{i, Sc.Active{}, l}]), seen) : Bool}:
  match bs:
    case Nil{}:
      {==}
    case b <> rest:
      match b:
        case Sc.Blk{bi, s, bl}:
          match s:
            case Sc.Comm{}:
              match seen:
                case True{}:
                  {==}
                case False{}:
                  ps.gapp(rest, i, l, False{})
            case Sc.Final{}:
              ps.gapp(rest, i, l, True{})
            case Sc.Active{}:
              ps.gapp(rest, i, l, True{})

# a growth or a final changes no gap
def ps.gedit(bs: List<&2, Sc.Blk>, +x: Nat, hit: Bool, +g: Maybe<&2, Nat>, +seen: Bool) -> {Sc.gapless.go(bs, seen) == Sc.gapless.go(Sc.edit.go(bs, x, g, hit), seen) : Bool}:
  match bs:
    case Nil{}:
      {==}
    case b <> +rest:
      match b:
        case Sc.Blk{i, s, l}:
          match s:
            case Sc.Comm{}:
              match hit:
                case True{}:
                  match g:
                    case None{}:
                      match seen:
                        case True{}:
                          {==}
                        case False{}:
                          ps.gedit(rest, x, Sc.bid.at(rest, x), None{}, False{})
                    case Some{n}:
                      match seen:
                        case True{}:
                          {==}
                        case False{}:
                          ps.gedit(rest, x, Sc.bid.at(rest, x), Some{n}, False{})
                case False{}:
                  match seen:
                    case True{}:
                      {==}
                    case False{}:
                      ps.gedit(rest, x, Sc.bid.at(rest, x), g, False{})
            case Sc.Final{}:
              match hit:
                case True{}:
                  match g:
                    case None{}:
                      ps.gedit(rest, x, Sc.bid.at(rest, x), None{}, True{})
                    case Some{n}:
                      ps.gedit(rest, x, Sc.bid.at(rest, x), Some{n}, True{})
                case False{}:
                  ps.gedit(rest, x, Sc.bid.at(rest, x), g, True{})
            case Sc.Active{}:
              match hit:
                case True{}:
                  match g:
                    case None{}:
                      ps.gedit(rest, x, Sc.bid.at(rest, x), None{}, True{})
                    case Some{n}:
                      ps.gedit(rest, x, Sc.bid.at(rest, x), Some{n}, True{})
                case False{}:
                  ps.gedit(rest, x, Sc.bid.at(rest, x), g, True{})

# a flush of blocks without a gap after `seen` leaves no gap
def ps.gflush(bs: List<&2, Sc.Blk>, seen: Bool, h: {Sc.gapless.go(bs, seen) == True{} : Bool}) -> {Sc.gapless.go(Sc.flush(bs), False{}) == True{} : Bool}:
  match bs:
    case Nil{}:
      {==}
    case b <> rest:
      match b:
        case Sc.Blk{i, s, l}:
          match s:
            case Sc.Comm{}:
              match seen:
                case True{}:
                  LLogicLogic.screen.ps.absurdF({Sc.gapless.go(Sc.flush(Sc.Blk{i, Sc.Comm{}, l} <> rest), False{}) == True{} : Bool}, h)
                case False{}:
                  ps.gflush(rest, False{}, h)
            case Sc.Final{}:
              ps.gflush(rest, True{}, h)
            case Sc.Active{}:
              h

def ps.gstep(+t: Sc.Tx, +e: Sc.Ev, h: {Sc.gapless(Sc.Tx.blocks(t)) == True{} : Bool}) -> {Sc.gapless(Sc.Tx.blocks(Sc.step(t, e))) == True{} : Bool}:
  match t:
    case Sc.Tx{+bs, +n, w}:
      match e:
        case Sc.Open{}:
          %ps.gapp(bs, n, 0n, False{}) : {_ == True{} : Bool}
          h
        case Sc.Grow{+x, k}:
          %ps.gedit(bs, x, Sc.bid.at(bs, x), Some{k}, False{}) : {_ == True{} : Bool}
          h
        case Sc.Fin{+x}:
          %ps.gedit(bs, x, Sc.bid.at(bs, x), None{}, False{}) : {_ == True{} : Bool}
          h
        case Sc.Flush{}:
          ps.gflush(bs, False{}, h)
        case Sc.Resize{v}:
          h

def ps.grun(es: List<&2, Sc.Ev>, +t: Sc.Tx, h: {Sc.gapless(Sc.Tx.blocks(t)) == True{} : Bool}) -> {Sc.gapless(Sc.Tx.blocks(Sc.run(es, t))) == True{} : Bool}:
  match es:
    case Nil{}:
      h
    case +e <> rest:
      ps.grun(rest, Sc.step(t, e), ps.gstep(t, e, h))

def ps.tx_gapless(es: List<&2, Sc.Ev>, +w: Nat) -> {Sc.gapless(Sc.Tx.blocks(Sc.run(es, Sc.Tx{Nil{}, 0n, w}))) == True{} : Bool}:
  ps.grun(es, Sc.Tx{Nil{}, 0n, w}, {==})

# (S8) The interface

def Screen.tx_gapless(es, w):
  ps.tx_gapless(es, w)
