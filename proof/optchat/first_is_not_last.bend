# eukhe: the proof of LAW first_is_not_last

import Base
import ../../bend/optchat.bend as O
import ../../bend/spec.bend as S
import ../../LAWS.bend as Laws

# Unit when the view's first line is at level 3, Empty otherwise
def push.disc(v: List<&2, O.Node>) -> Type:
  match v:
    case Nil{}:
      Empty
    case h <> t:
      match h:
        case O.Node{l, i}:
          match l:
            case 0n:
              Empty
            case 1n+a:
              match a:
                case 0n:
                  Empty
                case 1n+b:
                  match b:
                    case 0n:
                      Empty
                    case 1n+c:
                      Unit

def first_is_not_last() -> {O.fit.view(O.First{}, S.ten(), 3n, 0n, O.All{1n}, S.view10()) != O.fit.view(O.Last{}, S.ten(), 3n, 0n, O.All{1n}, S.view10()) : List<&2, O.Node>}:
  e =>
    %e : push.disc(_)
    Unit{}

def Laws.first_is_not_last():
  first_is_not_last()
