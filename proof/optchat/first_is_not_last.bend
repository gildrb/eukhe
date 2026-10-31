# eukhe: the proof of LAW first_is_not_last

import Base
import ../../bend/optchat/fit.bend as OFit
import ../../bend/optchat/info.bend as OInfo
import ../../bend/optchat/node.bend as ONode
import ../../spec/memory/optchat.bend as S
import ../../laws/optchat.bend as Optchat

# Unit when the view's first line is at level 3, Empty otherwise
def push.disc(v: List<&2, ONode.Node>) -> Type:
  match v:
    case Nil{}:
      Empty
    case h <> t:
      match h:
        case ONode.Node{l, i}:
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

def first_is_not_last() -> {OFit.fit.view(OFit.First{}, S.ten(), 3n, 0n, OInfo.All{1n}, S.view10()) != OFit.fit.view(OFit.Last{}, S.ten(), 3n, 0n, OInfo.All{1n}, S.view10()) : List<&2, ONode.Node>}:
  e =>
    %e : push.disc(_)
    Unit{}

def Optchat.first_is_not_last():
  first_is_not_last()
