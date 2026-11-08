# eukhe: the proof of LAW path_looped_never_inside
#
# PROOF: the class of a path is the model's class of the real path it
# reaches, demoted by its loop (pcc.cls_eq); a looped demotion is never
# Inside (pli.demote: Inside becomes Outside, the others stay).

import Base
import ../../bend/path_policy.bend as Pp
import ../../laws/path_policy/policy.bend as PathPolicy
import ../base/logic/logic.bend as LLogicLogic
import ./base/class.bend as LAC

def pli.demote(c: Pp.Cls, h: {Pp.demote(c, True{}) == Pp.Inside{} : Pp.Cls}) -> Empty:
  match c:
    case Pp.Inside{}:
      %h : LLogicLogic.pp.CM(_, Empty)
      Unit{}
    case Pp.Outside{}:
      %h : LLogicLogic.pp.CM(_, Empty)
      Unit{}
    case Pp.Protected{}:
      %h : LLogicLogic.pp.CM(_, Empty)
      Unit{}
    case Pp.Secret{}:
      %h : LLogicLogic.pp.CM(_, Empty)
      Unit{}

def PathPolicy.path_looped_never_inside(pol, ls, segs, at, res):
  h => pli.demote(Pp.class_of(pol, at), Equal.trans(Pp.Cls, Pp.demote(Pp.class_of(pol, at), True{}), Pp.class(pol, ls, segs), Pp.Inside{}, Equal.sym(Pp.Cls, Pp.class(pol, ls, segs), Pp.demote(Pp.class_of(pol, at), True{}), LAC.pcc.cls_eq(pol, ls, segs, at, True{}, res)), h))
