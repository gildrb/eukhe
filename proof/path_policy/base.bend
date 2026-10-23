# eukhe: lemmas the proofs of area path_policy share

import Base
import ../../bend/path_policy.bend as Pp
import ../base/logic/logic.bend as LLogicLogic

def pp.absurdF(-A: Type, e: {False{} == True{} : Bool}) -> A:
  %e : LLogicLogic.path_policy.pp.BD(_, A, Unit)
  Unit{}

def pp.and_r(a: Bool, +b: Bool, h: {Bool.and(a, b) == True{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case True{}:
      h
    case False{}:
      pp.absurdF({b == True{} : Bool}, h)

def pp.or_tr(a: Bool, +b: Bool, hb: {b == True{} : Bool}) -> {Bool.or(a, b) == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      hb

# demote gives Inside only for an Inside that did not loop
def pp.demote_inside(c: Pp.Cls, looped: Bool, h: {Pp.demote(c, looped) == Pp.Inside{} : Pp.Cls}) -> {Bool.and(Bool.not(looped), Pp.Cls.inside(c)) == True{} : Bool}:
  match c:
    case Pp.Inside{}:
      match looped:
        case True{}:
          %h : LLogicLogic.pp.CM(_, {Bool.and(Bool.not(True{}), True{}) == True{} : Bool})
          Unit{}
        case False{}:
          {==}
    case Pp.Outside{}:
      %h : LLogicLogic.pp.CM(_, {Bool.and(Bool.not(looped), False{}) == True{} : Bool})
      Unit{}
    case Pp.Protected{}:
      %h : LLogicLogic.pp.CM(_, {Bool.and(Bool.not(looped), False{}) == True{} : Bool})
      Unit{}
    case Pp.Secret{}:
      %h : LLogicLogic.pp.CM(_, {Bool.and(Bool.not(looped), False{}) == True{} : Bool})
      Unit{}

# 3. The gate
# -----------

# a yes that is not a yes
def pp.yes_clash(-A: Type, ans: Pp.Ans, ran: {Pp.Ans.yes(ans) == True{} : Bool}, no: {Pp.Ans.yes(ans) == False{} : Bool}) -> A:
  LLogicLogic.pp.absurd(A, Equal.trans(Bool, True{}, Pp.Ans.yes(ans), False{}, Equal.sym(Bool, Pp.Ans.yes(ans), True{}, ran), no))

def pp.gate_write_auto_only_inside(c: Pp.Cls, +auto: List<&2, Nat>, +ans: Pp.Ans, ran: {Pp.runs(c, Pp.Wr{}, auto, ans) == True{} : Bool}, no: {Pp.Ans.yes(ans) == False{} : Bool}) -> {c == Pp.Inside{} : Pp.Cls}:
  match c:
    case Pp.Inside{}:
      {==}
    case Pp.Outside{}:
      pp.yes_clash({Pp.Outside{} == Pp.Inside{} : Pp.Cls}, ans, ran, no)
    case Pp.Protected{}:
      pp.yes_clash({Pp.Protected{} == Pp.Inside{} : Pp.Cls}, ans, ran, no)
    case Pp.Secret{}:
      pp.yes_clash({Pp.Secret{} == Pp.Inside{} : Pp.Cls}, ans, ran, no)
