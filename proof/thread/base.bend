# eukhe: lemmas shared by the proofs of area thread: the logic of Bool.and
# and of a refuted premise, Nat.is_eq's reflexivity, and the model's log
# as the spec's chat

import Base
import ../../bend/thread.bend as Th
import ../../spec/memory/thread.bend as S

def thb.IfF(b: Bool, G: Type) -> Type:
  match b:
    case True{}:
      G
    case False{}:
      Unit

def thb.IfT(b: Bool, G: Type) -> Type:
  match b:
    case True{}:
      Unit
    case False{}:
      G

# a premise False == True proves anything
def thb.absurd_ft(-G: Type, e: {False{} == True{} : Bool}) -> G:
  %e : thb.IfF(_, G)
  Unit{}

# a premise True == False proves anything
def thb.absurd_tf(-G: Type, e: {True{} == False{} : Bool}) -> G:
  %e : thb.IfT(_, G)
  Unit{}

# the left side of a true and is true
def thb.and_l(a: Bool, -b: Bool, h: {Bool.and(a, b) == True{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      thb.absurd_ft({False{} == True{} : Bool}, h)

# the right side of a true and is true
def thb.and_r(a: Bool, -b: Bool, h: {Bool.and(a, b) == True{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case True{}:
      h
    case False{}:
      thb.absurd_ft({b == True{} : Bool}, h)

# two true sides make a true and
def thb.and_i(a: Bool, -b: Bool, ea: {a == True{} : Bool}, eb: {b == True{} : Bool}) -> {Bool.and(a, b) == True{} : Bool}:
  match a:
    case True{}:
      eb
    case False{}:
      thb.absurd_ft({Bool.and(False{}, b) == True{} : Bool}, ea)

# every Nat is equal to itself
def thb.eq_refl(n: Nat) -> {Nat.is_eq(n, n) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      thb.eq_refl(p)

# Chats
# -----

def thb.log_keep(b: Bool, m: Th.Msg, rest: List<&2, Th.Msg>) -> {Th.log.keep(b, m, rest) == List.append(&2, Th.Msg, S.only(b, m), rest) : List<&2, Th.Msg>}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

# the model's log of a session is the spec's chat (S1), by induction on the
# stream: a message the session wrote is kept in front of the rest's
# chat, any other is skipped (thb.log_keep)
def thb.log_chat(+s: Nat, evs: List<&2, Th.Msg>) -> {Th.log(s, evs) == S.chat(s, evs) : List<&2, Th.Msg>}:
  match evs:
    case Nil{}:
      {==}
    case m <> +t:
      match m:
        case Th.Msg{+who, +body}:
          %thb.log_chat(s, t) : {Th.log.keep(Nat.is_eq(who, s), Th.Msg{who, body}, Th.log(s, t)) == List.append(&2, Th.Msg, S.only(Nat.is_eq(who, s), Th.Msg{who, body}), _) : List<&2, Th.Msg>}
          thb.log_keep(Nat.is_eq(who, s), Th.Msg{who, body}, Th.log(s, t))
