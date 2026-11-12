# eukhe: the proof of LAW thread_log_one
#
# PROOF: a session's log of one message keeps it exactly when its writer
# is the session: Nat.is_eq(s, s) is True (thb.eq_refl), Nat.is_eq(o, s)
# False (the premise).

import Base
import ../../bend/thread.bend as Th
import ../../spec/memory/thread.bend as S
import ../../laws/thread.bend as Thread
import ./base.bend as LA

def tlo.mine(+s: Nat, +body: Nat) -> {Th.log(s, [Th.Msg{s, body}]) == [Th.Msg{s, body}] : List<&2, Th.Msg>}:
  %Equal.sym(Bool, Nat.is_eq(s, s), True{}, LA.thb.eq_refl(s)) : {Th.log.keep(_, Th.Msg{s, body}, Nil{}) == [Th.Msg{s, body}] : List<&2, Th.Msg>}
  {==}

def tlo.other(+s: Nat, +o: Nat, +body: Nat, other: {Nat.is_eq(o, s) == False{} : Bool}) -> {Th.log(s, [Th.Msg{o, body}]) == [] : List<&2, Th.Msg>}:
  %Equal.sym(Bool, Nat.is_eq(o, s), False{}, other) : {Th.log.keep(_, Th.Msg{o, body}, Nil{}) == [] : List<&2, Th.Msg>}
  {==}

def Thread.thread_log_one(s, o, body, other):
  (tlo.mine(s, body), tlo.other(s, o, body, other))
