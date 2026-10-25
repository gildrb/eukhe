# eukhe: the proof of LAW tiny_elect_is_worker_model
#
# PROOF: the code's comparison of the texts is the spec's (LA.te.same),
# which the premise names as the comparison of the tags; on the same
# Bool a pong's choice gets what the model's need gets (te.need_pong).
# With no worker both start one.

import Base
import ../../bend/tiny.bend as Tn
import ../../laws/base.bend as LawsBase
import ../../laws/tiny/elect.bend as Tiny
import ./base.bend as LA

def te.need_pong(c: Bool) -> {Tiny.sp_need(Tn.elect.pong(c)) == [Tn.need.g(c)] : List<&2, Tn.Got>}:
  match c:
    case True{}:
      {==}
    case False{}:
      {==}

def te.pong_model(+a: String, +b: String, -t: Nat, -m: Nat, e: {Tn.same(a, b) == Nat.is_eq(t, m) : Bool}) -> {Tiny.sp_need(Tn.elect(Tn.Pong{a}, b)) == [Tn.need.g(Nat.is_eq(t, m))] : List<&2, Tn.Got>}:
  %e : {Tiny.sp_need(Tn.elect.pong(Tn.same(a, b))) == [Tn.need.g(_)] : List<&2, Tn.Got>}
  te.need_pong(Tn.same(a, b))

def Tiny.tiny_elect_is_worker_model(o, t, q, m, a, b, named):
  (te.pong_model(a, b, t, m, Equal.trans(Bool, Tn.same(a, b), LawsBase.text_same(a, b), Nat.is_eq(t, m), LA.te.same(a, b), named)), {==})
