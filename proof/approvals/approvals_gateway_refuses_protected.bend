# eukhe: the proof of LAW approvals_gateway_refuses_protected
# PROOF: the gateway rule reads whether 5 is among the effects; it is,
# wherever it sits (pg.mid, by induction on pre).

import Base
import ../../bend/approvals.bend as Am
import ../../bend/tools.bend as Tl
import ../../laws/approvals/desk.bend as ApprovalsDesk
import ./base/desk.bend as LAD

# 5 is among pre, then 5, then post
def pg.mid(pre: List<&2, Nat>, +post: List<&2, Nat>) -> {Tl.elem(List.append(&2, Nat, pre, 5n <> post), 5n) == True{} : Bool}:
  match pre:
    case Nil{}:
      {==}
    case +y <> rest:
      %Equal.sym(Bool, Tl.elem(List.append(&2, Nat, rest, 5n <> post), 5n), True{}, pg.mid(rest, post)) : {Bool.or(Nat.is_eq(y, 5n), _) == True{} : Bool}
      LAD.ad.or_true(Nat.is_eq(y, 5n))

def ApprovalsDesk.approvals_gateway_refuses_protected(pre, post, a):
  %Equal.sym(Bool, Tl.elem(List.append(&2, Nat, pre, 5n <> post), 5n), True{}, pg.mid(pre, post)) : {Am.guard(_) == Am.GatewayRefused{} : Am.Fate}
  {==}
