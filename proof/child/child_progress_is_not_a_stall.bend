# eukhe: the proof of LAW child_progress_is_not_a_stall

import Base
import ../../bend/child.bend as Ch
import ../../laws/child.bend as Child
import ../base/child.bend as LChild

# a token x other than the held y moved
def pc.moved_other(+y: Nat, +x: Nat, news: {Nat.is_eq(y, x) == False{} : Bool}) -> {Ch.moved(Some{y}, Some{x}) == True{} : Bool}:
  %Equal.sym(Bool, Nat.is_eq(y, x), False{}, news) : {Bool.not(_) == True{} : Bool}
  {==}

def Child.child_progress_is_not_a_stall(s, f, y, l, n, e, x, news):
  LChild.pc.progress(s, f, Some{y}, l, n, e, x, pc.moved_other(y, x, news))
