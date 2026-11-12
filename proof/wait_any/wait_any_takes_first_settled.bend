# eukhe: the proof of LAW wait_any_takes_first_settled
#
# PROOF: the code's first settled index past pre, none of which counts
# as settled, is |pre| (wap.first, by induction on pre); a found index
# ends the poll whatever the cancel and the cap say.

import Base
import ../../bend/wait_any.bend as Wa
import ../../spec/durable/wait_any.bend as WaSpec
import ../../laws/wait_any.bend as WaitAny
import ./base/poll.bend as LWP

def WaitAny.wait_any_takes_first_settled(named, cancel, late, pre, t, post, none, here):
  %Equal.sym(Maybe<&2, Nat>, Wa.first(List.append(&2, Wa.Tgt, pre, Con{t, post}), named, 0n), Some{Nat.add(0n, List.length(&2, Wa.Tgt, pre))}, LWP.wap.first(pre, named, t, post, 0n, none, here)) : {Wa.poll.found(_, Wa.live(List.append(&2, Wa.Tgt, pre, Con{t, post})), cancel, late) == Wa.Takes{List.length(&2, Wa.Tgt, pre)} : Wa.Pick}
  {==}
