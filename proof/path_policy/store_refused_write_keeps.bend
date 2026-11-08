# eukhe: the proof of LAW store_refused_write_keeps
#
# PROOF: one write is the store's step: the gate's verdict on the class of
# its path picks the write or the store as it was; refused, the store.

import Base
import ../../bend/path_policy.bend as Pp
import ../../laws/path_policy/gate.bend as PathPolicyGate

def PathPolicyGate.store_refused_write_keeps(pol, ls, auto, cs, segs, v, ans, refused):
  %Equal.sym(Bool, Pp.runs(Pp.class(pol, ls, segs), Pp.Wr{}, auto, ans), False{}, refused) : {Pp.put.pick(_, cs, Pp.Res.at(Pp.real(ls, segs)), v) == cs : List<&2, Pp.Cell>}
  {==}
