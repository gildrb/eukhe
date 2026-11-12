# eukhe: the proof of LAW sandbox_read_skips
#
# PROOF: the first file's path is not p (the premise), so the read goes on
# with the rest, as a read of the rest does.

import Base
import ../../bend/sandbox.bend as Sb
import ../../laws/sandbox.bend as Sandbox
import ./base.bend as LA

def Sandbox.sandbox_read_skips(q, b, rest, p, other):
  %Equal.sym(Bool, Nat.is_eq(q, p), False{}, other) : {Sb.read.go(Sb.Doc{q, b} <> rest, p, _) == Sb.read(rest, p) : Maybe<&2, Nat>}
  {==}
