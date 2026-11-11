# eukhe: the proof of LAW sandbox_read_first
#
# PROOF: the first file's path is p (LA.px.eq_refl), so the read stops at it.

import Base
import ../../bend/sandbox.bend as Sb
import ../../laws/sandbox.bend as Sandbox
import ./base.bend as LA

def Sandbox.sandbox_read_first(p, b, rest):
  %LA.px.eq_refl(p) : {Sb.read.go(Sb.Doc{p, b} <> rest, p, _) == Some{b} : Maybe<&2, Nat>}
  {==}
