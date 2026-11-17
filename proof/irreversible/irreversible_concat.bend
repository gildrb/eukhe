# eukhe: the proof of LAW irreversible_concat
#
# PROOF: by induction on xs; a step is the associativity of `or`
# (LA.irb.or_assoc).

import Base
import ../../bend/irreversible.bend as Ir
import ../../laws/irreversible.bend as Irreversible
import ./base.bend as LA

def irc.go(xs: List<&2, Nat>, +ys: List<&2, Nat>) -> {Ir.irreversible(List.append(&2, Nat, xs, ys)) == Bool.or(Ir.irreversible(xs), Ir.irreversible(ys)) : Bool}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +t:
      %Equal.sym(Bool, Ir.irreversible(List.append(&2, Nat, t, ys)), Bool.or(Ir.irreversible(t), Ir.irreversible(ys)), irc.go(t, ys)) : {Bool.or(Bool.not(Ir.reversible.at(x)), _) == Bool.or(Bool.or(Bool.not(Ir.reversible.at(x)), Ir.irreversible(t)), Ir.irreversible(ys)) : Bool}
      LA.irb.or_assoc(Bool.not(Ir.reversible.at(x)), Ir.irreversible(t), Ir.irreversible(ys))

def Irreversible.irreversible_concat(xs, ys):
  irc.go(xs, ys)
