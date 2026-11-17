# eukhe: the proof of LAW shell_verdict_effects
#
# PROOF: by induction on the parts: a part's effects are those of the
# same part without its own-write fact, by definition.

import Base
import ../../bend/tools.bend as Tl
import ../../laws/shell.bend as Shell

def sve.go(ps: List<&2, Tl.Piece>) -> {Tl.pieces.effs(ps) == Tl.join(Tl.parts.effs(Shell.pieces_parts(ps))) : List<&2, Nat>}:
  match ps:
    case Nil{}:
      {==}
    case p <> +t:
      match p:
        case Tl.Piece{+o, +s, m}:
          %Equal.sym(List<&2, Nat>, Tl.pieces.effs(t), Tl.join(Tl.parts.effs(Shell.pieces_parts(t))), sve.go(t)) : {List.append(&2, Nat, Tl.part.effs(Tl.Part{o, s}), _) == Tl.join(Tl.parts.effs(Shell.pieces_parts(Tl.Piece{o, s, m} <> t))) : List<&2, Nat>}
          {==}

def Shell.shell_verdict_effects(ps):
  sve.go(ps)
