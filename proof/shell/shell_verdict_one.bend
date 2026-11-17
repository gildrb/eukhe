# eukhe: the proof of LAW shell_verdict_one
#
# PROOF: by cases on the own-write flag; both sides compute.

import Base
import ../../bend/tools.bend as Tl
import ../../laws/shell.bend as Shell

def svo.go(o: List<&2, Nat>, s: Bool, m: Bool) -> {Shell.refused(Tl.verdict([Tl.Piece{o, s, m}])) == m : Bool}:
  match m:
    case True{}:
      {==}
    case False{}:
      {==}

def Shell.shell_verdict_one(o, s, m):
  svo.go(o, s, m)
