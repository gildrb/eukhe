# eukhe: the proof of LAW move_exact
#
# PROOF: has is the spec's (move_tests_exact); for either answer of it the
# move is the spec's: refused with the files, or done with rename, which
# is the spec's rename by induction on the files.

import Base
import ../../bend/doc_commit.bend as Cm
import ../../laws/doc_commit/exact.bend as DocCommitExact
import ./move_tests_exact.bend as PMoveTestsExact

def dx.rename.put(+t: Nat, +m: Nat, g: Nat, -r: List<&2, Cm.Entry>, b: Bool) -> {Cm.rename.put(t, m, g, r, b) == Cm.Entry{DocCommitExact.sp_name(b, t, m), g} <> r : List<&2, Cm.Entry>}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

# rename is the spec's rename
def dx.rename(+s: Nat, +t: Nat, es: List<&2, Cm.Entry>) -> {Cm.rename(s, t, es) == DocCommitExact.sp_rename(s, t, es) : List<&2, Cm.Entry>}:
  match es:
    case Nil{}:
      {==}
    case e <> rest:
      match e:
        case Cm.Entry{+m, g}:
          %dx.rename(s, t, rest) : {Cm.rename.put(t, m, g, Cm.rename(s, t, rest), Nat.is_eq(m, s)) == Cm.Entry{DocCommitExact.sp_name(Nat.is_eq(m, s), t, m), g} <> _ : List<&2, Cm.Entry>}
          dx.rename.put(t, m, g, Cm.rename(s, t, rest), Nat.is_eq(m, s))

def dx.move.go(+s: Nat, +t: Nat, b: Bool, +es: List<&2, Cm.Entry>) -> {Cm.move.go(s, t, b, es) == DocCommitExact.sp_move.of(b, s, t, es) : Cm.Mv}:
  match b:
    case True{}:
      {==}
    case False{}:
      %dx.rename(s, t, es) : {Cm.Mv{True{}, Cm.rename(s, t, es)} == Cm.Mv{True{}, _} : Cm.Mv}
      {==}

def DocCommitExact.move_exact(s, t, es):
  %PMoveTestsExact.dx.has(t, es) : {Cm.move.go(s, t, Cm.has(t, es), es) == DocCommitExact.sp_move.of(_, s, t, es) : Cm.Mv}
  dx.move.go(s, t, Cm.has(t, es), es)
