# eukhe: the proof of LAW move_tests_exact
#
# PROOF: induction on the files: has and get test each file's name as the
# spec does; get's pick is the spec's pick for either answer of the test.

import Base
import ../../bend/doc_commit.bend as Cm
import ../../laws/doc_commit/exact.bend as DocCommitExact

# has is the spec's membership
def dx.has(+n: Nat, es: List<&2, Cm.Entry>) -> {Cm.has(n, es) == DocCommitExact.sp_has(n, es) : Bool}:
  match es:
    case Nil{}:
      {==}
    case e <> rest:
      match e:
        case Cm.Entry{m, g}:
          %dx.has(n, rest) : {Bool.or(Nat.is_eq(m, n), Cm.has(n, rest)) == Bool.or(Nat.is_eq(m, n), _) : Bool}
          {==}

def dx.get.put(b: Bool, g: Nat, -r: Maybe<&2, Nat>) -> {Cm.get.put(b, g, r) == DocCommitExact.sp_get.of(b, g, r) : Maybe<&2, Nat>}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

# get is the spec's first match
def dx.get(+n: Nat, es: List<&2, Cm.Entry>) -> {Cm.get(n, es) == DocCommitExact.sp_get(n, es) : Maybe<&2, Nat>}:
  match es:
    case Nil{}:
      {==}
    case e <> rest:
      match e:
        case Cm.Entry{+m, g}:
          %dx.get(n, rest) : {Cm.get.put(Nat.is_eq(m, n), g, Cm.get(n, rest)) == DocCommitExact.sp_get.of(Nat.is_eq(m, n), g, _) : Maybe<&2, Nat>}
          dx.get.put(Nat.is_eq(m, n), g, Cm.get(n, rest))

def DocCommitExact.move_tests_exact(n, es):
  (dx.has(n, es), dx.get(n, es))
