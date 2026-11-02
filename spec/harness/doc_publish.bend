# doc_publish (spec): what the laws of area doc_publish
# (laws/doc_publish.bend) speak of, over the types of bend/doc_publish.bend:
# the step of a publish after it re-read its target, just before the rename
# that puts an edit's new bytes in place. A spec: the shipped code never
# calls it.
#
# Versions of a file are Nats (equal Nats: equal bytes).
# S1: a publish renames its new bytes over the target only while the target
#     holds the bytes the change was made from (its base): it never
#     replaces bytes it did not read.
# S2: a target that holds other bytes: the change is rebased onto them
#     (they become its base), and the publish checks again; at most
#     bound() = 3 rebases in one publish.
# S3: a target that is gone, or that holds other bytes once the rebases
#     ran out, is refused: the target keeps its bytes.
#
# A re-read: what one re-read of the target met (a version, or no file) and
# what the rebase onto it answers (the rebased version, or a refusal). A
# run of a publish over its re-reads ends in a write over the bytes it met,
# or in a refusal.

import Base
import ../../bend/doc_publish.bend as P

# the rebases one publish may do (S2)
def bound() -> Nat:
  3n

def seen.of(eq: Bool) -> P.Seen:
  match eq:
    case True{}:
      P.Same{}
    case False{}:
      P.Moved{}

# what a re-read met when the base is b: no file, b, or other bytes
def seen(+b: Nat, d: Maybe<&2, Nat>) -> P.Seen:
  match d:
    case None{}:
      P.Gone{}
    case Some{v}:
      seen.of(Nat.is_eq(v, b))

def step.moved(left: Bool) -> P.Step:
  match left:
    case True{}:
      P.Rebase{}
    case False{}:
      P.Refuse{}

# the step after n rebases, having met s (S1-S3)
def step(n: Nat, s: P.Seen) -> P.Step:
  match s:
    case P.Same{}:
      P.Place{}
    case P.Gone{}:
      P.Refuse{}
    case P.Moved{}:
      step.moved(Nat.is_lt(n, bound()))

# one re-read: the target's version (None: no file), and the rebase onto
# it (None: refused)
type Reread is Data:
  Reread{disk: Maybe<&2, Nat>, rebased: Maybe<&2, Nat>}

# how a run ended: the change `with` renamed over the version `over` (None:
# no file) while its base was `read`; or refused
type Run is Data:
  Wrote{over: Maybe<&2, Nat>, read: Nat, with: Nat}
  Refused{}

# S1: a run replaced only bytes it read: the version it renamed over is
# its base
def safe(r: Run) -> Bool:
  match r:
    case Wrote{o, b, c}:
      match o:
        case None{}:
          False{}
        case Some{v}:
          Nat.is_eq(v, b)
    case Refused{}:
      True{}
