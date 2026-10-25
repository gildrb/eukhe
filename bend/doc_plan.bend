# doc_plan: what a session commit writes and publishes for one staged
# document (crates/eukhe-durable/src/session/plans.rs `plan_loaded`,
# `publishes`). A loaded incarnation whose definition is newer than what
# storage holds writes a new base, even without operations; else only
# staged operations write a delta. Adoption publishes every plan that
# retires its document or has no loaded incarnation (a creation, a copy, a
# retirement), and a loaded incarnation's plan only when it writes
# content (a migration-only base included, so observers of the older shape
# receive the new value). Pure: no IO, no @unsafe. laws/doc_plan.bend
# states its laws.

import Base

# what a loaded incarnation writes
type Content is Data:
  # nothing
  Kept{}
  # a base of the whole value at the definition's version
  NewBase{}
  # a delta of the staged operations
  NewDelta{}

# the change a plan carries
type Change is Data:
  # none (a fork copy, a retirement)
  NoChange{}
  # the change of a created document
  Fresh{}
  # the change of a loaded incarnation
  OfLoaded{}

def content.pick(newer: Bool, ops: Bool) -> Content:
  match newer:
    case True{}:
      NewBase{}
    case False{}:
      match ops:
        case True{}:
          NewDelta{}
        case False{}:
          Kept{}

# the content a loaded incarnation stored at version `stored` writes at the
# definition's `version`, with staged operations (`ops`) or none
def content(stored: Nat, version: Nat, ops: Bool) -> Content:
  content.pick(Nat.is_lt(stored, version), ops)

# whether adoption publishes a plan that retires its document (`retire`),
# carries `change`, and writes content (`writes`)
def publishes(retire: Bool, change: Change, writes: Bool) -> Bool:
  match retire:
    case True{}:
      True{}
    case False{}:
      match change:
        case NoChange{}:
          True{}
        case Fresh{}:
          True{}
        case OfLoaded{}:
          writes
