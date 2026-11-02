# doc_publish: what a publish of one edited file does when it re-checks
# the target just before the rename (Rust: eukhe-docs write.rs publish,
# asked by LockedWriter for every file of an edit and by write_file for
# the write tool). The edit was staged on bytes it read (its base); the
# new bytes are written and synced to a temporary file; then the target is
# read again. Another program (no path lock: a formatter, a stamper) may
# have changed it since the base was read. A publish never replaces bytes
# it did not read: it renames only over its base; over other bytes it
# rebases the edit onto them (the line rebase of bend/rebase.bend) and
# checks again, at most `bound` times; a target gone, or changed once the
# rebases ran out, refuses the file and writes nothing of it. Pure: no IO,
# no @unsafe.

import Base

# what the re-check of the target met
type Seen is Data:
  Same{}   # the target holds the base
  Gone{}   # no file is there
  Moved{}  # other bytes are there

# what the publish does next
type Step is Data:
  Place{}   # rename the new bytes over the target
  Rebase{}  # rebase the edit onto the target's bytes, write, re-check
  Refuse{}  # remove the temporary file; the target keeps its bytes

# the rebases one publish may do
def bound() -> Nat:
  3n

def step.moved(lt: Bool) -> Step:
  match lt:
    case True{}:
      Rebase{}
    case False{}:
      Refuse{}

# the next step of a publish that rebased n times and then met s
def step(n: Nat, s: Seen) -> Step:
  match s:
    case Same{}:
      Place{}
    case Gone{}:
      Refuse{}
    case Moved{}:
      step.moved(Nat.is_lt(n, bound()))
