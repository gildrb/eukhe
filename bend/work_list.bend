# work_list: how a child hands back its work list (Rust: eukhe-core
# durable/children/task.rs, the watch of a child given items). The parent
# names the items (`items` of an `rlm.split` half, an `rlm.spawn` help leaf
# or a worker's task, `worker_assign`); the child
# accounts for each, done or left with a reason (`rlm.items`). The hand-back
# is Finished only when every item is accounted done; otherwise it is
# Stopped, naming the position of every item not done, in the order the
# parent gave them. An item the child never accounted for is not done.
# Pure: no IO, no @unsafe.

import Base

# the hand-back of a work list
type Outcome is Data:
  Finished{}
  Stopped{left: List<&2, Nat>}

# the positions, from i, of the items not done
def open(done: List<&2, Bool>, +i: Nat) -> List<&2, Nat>:
  match done:
    case Nil{}:
      []
    case d <> t:
      match d:
        case True{}:
          open(t, 1n+i)
        case False{}:
          i <> open(t, 1n+i)

def of_open(left: List<&2, Nat>) -> Outcome:
  match left:
    case Nil{}:
      Finished{}
    case x <> t:
      Stopped{x <> t}

# the hand-back of the items, `done` one Bool per item in the parent's
# order: Finished when all are done, else Stopped with the items left
def outcome(done: List<&2, Bool>) -> Outcome:
  of_open(open(done, 0n))
