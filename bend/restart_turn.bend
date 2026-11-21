# restart_turn: what follows when the supervisor ended a session's run (its
# worker stopped answering and was killed, or crashed past the restart
# budget). The worker that reopens the session stops the run that hung or
# crashed and asks Reopened: the turn continues by itself with a harness
# continuation, at most cap() times a turn, then the run ends with its
# report (Rust: crates/eukhe-daemon worker/create.rs). The supervisor that
# gives a crash-looping worker up asks GaveUp: it relaunches the worker,
# whose reopen decides the turn, unless its last relaunch never opened the
# session or ended the turn at the cap (Rust: supervisor/supervision.rs).
# Pure: no IO, no @unsafe.

import Base

# the automatic continues of one turn after restarts
def cap() -> Nat:
  3n

# what the supervisor knows of a session's last relaunch: Clear (no
# relaunch of it is unsettled, none ended its turn at the cap), Unsettled
# (its last relaunch never opened the session), Ended (its last reopen
# ended the turn at the cap)
type Prior is Data:
  Clear{}
  Unsettled{}
  Ended{}

# the facts of one decision: a worker reopened the session, `made`
# automatic continues made this turn; or the restart budget gave the
# session's worker up
type Fact is Data:
  Reopened{made: Nat}
  GaveUp{prior: Prior}

# what follows: submit the continuation, the n-th automatic continue of
# the turn; end the run with its report, n continues made; relaunch the
# worker; give the worker up
type Next is Data:
  Continue{n: Nat}
  End{n: Nat}
  Relaunch{}
  Retire{}

def reopened(below: Bool, made: Nat) -> Next:
  match below:
    case True{}:
      Continue{1n+made}
    case False{}:
      End{made}

def gave_up(p: Prior) -> Next:
  match p:
    case Clear{}:
      Relaunch{}
    case Unsettled{}:
      Retire{}
    case Ended{}:
      Retire{}

# what follows the facts f
def next(f: Fact) -> Next:
  match f:
    case Reopened{+made}:
      reopened(Nat.is_lt(made, cap()), made)
    case GaveUp{p}:
      gave_up(p)
