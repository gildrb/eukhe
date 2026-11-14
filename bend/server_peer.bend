# server_peer: whom a client accepts as the listener of one of eukhe's
# endpoints (Rust: crates/eukhe-types/src/platform/transport.rs, the
# server rule every connect to an abstract endpoint applies; the call is
# crates/eukhe-bend/src/rules/server_peer.rs).
#
# On Linux eukhe's endpoints are abstract sockets: any process on the
# host, of any user, can bind a free name first. The listener of an
# endpoint records its pid in eukhe's run dir once it has bound the name
# (`<name>.pid` beside the name's path); a client reads the listener's uid
# and pid from the kernel (SO_PEERCRED) and the recorded pid, and talks to
# the listener only when it runs as the client's uid and is the recorded
# process. A record is a pid above 0: Rust sends 0 when no pid is
# recorded (a listener records its own pid, never 0).
#
# Uids and pids are numbers. Pure: no IO, no @unsafe.

import Base

# The verdict on a listener
type Served is Data:
  # it runs as the client's uid and is the recorded process
  Served{}
  # it runs as another uid
  OtherUid{}
  # no pid is recorded for the endpoint
  NoRecord{}
  # it is not the recorded process
  OtherPid{}

def served.pid(same: Bool) -> Served:
  match same:
    case True{}:
      Served{}
    case False{}:
      OtherPid{}

def served.rec(+pid: Nat, rec: Nat) -> Served:
  match rec:
    case 0n:
      NoRecord{}
    case 1n+q:
      served.pid(Nat.is_eq(pid, 1n+q))

def served.uid(same: Bool, +pid: Nat, rec: Nat) -> Served:
  match same:
    case True{}:
      served.rec(pid, rec)
    case False{}:
      OtherUid{}

# the verdict on a listener of uid p and pid pid, for a client of uid own,
# when rec is the pid recorded for the endpoint (0: none)
def served(+p: Nat, +own: Nat, +pid: Nat, rec: Nat) -> Served:
  served.uid(Nat.is_eq(p, own), pid, rec)
