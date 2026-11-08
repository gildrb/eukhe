# ffi_job_notice: the entry of the compiled Bend core for the notice of
# one settled job (bend/job_notice.bend; Rust: eukhe-bend
# rules/job_notice.rs, asked by eukhe-daemon job_notices.rs
# JobNotices::deliver and eukhe-core durable/rlm/jobs.rs cancel). Grammar:
# crates/eukhe-bend/WIRE.md.
#
#   request  who stopped the job, a tag (Nat): 0 nobody, 1 the agent,
#            2 the user, 3 an interrupt; then T|F: the agent's own call
#            took the result
#   reply    the notice, a tag (Nat): 0 dropped, 1 a wake
#
# Malformed input (a tag past 3, no Bool, input left after the request)
# answers `E job_notice: malformed request`, never a default. Pure: no IO,
# no @unsafe.

import Base
import ./wire.bend as W
import ./job_notice.bend as N

# A request of the entry
type Req is Data:
  Req{by: N.Stopper, taken: Bool}

def get_req.taken(by: N.Stopper, r: W.Dec<Bool>) -> W.Dec<Req>:
  match r:
    case W.Got{t, s}:
      W.Got{Req{by, t}, s}
    case W.Bad{}:
      W.Bad{}

# the stopper of tag n, then the Bool after it
def get_req.by(n: Nat, s: String) -> W.Dec<Req>:
  match n:
    case 0n:
      get_req.taken(N.NoStop{}, W.get_bool(s))
    case 1n+a:
      match a:
        case 0n:
          get_req.taken(N.AgentStop{}, W.get_bool(s))
        case 1n+b:
          match b:
            case 0n:
              get_req.taken(N.UserStop{}, W.get_bool(s))
            case 1n+c:
              match c:
                case 0n:
                  get_req.taken(N.InterruptStop{}, W.get_bool(s))
                case 1n+d:
                  W.Bad{}

def get_req.tag(r: W.Dec<Nat>) -> W.Dec<Req>:
  match r:
    case W.Got{n, s}:
      get_req.by(n, s)
    case W.Bad{}:
      W.Bad{}

# the request at the start of s
def get_req(s: String) -> W.Dec<Req>:
  get_req.tag(W.get_nat(s))

# The entry
# ---------

# the reply's tag of a notice
def put_notice(n: N.Notice) -> String:
  match n:
    case N.Drops{}:
      W.put_nat(0n, "")
    case N.Wakes{}:
      W.put_nat(1n, "")

# the reply of a request: the model's notice, encoded
def answer(q: Req) -> String:
  match q:
    case Req{by, t}:
      put_notice(N.notice(by, t))

def ffi.done(q: Req, end: Bool) -> String:
  match end:
    case True{}:
      answer(q)
    case False{}:
      W.err("job_notice: malformed request")

def ffi.got(r: W.Dec<Req>) -> String:
  match r:
    case W.Got{q, +s}:
      ffi.done(q, W.end(s))
    case W.Bad{}:
      W.err("job_notice: malformed request")

# the entry: decode the request, answer the model's notice
def ffi(input: String) -> String:
  ffi.got(get_req(input))
