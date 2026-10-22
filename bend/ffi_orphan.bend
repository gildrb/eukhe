# ffi_orphan: the compiled Bend core's entry for the orphan exit
# (bend/orphan.bend). Rust `supervisor_lost::exit_due` and
# `work_gate::orphan_exit` call it through `eukhe_bend::call`.
#
# Request (crates/eukhe-bend/WIRE.md): a record
#   window: Maybe<Nat>   the lost-exit window in ms; None past the wire's
#                        Nat range (it never expires)
#   absent: Nat          the ms the supervisor has been unreachable
#   work:   tag          0 Idle, 1 Ongoing
# Reply: a record
#   due:  Bool           whether the worker exits now (M.exit_due.at)
#   exit: tag            0 Shut, 1 Handover (M.orphan_exit)
# A malformed request or input left over answers the wire error form.

import Base
import ./wire.bend as W
import ./orphan.bend as M

type Req is Data:
  Req{window: Maybe<&2, Nat>, absent: Nat, work: M.Work}

type Reply is Data:
  Reply{due: Bool, exit: M.Exit}

# Work: a tag

def put_work(w: M.Work, rest: String) -> String:
  match w:
    case M.Idle{}:
      W.put_nat(0n, rest)
    case M.Ongoing{}:
      W.put_nat(1n, rest)

def get_work.tag(t: Nat, rest: String) -> W.Dec<M.Work>:
  match t:
    case 0n:
      W.Got{M.Idle{}, rest}
    case 1n+p:
      match p:
        case 0n:
          W.Got{M.Ongoing{}, rest}
        case 1n+q:
          W.Bad{}

def get_work.of(r: W.Dec<Nat>) -> W.Dec<M.Work>:
  match r:
    case W.Got{t, rest}:
      get_work.tag(t, rest)
    case W.Bad{}:
      W.Bad{}

def get_work(s: String) -> W.Dec<M.Work>:
  get_work.of(W.get_nat(s))

# Exit: a tag

def put_exit(e: M.Exit, rest: String) -> String:
  match e:
    case M.Shut{}:
      W.put_nat(0n, rest)
    case M.Handover{}:
      W.put_nat(1n, rest)

def get_exit.tag(t: Nat, rest: String) -> W.Dec<M.Exit>:
  match t:
    case 0n:
      W.Got{M.Shut{}, rest}
    case 1n+p:
      match p:
        case 0n:
          W.Got{M.Handover{}, rest}
        case 1n+q:
          W.Bad{}

def get_exit.of(r: W.Dec<Nat>) -> W.Dec<M.Exit>:
  match r:
    case W.Got{t, rest}:
      get_exit.tag(t, rest)
    case W.Bad{}:
      W.Bad{}

def get_exit(s: String) -> W.Dec<M.Exit>:
  get_exit.of(W.get_nat(s))

# the window: a Maybe<Nat>

def put_window(m: Maybe<&2, Nat>, rest: String) -> String:
  match m:
    case None{}:
      W.put_nat(0n, rest)
    case Some{n}:
      W.put_nat(1n, W.put_nat(n, rest))

def get_window.some(r: W.Dec<Nat>) -> W.Dec<Maybe<&2, Nat>>:
  match r:
    case W.Got{n, rest}:
      W.Got{Some{n}, rest}
    case W.Bad{}:
      W.Bad{}

def get_window.tag(t: Nat, rest: String) -> W.Dec<Maybe<&2, Nat>>:
  match t:
    case 0n:
      W.Got{None{}, rest}
    case 1n+p:
      match p:
        case 0n:
          get_window.some(W.get_nat(rest))
        case 1n+q:
          W.Bad{}

def get_window.of(r: W.Dec<Nat>) -> W.Dec<Maybe<&2, Nat>>:
  match r:
    case W.Got{t, rest}:
      get_window.tag(t, rest)
    case W.Bad{}:
      W.Bad{}

def get_window(s: String) -> W.Dec<Maybe<&2, Nat>>:
  get_window.of(W.get_nat(s))

# the request

def put_req(q: Req, rest: String) -> String:
  match q:
    case Req{w, a, k}:
      put_window(w, W.put_nat(a, put_work(k, rest)))

def get_req.work(w: Maybe<&2, Nat>, a: Nat, r: W.Dec<M.Work>) -> W.Dec<Req>:
  match r:
    case W.Got{k, rest}:
      W.Got{Req{w, a, k}, rest}
    case W.Bad{}:
      W.Bad{}

def get_req.absent(w: Maybe<&2, Nat>, r: W.Dec<Nat>) -> W.Dec<Req>:
  match r:
    case W.Got{a, rest}:
      get_req.work(w, a, get_work(rest))
    case W.Bad{}:
      W.Bad{}

def get_req.window(r: W.Dec<Maybe<&2, Nat>>) -> W.Dec<Req>:
  match r:
    case W.Got{w, rest}:
      get_req.absent(w, W.get_nat(rest))
    case W.Bad{}:
      W.Bad{}

def get_req(s: String) -> W.Dec<Req>:
  get_req.window(get_window(s))

# the reply

def put_reply(p: Reply, rest: String) -> String:
  match p:
    case Reply{d, e}:
      W.put_bool(d, put_exit(e, rest))

def get_reply.exit(d: Bool, r: W.Dec<M.Exit>) -> W.Dec<Reply>:
  match r:
    case W.Got{e, rest}:
      W.Got{Reply{d, e}, rest}
    case W.Bad{}:
      W.Bad{}

def get_reply.due(r: W.Dec<Bool>) -> W.Dec<Reply>:
  match r:
    case W.Got{d, rest}:
      get_reply.exit(d, get_exit(rest))
    case W.Bad{}:
      W.Bad{}

def get_reply(s: String) -> W.Dec<Reply>:
  get_reply.due(W.get_bool(s))

# the decision on a request
def decide(q: Req) -> Reply:
  match q:
    case Req{w, a, +k}:
      Reply{M.exit_due.at(w, a, k), M.orphan_exit(k)}

def ffi.fin(done: Bool, q: Req) -> String:
  match done:
    case True{}:
      put_reply(decide(q), "")
    case False{}:
      W.err("orphan: input left over")

def ffi.go(r: W.Dec<Req>) -> String:
  match r:
    case W.Got{q, rest}:
      ffi.fin(W.end(rest), q)
    case W.Bad{}:
      W.err("orphan: malformed request")

def ffi(input: String) -> String:
  ffi.go(get_req(input))
