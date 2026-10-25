import Base
import ./wire.bend as W
import ./progress.bend as M

# ffi_progress: the goal loop's progress check (bend/progress.bend
# `judge`) as an entry of the compiled Bend core, with the count held
# below the bound t (Rust sends the wire's largest Nat). The request: t, the
# cap (directors.stallSteps),
# the prior check of the same run and goal (Maybe: its stalls and its
# work; bend/ffi_work.bend `ffi` decides which prior that is), the work
# now. The reply: the Goal, its tag (Go 0, Stop 1) and its count of
# stalls. Any other input answers the error form "progress: malformed
# request". laws/progress.bend (goal_entry, goal_entry_*) pins the entry.

def put_prior(p: Maybe<&2, M.Prior>, rest: String) -> String:
  match p:
    case None{}:
      W.put_nat(0n, rest)
    case Some{x}:
      match x:
        case M.Prior{s, w}:
          W.put_nat(1n, W.put_nat(s, W.put_nat(w, rest)))

def put_req(t: Nat, cap: Nat, p: Maybe<&2, M.Prior>, work: Nat) -> String:
  W.put_nat(t, W.put_nat(cap, put_prior(p, W.put_nat(work, ""))))

def put_goal(g: M.Goal, rest: String) -> String:
  match g:
    case M.Go{s}:
      W.put_nat(0n, W.put_nat(s, rest))
    case M.Stop{s}:
      W.put_nat(1n, W.put_nat(s, rest))

def get_prior.w(+s: Nat, r: W.Dec<Nat>) -> W.Dec<Maybe<&2, M.Prior>>:
  match r:
    case W.Got{w, rest}:
      W.Got{Some{M.Prior{s, w}}, rest}
    case W.Bad{}:
      W.Bad{}

def get_prior.s(r: W.Dec<Nat>) -> W.Dec<Maybe<&2, M.Prior>>:
  match r:
    case W.Got{+s, rest}:
      get_prior.w(s, W.get_nat(rest))
    case W.Bad{}:
      W.Bad{}

def get_prior.tag(t: Nat, s: String) -> W.Dec<Maybe<&2, M.Prior>>:
  match t:
    case 0n:
      W.Got{None{}, s}
    case 1n+p:
      match p:
        case 0n:
          get_prior.s(W.get_nat(s))
        case 1n+q:
          W.Bad{}

def get_prior.go(r: W.Dec<Nat>) -> W.Dec<Maybe<&2, M.Prior>>:
  match r:
    case W.Got{t, s}:
      get_prior.tag(t, s)
    case W.Bad{}:
      W.Bad{}

def get_prior(s: String) -> W.Dec<Maybe<&2, M.Prior>>:
  get_prior.go(W.get_nat(s))

def run.end(left: Bool, +t: Nat, +cap: Nat, p: Maybe<&2, M.Prior>, +work: Nat) -> String:
  match left:
    case True{}:
      put_goal(M.judge(t, cap, p, work), "")
    case False{}:
      W.err("progress: malformed request")

def run.work(+t: Nat, +cap: Nat, p: Maybe<&2, M.Prior>, r: W.Dec<Nat>) -> String:
  match r:
    case W.Got{+work, s}:
      run.end(W.end(s), t, cap, p, work)
    case W.Bad{}:
      W.err("progress: malformed request")

def run.prior(+t: Nat, +cap: Nat, r: W.Dec<Maybe<&2, M.Prior>>) -> String:
  match r:
    case W.Got{p, s}:
      run.work(t, cap, p, W.get_nat(s))
    case W.Bad{}:
      W.err("progress: malformed request")

def run.cap(+t: Nat, r: W.Dec<Nat>) -> String:
  match r:
    case W.Got{+cap, s}:
      run.prior(t, cap, get_prior(s))
    case W.Bad{}:
      W.err("progress: malformed request")

def run.t(r: W.Dec<Nat>) -> String:
  match r:
    case W.Got{+t, s}:
      run.cap(t, W.get_nat(s))
    case W.Bad{}:
      W.err("progress: malformed request")

# the entry
def ffi(input: String) -> String:
  run.t(W.get_nat(input))
