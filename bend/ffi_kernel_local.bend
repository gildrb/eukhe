import Base
import ./wire.bend as W
import ./kernel_local.bend as M

# ffi_kernel_local: the kernel setup's plan, the bootstrap lock sweep's
# verdict on each leftover and the lock attempt's verdict
# (bend/kernel_local.bend `plan`, `keeps`, `attempt` of `lock.of`) as an
# entry of the compiled Bend core. Request: a tag, then
#   0  the plan: the venv found (0 current, 1 skills stale, 2 stale), the
#      setup (0 a session, 1 `eukhe kernel install`)
#   1  the sweep: a count, then per file its kind (0 an attempt's
#      candidate, 1 a stale lock renamed aside, 2 another file) and
#      whether its owner lives (T|F)
#   2  the attempt: what it saw (0 linked, 1 vanished, 2 an owner, then
#      T|F alive, 3 no owner, then its age: 0 none | 1 and the ms)
# Reply: the plan as a count, then per action its tag (0 a fetch, then
# T|F hashed, 1 local only, 2 the check, 3 the start); the sweep as a
# count, then T (the file stays) or F per file; the attempt as its end's
# tag (0 got, 1 busy, 2 freed, 3 crash). Any other input: the error form.

# Decoding
# --------

def get_found.tag(t: Nat, s: String) -> W.Dec<M.Found>:
  match t:
    case 0n:
      W.Got{M.Current{}, s}
    case 1n:
      W.Got{M.Skills{}, s}
    case 2n:
      W.Got{M.Stale{}, s}
    case 3n+p:
      W.Bad{}

def get_found.go(r: W.Dec<Nat>) -> W.Dec<M.Found>:
  match r:
    case W.Got{t, s}:
      get_found.tag(t, s)
    case W.Bad{}:
      W.Bad{}

def get_setup.tag(t: Nat, s: String) -> W.Dec<M.Setup>:
  match t:
    case 0n:
      W.Got{M.Local{}, s}
    case 1n:
      W.Got{M.Install{}, s}
    case 2n+p:
      W.Bad{}

def get_setup.go(r: W.Dec<Nat>) -> W.Dec<M.Setup>:
  match r:
    case W.Got{t, s}:
      get_setup.tag(t, s)
    case W.Bad{}:
      W.Bad{}

def get_plan.setup(f: M.Found, r: W.Dec<M.Setup>) -> W.Dec<M.Ask>:
  match r:
    case W.Got{x, s}:
      W.Got{M.AskPlan{f, x}, s}
    case W.Bad{}:
      W.Bad{}

def get_plan.found(r: W.Dec<M.Found>) -> W.Dec<M.Ask>:
  match r:
    case W.Got{f, s}:
      get_plan.setup(f, get_setup.go(W.get_nat(s)))
    case W.Bad{}:
      W.Bad{}

def get_kind.tag(t: Nat, s: String) -> W.Dec<M.FileKind>:
  match t:
    case 0n:
      W.Got{M.Cand{}, s}
    case 1n:
      W.Got{M.Aside{}, s}
    case 2n:
      W.Got{M.Foreign{}, s}
    case 3n+p:
      W.Bad{}

def get_kind.go(r: W.Dec<Nat>) -> W.Dec<M.FileKind>:
  match r:
    case W.Got{t, s}:
      get_kind.tag(t, s)
    case W.Bad{}:
      W.Bad{}

def owner(alive: Bool) -> M.Owner:
  match alive:
    case True{}:
      M.Alive{}
    case False{}:
      M.Dead{}

def get_left.owner(k: M.FileKind, r: W.Dec<Bool>) -> W.Dec<M.Left>:
  match r:
    case W.Got{b, s}:
      W.Got{M.Left{k, owner(b)}, s}
    case W.Bad{}:
      W.Bad{}

def get_left.go(r: W.Dec<M.FileKind>) -> W.Dec<M.Left>:
  match r:
    case W.Got{k, s}:
      get_left.owner(k, W.get_bool(s))
    case W.Bad{}:
      W.Bad{}

def get_left(s: String) -> W.Dec<M.Left>:
  get_left.go(get_kind.go(W.get_nat(s)))

def get_lefts.cons(l: M.Left, r: W.Dec<List<&2, M.Left>>) -> W.Dec<List<&2, M.Left>>:
  match r:
    case W.Got{ls, s}:
      W.Got{l <> ls, s}
    case W.Bad{}:
      W.Bad{}

# n more files after the one cur answers
def get_lefts.go(n: Nat, cur: W.Dec<M.Left>) -> W.Dec<List<&2, M.Left>>:
  match n:
    case 0n:
      match cur:
        case W.Got{l, s}:
          W.Got{[l], s}
        case W.Bad{}:
          W.Bad{}
    case 1n+m:
      match cur:
        case W.Got{l, s}:
          get_lefts.cons(l, get_lefts.go(m, get_left(s)))
        case W.Bad{}:
          W.Bad{}

def get_sweep.files(r: W.Dec<List<&2, M.Left>>) -> W.Dec<M.Ask>:
  match r:
    case W.Got{ls, s}:
      W.Got{M.AskSweep{ls}, s}
    case W.Bad{}:
      W.Bad{}

def get_sweep(r: W.Dec<Nat>) -> W.Dec<M.Ask>:
  match r:
    case W.Got{n, s}:
      match n:
        case 0n:
          W.Got{M.AskSweep{Nil{}}, s}
        case 1n+m:
          get_sweep.files(get_lefts.go(m, get_left(s)))
    case W.Bad{}:
      W.Bad{}

def get_age.some(r: W.Dec<Nat>) -> W.Dec<M.Seen>:
  match r:
    case W.Got{a, s}:
      W.Got{M.NoOwner{Some{a}}, s}
    case W.Bad{}:
      W.Bad{}

def get_age.tag(t: Nat, s: String) -> W.Dec<M.Seen>:
  match t:
    case 0n:
      W.Got{M.NoOwner{None{}}, s}
    case 1n:
      get_age.some(W.get_nat(s))
    case 2n+p:
      W.Bad{}

def get_age.go(r: W.Dec<Nat>) -> W.Dec<M.Seen>:
  match r:
    case W.Got{t, s}:
      get_age.tag(t, s)
    case W.Bad{}:
      W.Bad{}

def get_owner(r: W.Dec<Bool>) -> W.Dec<M.Seen>:
  match r:
    case W.Got{b, s}:
      W.Got{M.Owner{b}, s}
    case W.Bad{}:
      W.Bad{}

def get_seen.tag(t: Nat, s: String) -> W.Dec<M.Seen>:
  match t:
    case 0n:
      W.Got{M.Linked{}, s}
    case 1n:
      W.Got{M.Vanished{}, s}
    case 2n:
      get_owner(W.get_bool(s))
    case 3n:
      get_age.go(W.get_nat(s))
    case 4n+p:
      W.Bad{}

def get_seen.go(r: W.Dec<Nat>) -> W.Dec<M.Seen>:
  match r:
    case W.Got{t, s}:
      get_seen.tag(t, s)
    case W.Bad{}:
      W.Bad{}

def get_lock(r: W.Dec<M.Seen>) -> W.Dec<M.Ask>:
  match r:
    case W.Got{x, s}:
      W.Got{M.AskLock{x}, s}
    case W.Bad{}:
      W.Bad{}

def get_ask.tag(t: Nat, s: String) -> W.Dec<M.Ask>:
  match t:
    case 0n:
      get_plan.found(get_found.go(W.get_nat(s)))
    case 1n:
      get_sweep(W.get_nat(s))
    case 2n:
      get_lock(get_seen.go(W.get_nat(s)))
    case 3n+p:
      W.Bad{}

def get_ask.go(r: W.Dec<Nat>) -> W.Dec<M.Ask>:
  match r:
    case W.Got{t, s}:
      get_ask.tag(t, s)
    case W.Bad{}:
      W.Bad{}

# the request at the start of s
def get_ask(s: String) -> W.Dec<M.Ask>:
  get_ask.go(W.get_nat(s))

# Encoding
# --------

def put_act(a: M.Act, rest: String) -> String:
  match a:
    case M.Fetch{h}:
      W.put_nat(0n, W.put_bool(h, rest))
    case M.Offline{}:
      W.put_nat(1n, rest)
    case M.Check{}:
      W.put_nat(2n, rest)
    case M.Run{}:
      W.put_nat(3n, rest)

def put_acts.items(xs: List<&2, M.Act>, rest: String) -> String:
  match xs:
    case Nil{}:
      rest
    case x <> t:
      put_act(x, put_acts.items(t, rest))

def put_acts(+xs: List<&2, M.Act>, rest: String) -> String:
  W.put_nat(List.length(&2, M.Act, xs), put_acts.items(xs, rest))

def put_bools.items(xs: List<&2, Bool>, rest: String) -> String:
  match xs:
    case Nil{}:
      rest
    case x <> t:
      W.put_bool(x, put_bools.items(t, rest))

def put_bools(+xs: List<&2, Bool>, rest: String) -> String:
  W.put_nat(List.length(&2, Bool, xs), put_bools.items(xs, rest))

def put_end(e: M.End, rest: String) -> String:
  match e:
    case M.Got{}:
      W.put_nat(0n, rest)
    case M.Busy{}:
      W.put_nat(1n, rest)
    case M.Freed{}:
      W.put_nat(2n, rest)
    case M.Crash{}:
      W.put_nat(3n, rest)

# The entry
# ---------

# the answer to a request
def answer(a: M.Ask) -> String:
  match a:
    case M.AskPlan{f, s}:
      put_acts(M.plan(f, s), "")
    case M.AskSweep{ls}:
      put_bools(M.keeps(ls), "")
    case M.AskLock{x}:
      put_end(M.attempt(M.lock.of(x)), "")

def fail() -> String:
  W.err("kernel_local: malformed request")

def run.end(whole: Bool, a: M.Ask) -> String:
  match whole:
    case True{}:
      answer(a)
    case False{}:
      fail()

def run(r: W.Dec<M.Ask>) -> String:
  match r:
    case W.Got{a, s}:
      run.end(W.end(s), a)
    case W.Bad{}:
      fail()

def ffi(input: String) -> String:
  run(get_ask(input))
