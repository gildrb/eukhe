import Base
import ./wire.bend as W
import ./job.bend as M

# ffi_job_rewind: the kills of a rewind of the job table (bend/job.bend
# `kills`) as an entry of the compiled Bend core. Request: the commit of
# the target entry (a Maybe Nat: 0, none | 1, then the commit), then the
# jobs of the table as a count, then per job T|F (it runs) and the commit
# of the last entry the table saw when it started (a Maybe Nat). Reply: a
# count, then per job, in order, T (send the kill) or F. Any other input:
# the error form, `job_rewind: malformed request`.

# Decoding
# --------

def get_commit.some(r: W.Dec<Nat>) -> W.Dec<Maybe<&2, Nat>>:
  match r:
    case W.Got{x, s}:
      W.Got{Some{x}, s}
    case W.Bad{}:
      W.Bad{}

def get_commit.tag(t: Nat, s: String) -> W.Dec<Maybe<&2, Nat>>:
  match t:
    case 0n:
      W.Got{None{}, s}
    case 1n:
      get_commit.some(W.get_nat(s))
    case 2n+p:
      W.Bad{}

def get_commit.go(r: W.Dec<Nat>) -> W.Dec<Maybe<&2, Nat>>:
  match r:
    case W.Got{t, s}:
      get_commit.tag(t, s)
    case W.Bad{}:
      W.Bad{}

# a commit, or none, at the start of s
def get_commit(s: String) -> W.Dec<Maybe<&2, Nat>>:
  get_commit.go(W.get_nat(s))

def get_seen.after(b: Bool, r: W.Dec<Maybe<&2, Nat>>) -> W.Dec<M.Seen>:
  match r:
    case W.Got{a, s}:
      W.Got{M.Seen{b, a}, s}
    case W.Bad{}:
      W.Bad{}

def get_seen.go(r: W.Dec<Bool>) -> W.Dec<M.Seen>:
  match r:
    case W.Got{b, s}:
      get_seen.after(b, get_commit(s))
    case W.Bad{}:
      W.Bad{}

# a job at the start of s
def get_seen(s: String) -> W.Dec<M.Seen>:
  get_seen.go(W.get_bool(s))

def get_seens.cons(x: M.Seen, r: W.Dec<List<&2, M.Seen>>) -> W.Dec<List<&2, M.Seen>>:
  match r:
    case W.Got{xs, s}:
      W.Got{x <> xs, s}
    case W.Bad{}:
      W.Bad{}

# n more jobs after the one cur answers
def get_seens.go(n: Nat, cur: W.Dec<M.Seen>) -> W.Dec<List<&2, M.Seen>>:
  match n:
    case 0n:
      match cur:
        case W.Got{x, s}:
          W.Got{[x], s}
        case W.Bad{}:
          W.Bad{}
    case 1n+m:
      match cur:
        case W.Got{x, s}:
          get_seens.cons(x, get_seens.go(m, get_seen(s)))
        case W.Bad{}:
          W.Bad{}

# the jobs, after their count r
def get_seens(r: W.Dec<Nat>) -> W.Dec<List<&2, M.Seen>>:
  match r:
    case W.Got{n, s}:
      match n:
        case 0n:
          W.Got{Nil{}, s}
        case 1n+m:
          get_seens.go(m, get_seen(s))
    case W.Bad{}:
      W.Bad{}

# Encoding
# --------

def put_kills.items(xs: List<&2, Bool>, rest: String) -> String:
  match xs:
    case Nil{}:
      rest
    case b <> t:
      W.put_bool(b, put_kills.items(t, rest))

def put_kills(+xs: List<&2, Bool>) -> String:
  W.put_nat(List.length(&2, Bool, xs), put_kills.items(xs, ""))

# The entry
# ---------

def run.end(whole: Bool, +target: Maybe<&2, Nat>, js: List<&2, M.Seen>) -> String:
  match whole:
    case True{}:
      put_kills(M.kills(js, target))
    case False{}:
      W.err("job_rewind: malformed request")

def run.jobs(+target: Maybe<&2, Nat>, r: W.Dec<List<&2, M.Seen>>) -> String:
  match r:
    case W.Got{js, s}:
      run.end(W.end(s), target, js)
    case W.Bad{}:
      W.err("job_rewind: malformed request")

def run(r: W.Dec<Maybe<&2, Nat>>) -> String:
  match r:
    case W.Got{+target, s}:
      run.jobs(target, get_seens(W.get_nat(s)))
    case W.Bad{}:
      W.err("job_rewind: malformed request")

def ffi(input: String) -> String:
  run(get_commit(input))
