# ffi_workflow: the entry of the compiled Bend core for a dynamic
# workflow run (crates/eukhe-core/src/durable/workflow): the admission of
# one `agent()` call (bend/workflow.bend `admit`) and a run's limits
# (`effective`). The codec is the wire format of bend/wire.bend:
#
#   request  0, Admit | 1, Limits
#   Admit    prior: Maybe<Sts>, k: Nat, rows: List<Row>, pool: Pool
#   Row      key: Nat, Sts
#   Sts      0 queued | 1 running | 2 done | 3 failed | 4 cancelled
#            | 5 cached
#   Pool     taken: Nat, left: Nat
#   Limits   concurrency: Nat, max agents: Nat, cap: Nat (0: no cap)
#   reply    to Admit: the decision (0 ended | 1 reattach | 2 i: reuse
#            row i | 3 spawn | 4 refused), then the pool; to Limits:
#            concurrency, max agents
#
# A malformed request, or one with input left over, answers the wire's
# error form.

import Base
import ./wire.bend as W
import ./workflow.bend as M

# Encoders
# --------

def put_sts(s: M.Sts, rest: String) -> String:
  match s:
    case M.Queued{}:
      W.put_nat(0n, rest)
    case M.Running{}:
      W.put_nat(1n, rest)
    case M.Finished{}:
      W.put_nat(2n, rest)
    case M.Erred{}:
      W.put_nat(3n, rest)
    case M.Cancelled{}:
      W.put_nat(4n, rest)
    case M.Cached{}:
      W.put_nat(5n, rest)

def put_row(r: M.Row, rest: String) -> String:
  match r:
    case M.Row{k, s}:
      W.put_nat(k, put_sts(s, rest))

def put_pool(p: M.Pool, rest: String) -> String:
  match p:
    case M.Pool{t, l}:
      W.put_nat(t, W.put_nat(l, rest))

def put_admit(a: M.Admit, rest: String) -> String:
  match a:
    case M.Ended{}:
      W.put_nat(0n, rest)
    case M.Reattach{}:
      W.put_nat(1n, rest)
    case M.Reuse{i}:
      W.put_nat(2n, W.put_nat(i, rest))
    case M.Spawn{}:
      W.put_nat(3n, rest)
    case M.Refused{}:
      W.put_nat(4n, rest)

def put_decision(d: M.Admit & M.Pool, rest: String) -> String:
  (a, p) = d
  put_admit(a, put_pool(p, rest))

def put_limits(l: M.Limits, rest: String) -> String:
  match l:
    case M.Limits{c, m}:
      W.put_nat(c, W.put_nat(m, rest))

# Decoders
# --------

def get_sts.tag(n: Nat, s: String) -> W.Dec<M.Sts>:
  match n:
    case 0n:
      W.Got{M.Queued{}, s}
    case 1n+a:
      match a:
        case 0n:
          W.Got{M.Running{}, s}
        case 1n+b:
          match b:
            case 0n:
              W.Got{M.Finished{}, s}
            case 1n+c:
              match c:
                case 0n:
                  W.Got{M.Erred{}, s}
                case 1n+d:
                  match d:
                    case 0n:
                      W.Got{M.Cancelled{}, s}
                    case 1n+e:
                      match e:
                        case 0n:
                          W.Got{M.Cached{}, s}
                        case 1n+f:
                          W.Bad{}

def get_sts.go(r: W.Dec<Nat>) -> W.Dec<M.Sts>:
  match r:
    case W.Got{n, s}:
      get_sts.tag(n, s)
    case W.Bad{}:
      W.Bad{}

def get_sts(s: String) -> W.Dec<M.Sts>:
  get_sts.go(W.get_nat(s))

def get_row.sts(k: Nat, r: W.Dec<M.Sts>) -> W.Dec<M.Row>:
  match r:
    case W.Got{st, s}:
      W.Got{M.Row{k, st}, s}
    case W.Bad{}:
      W.Bad{}

def get_row.go(r: W.Dec<Nat>) -> W.Dec<M.Row>:
  match r:
    case W.Got{k, s}:
      get_row.sts(k, get_sts(s))
    case W.Bad{}:
      W.Bad{}

def get_row(s: String) -> W.Dec<M.Row>:
  get_row.go(W.get_nat(s))

def get_prior.some(r: W.Dec<M.Sts>) -> W.Dec<Maybe<&2, M.Sts>>:
  match r:
    case W.Got{st, s}:
      W.Got{Some{st}, s}
    case W.Bad{}:
      W.Bad{}

def get_prior.tag(n: Nat, s: String) -> W.Dec<Maybe<&2, M.Sts>>:
  match n:
    case 0n:
      W.Got{None{}, s}
    case 1n+m:
      match m:
        case 0n:
          get_prior.some(get_sts(s))
        case 1n+x:
          W.Bad{}

def get_prior.go(r: W.Dec<Nat>) -> W.Dec<Maybe<&2, M.Sts>>:
  match r:
    case W.Got{n, s}:
      get_prior.tag(n, s)
    case W.Bad{}:
      W.Bad{}

def get_prior(s: String) -> W.Dec<Maybe<&2, M.Sts>>:
  get_prior.go(W.get_nat(s))

def get_pool.left(t: Nat, r: W.Dec<Nat>) -> W.Dec<M.Pool>:
  match r:
    case W.Got{l, s}:
      W.Got{M.Pool{t, l}, s}
    case W.Bad{}:
      W.Bad{}

def get_pool.go(r: W.Dec<Nat>) -> W.Dec<M.Pool>:
  match r:
    case W.Got{t, s}:
      get_pool.left(t, W.get_nat(s))
    case W.Bad{}:
      W.Bad{}

def get_pool(s: String) -> W.Dec<M.Pool>:
  get_pool.go(W.get_nat(s))

# the reply, when nothing is left of the input
def fin(done: Bool, reply: String) -> String:
  match done:
    case True{}:
      reply
    case False{}:
      W.err("workflow: input left over")

# The reply to an Admit request
def admit.reply(prior: Maybe<&2, M.Sts>, k: Nat, rows: List<&2, M.Row>, r: W.Dec<M.Pool>) -> String:
  match r:
    case W.Got{p, s}:
      fin(W.end(s), put_decision(M.admit(prior, k, rows, p), ""))
    case W.Bad{}:
      W.err("workflow: malformed pool")

def admit.rows(prior: Maybe<&2, M.Sts>, k: Nat, r: W.Dec<List<&2, M.Row>>) -> String:
  match r:
    case W.Got{rows, s}:
      admit.reply(prior, k, rows, get_pool(s))
    case W.Bad{}:
      W.err("workflow: malformed rows")

def admit.key(prior: Maybe<&2, M.Sts>, r: W.Dec<Nat>) -> String:
  match r:
    case W.Got{k, s}:
      admit.rows(prior, k, W.get_list(~M.Row, ~get_row, s))
    case W.Bad{}:
      W.err("workflow: malformed key")

def admit.go(r: W.Dec<Maybe<&2, M.Sts>>) -> String:
  match r:
    case W.Got{prior, s}:
      admit.key(prior, W.get_nat(s))
    case W.Bad{}:
      W.err("workflow: malformed prior row")

# The reply to a Limits request
def limits.cap(c: Nat, m: Nat, r: W.Dec<Nat>) -> String:
  match r:
    case W.Got{cap, s}:
      fin(W.end(s), put_limits(M.effective(M.Limits{c, m}, cap), ""))
    case W.Bad{}:
      W.err("workflow: malformed cap")

def limits.max(c: Nat, r: W.Dec<Nat>) -> String:
  match r:
    case W.Got{m, s}:
      limits.cap(c, m, W.get_nat(s))
    case W.Bad{}:
      W.err("workflow: malformed max agents")

def limits.go(r: W.Dec<Nat>) -> String:
  match r:
    case W.Got{c, s}:
      limits.max(c, W.get_nat(s))
    case W.Bad{}:
      W.err("workflow: malformed concurrency")

# The entry
# ---------

def ffi.tag(n: Nat, s: String) -> String:
  match n:
    case 0n:
      admit.go(get_prior(s))
    case 1n+m:
      match m:
        case 0n:
          limits.go(W.get_nat(s))
        case 1n+x:
          W.err("workflow: unknown request")

def ffi.go(r: W.Dec<Nat>) -> String:
  match r:
    case W.Got{n, s}:
      ffi.tag(n, s)
    case W.Bad{}:
      W.err("workflow: malformed request")

# One request: an agent call's admission, or a run's limits.
def ffi(input: String) -> String:
  ffi.go(W.get_nat(input))
