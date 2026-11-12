# ffi_budget: the entry of the compiled Bend core for the ledger of a task
# tree's budget (bend/budget.bend; Rust: eukhe-bend rules/budget.rs, asked
# by eukhe-budget ledger.rs for every reservation, settlement, carve,
# close and funding). Grammar: crates/eukhe-bend/WIRE.md.
#
#   an amount   four Nats: money, tokens, tool calls, model requests
#   an ask      an amount, then a duration in ms (Nat)
#   a hold      its id (Nat), then its amount
#   an account  free, spent, lent, over (an amount each), the holds
#               (List), the deadline (Nat, ms)
#   a phase     a tag (Nat): 0 Working, 1 WrapUp, 2 Exhausted
#   request  a question, its tag then its fields:
#            0 reserve: the use, a tag (0 work, 1 final answer, 2 side
#              request), the asking agent's phase, the id (Nat), now
#              (Nat, ms), base, keep, the wanted ask, the smaller offers
#              (List of asks), the account
#            1 settle: the id (Nat), the actual amount, the account
#            2 carve: the parent agent's phase, now (Nat, ms), the wanted
#              ask, base, the parent's account
#            3 close: the child's account, the parent's account
#            4 fund: the ask, the account
#   reply    reserve: 0, the offer's place (Nat), its ask, the account,
#              T|F tight | 1, the reason, the agent's phase
#            settle, fund: the account
#            carve: 0, the parent's account, the child's account | 1, the
#              reason
#            close: 0, the parent's account, the child's account | 1,
#            a reason, its tag: 0 short, then the dimension, a tag
#              (0 money, 1 tokens, 2 time, 3 tool calls, 4 model
#              requests) | 1 the id is
#              held | 2 the phase admits nothing of the kind
#
# Malformed input (an unknown tag, a missing field, input left after the
# request) answers `E budget: malformed request`, never a default. Pure:
# no IO, no @unsafe.

import Base
import ./wire.bend as W
import ./budget.bend as B

# A request of the entry
type Req is Data:
  QReserve{use: B.Use, phase: B.Phase, id: Nat, now: Nat, base: B.Ask, keep: B.Ask, want: B.Ask, less: List<&2, B.Ask>, acct: B.Acct}
  QSettle{id: Nat, act: B.Amt, acct: B.Acct}
  QCarve{phase: B.Phase, now: Nat, want: B.Ask, base: B.Ask, acct: B.Acct}
  QClose{child: B.Acct, parent: B.Acct}
  QFund{n: B.Ask, acct: B.Acct}

# Decoders
# --------

def get_amt.r(c: Nat, k: Nat, n: Nat, r: W.Dec<Nat>) -> W.Dec<B.Amt>:
  match r:
    case W.Got{q, s}:
      W.Got{B.Amt{c, k, n, q}, s}
    case W.Bad{}:
      W.Bad{}

def get_amt.n(c: Nat, k: Nat, r: W.Dec<Nat>) -> W.Dec<B.Amt>:
  match r:
    case W.Got{n, s}:
      get_amt.r(c, k, n, W.get_nat(s))
    case W.Bad{}:
      W.Bad{}

def get_amt.k(c: Nat, r: W.Dec<Nat>) -> W.Dec<B.Amt>:
  match r:
    case W.Got{k, s}:
      get_amt.n(c, k, W.get_nat(s))
    case W.Bad{}:
      W.Bad{}

def get_amt.c(r: W.Dec<Nat>) -> W.Dec<B.Amt>:
  match r:
    case W.Got{c, s}:
      get_amt.k(c, W.get_nat(s))
    case W.Bad{}:
      W.Bad{}

# the amount at the start of s
def get_amt(s: String) -> W.Dec<B.Amt>:
  get_amt.c(W.get_nat(s))

def get_ask.ms(x: B.Amt, r: W.Dec<Nat>) -> W.Dec<B.Ask>:
  match r:
    case W.Got{m, s}:
      W.Got{B.Ask{x, m}, s}
    case W.Bad{}:
      W.Bad{}

def get_ask.amt(r: W.Dec<B.Amt>) -> W.Dec<B.Ask>:
  match r:
    case W.Got{x, s}:
      get_ask.ms(x, W.get_nat(s))
    case W.Bad{}:
      W.Bad{}

# the ask at the start of s
def get_ask(s: String) -> W.Dec<B.Ask>:
  get_ask.amt(get_amt(s))

def get_hold.amt(id: Nat, r: W.Dec<B.Amt>) -> W.Dec<B.Hold>:
  match r:
    case W.Got{x, s}:
      W.Got{B.Hold{id, x}, s}
    case W.Bad{}:
      W.Bad{}

def get_hold.id(r: W.Dec<Nat>) -> W.Dec<B.Hold>:
  match r:
    case W.Got{id, s}:
      get_hold.amt(id, get_amt(s))
    case W.Bad{}:
      W.Bad{}

# the hold at the start of s
def get_hold(s: String) -> W.Dec<B.Hold>:
  get_hold.id(W.get_nat(s))

# the phase of tag n
def get_phase.of(n: Nat, s: String) -> W.Dec<B.Phase>:
  match n:
    case 0n:
      W.Got{B.Working{}, s}
    case 1n+a:
      match a:
        case 0n:
          W.Got{B.WrapUp{}, s}
        case 1n+b:
          match b:
            case 0n:
              W.Got{B.Exhausted{}, s}
            case 1n+c:
              W.Bad{}

def get_phase.tag(r: W.Dec<Nat>) -> W.Dec<B.Phase>:
  match r:
    case W.Got{n, s}:
      get_phase.of(n, s)
    case W.Bad{}:
      W.Bad{}

# the phase at the start of s
def get_phase(s: String) -> W.Dec<B.Phase>:
  get_phase.tag(W.get_nat(s))

def get_acct.until(f: B.Amt, sp: B.Amt, l: B.Amt, o: B.Amt, h: List<&2, B.Hold>, r: W.Dec<Nat>) -> W.Dec<B.Acct>:
  match r:
    case W.Got{u, s}:
      W.Got{B.Acct{f, sp, l, o, h, u}, s}
    case W.Bad{}:
      W.Bad{}

def get_acct.holds(f: B.Amt, sp: B.Amt, l: B.Amt, o: B.Amt, r: W.Dec<List<&2, B.Hold>>) -> W.Dec<B.Acct>:
  match r:
    case W.Got{h, s}:
      get_acct.until(f, sp, l, o, h, W.get_nat(s))
    case W.Bad{}:
      W.Bad{}

def get_acct.over(f: B.Amt, sp: B.Amt, l: B.Amt, r: W.Dec<B.Amt>) -> W.Dec<B.Acct>:
  match r:
    case W.Got{o, s}:
      get_acct.holds(f, sp, l, o, W.get_list(~B.Hold, ~get_hold, s))
    case W.Bad{}:
      W.Bad{}

def get_acct.lent(f: B.Amt, sp: B.Amt, r: W.Dec<B.Amt>) -> W.Dec<B.Acct>:
  match r:
    case W.Got{l, s}:
      get_acct.over(f, sp, l, get_amt(s))
    case W.Bad{}:
      W.Bad{}

def get_acct.spent(f: B.Amt, r: W.Dec<B.Amt>) -> W.Dec<B.Acct>:
  match r:
    case W.Got{sp, s}:
      get_acct.lent(f, sp, get_amt(s))
    case W.Bad{}:
      W.Bad{}

def get_acct.free(r: W.Dec<B.Amt>) -> W.Dec<B.Acct>:
  match r:
    case W.Got{f, s}:
      get_acct.spent(f, get_amt(s))
    case W.Bad{}:
      W.Bad{}

# the account at the start of s
def get_acct(s: String) -> W.Dec<B.Acct>:
  get_acct.free(get_amt(s))

# Requests
# --------

def get_reserve.acct(u: B.Use, p: B.Phase, id: Nat, now: Nat, base: B.Ask, keep: B.Ask, want: B.Ask, less: List<&2, B.Ask>, r: W.Dec<B.Acct>) -> W.Dec<Req>:
  match r:
    case W.Got{a, s}:
      W.Got{QReserve{u, p, id, now, base, keep, want, less, a}, s}
    case W.Bad{}:
      W.Bad{}

def get_reserve.less(u: B.Use, p: B.Phase, id: Nat, now: Nat, base: B.Ask, keep: B.Ask, want: B.Ask, r: W.Dec<List<&2, B.Ask>>) -> W.Dec<Req>:
  match r:
    case W.Got{less, s}:
      get_reserve.acct(u, p, id, now, base, keep, want, less, get_acct(s))
    case W.Bad{}:
      W.Bad{}

def get_reserve.want(u: B.Use, p: B.Phase, id: Nat, now: Nat, base: B.Ask, keep: B.Ask, r: W.Dec<B.Ask>) -> W.Dec<Req>:
  match r:
    case W.Got{want, s}:
      get_reserve.less(u, p, id, now, base, keep, want, W.get_list(~B.Ask, ~get_ask, s))
    case W.Bad{}:
      W.Bad{}

def get_reserve.keep(u: B.Use, p: B.Phase, id: Nat, now: Nat, base: B.Ask, r: W.Dec<B.Ask>) -> W.Dec<Req>:
  match r:
    case W.Got{keep, s}:
      get_reserve.want(u, p, id, now, base, keep, get_ask(s))
    case W.Bad{}:
      W.Bad{}

def get_reserve.base(u: B.Use, p: B.Phase, id: Nat, now: Nat, r: W.Dec<B.Ask>) -> W.Dec<Req>:
  match r:
    case W.Got{base, s}:
      get_reserve.keep(u, p, id, now, base, get_ask(s))
    case W.Bad{}:
      W.Bad{}

def get_reserve.now(u: B.Use, p: B.Phase, id: Nat, r: W.Dec<Nat>) -> W.Dec<Req>:
  match r:
    case W.Got{now, s}:
      get_reserve.base(u, p, id, now, get_ask(s))
    case W.Bad{}:
      W.Bad{}

def get_reserve.id(u: B.Use, p: B.Phase, r: W.Dec<Nat>) -> W.Dec<Req>:
  match r:
    case W.Got{id, s}:
      get_reserve.now(u, p, id, W.get_nat(s))
    case W.Bad{}:
      W.Bad{}

def get_reserve.phase(u: B.Use, r: W.Dec<B.Phase>) -> W.Dec<Req>:
  match r:
    case W.Got{p, s}:
      get_reserve.id(u, p, W.get_nat(s))
    case W.Bad{}:
      W.Bad{}

# the use of tag n, then the rest of a reserve
def get_reserve.use(n: Nat, s: String) -> W.Dec<Req>:
  match n:
    case 0n:
      get_reserve.phase(B.Work{}, get_phase(s))
    case 1n+a:
      match a:
        case 0n:
          get_reserve.phase(B.Final{}, get_phase(s))
        case 1n+b:
          match b:
            case 0n:
              get_reserve.phase(B.Side{}, get_phase(s))
            case 1n+c:
              W.Bad{}

def get_reserve(r: W.Dec<Nat>) -> W.Dec<Req>:
  match r:
    case W.Got{n, s}:
      get_reserve.use(n, s)
    case W.Bad{}:
      W.Bad{}

def get_settle.acct(id: Nat, act: B.Amt, r: W.Dec<B.Acct>) -> W.Dec<Req>:
  match r:
    case W.Got{a, s}:
      W.Got{QSettle{id, act, a}, s}
    case W.Bad{}:
      W.Bad{}

def get_settle.act(id: Nat, r: W.Dec<B.Amt>) -> W.Dec<Req>:
  match r:
    case W.Got{act, s}:
      get_settle.acct(id, act, get_acct(s))
    case W.Bad{}:
      W.Bad{}

def get_settle(r: W.Dec<Nat>) -> W.Dec<Req>:
  match r:
    case W.Got{id, s}:
      get_settle.act(id, get_amt(s))
    case W.Bad{}:
      W.Bad{}

def get_carve.acct(p: B.Phase, now: Nat, want: B.Ask, base: B.Ask, r: W.Dec<B.Acct>) -> W.Dec<Req>:
  match r:
    case W.Got{a, s}:
      W.Got{QCarve{p, now, want, base, a}, s}
    case W.Bad{}:
      W.Bad{}

def get_carve.base(p: B.Phase, now: Nat, want: B.Ask, r: W.Dec<B.Ask>) -> W.Dec<Req>:
  match r:
    case W.Got{base, s}:
      get_carve.acct(p, now, want, base, get_acct(s))
    case W.Bad{}:
      W.Bad{}

def get_carve.want(p: B.Phase, now: Nat, r: W.Dec<B.Ask>) -> W.Dec<Req>:
  match r:
    case W.Got{want, s}:
      get_carve.base(p, now, want, get_ask(s))
    case W.Bad{}:
      W.Bad{}

def get_carve.now(p: B.Phase, r: W.Dec<Nat>) -> W.Dec<Req>:
  match r:
    case W.Got{now, s}:
      get_carve.want(p, now, get_ask(s))
    case W.Bad{}:
      W.Bad{}

def get_carve(r: W.Dec<B.Phase>) -> W.Dec<Req>:
  match r:
    case W.Got{p, s}:
      get_carve.now(p, W.get_nat(s))
    case W.Bad{}:
      W.Bad{}

def get_close.parent(c: B.Acct, r: W.Dec<B.Acct>) -> W.Dec<Req>:
  match r:
    case W.Got{p, s}:
      W.Got{QClose{c, p}, s}
    case W.Bad{}:
      W.Bad{}

def get_close(r: W.Dec<B.Acct>) -> W.Dec<Req>:
  match r:
    case W.Got{c, s}:
      get_close.parent(c, get_acct(s))
    case W.Bad{}:
      W.Bad{}

def get_fund.acct(n: B.Ask, r: W.Dec<B.Acct>) -> W.Dec<Req>:
  match r:
    case W.Got{a, s}:
      W.Got{QFund{n, a}, s}
    case W.Bad{}:
      W.Bad{}

def get_fund(r: W.Dec<B.Ask>) -> W.Dec<Req>:
  match r:
    case W.Got{n, s}:
      get_fund.acct(n, get_acct(s))
    case W.Bad{}:
      W.Bad{}

# the request of tag n
def get_req.of(n: Nat, s: String) -> W.Dec<Req>:
  match n:
    case 0n:
      get_reserve(W.get_nat(s))
    case 1n+a:
      match a:
        case 0n:
          get_settle(W.get_nat(s))
        case 1n+b:
          match b:
            case 0n:
              get_carve(get_phase(s))
            case 1n+c:
              match c:
                case 0n:
                  get_close(get_acct(s))
                case 1n+d:
                  match d:
                    case 0n:
                      get_fund(get_ask(s))
                    case 1n+e:
                      W.Bad{}

def get_req.tag(r: W.Dec<Nat>) -> W.Dec<Req>:
  match r:
    case W.Got{n, s}:
      get_req.of(n, s)
    case W.Bad{}:
      W.Bad{}

# the request at the start of s
def get_req(s: String) -> W.Dec<Req>:
  get_req.tag(W.get_nat(s))

# Encoders
# --------

def put_amt(x: B.Amt, rest: String) -> String:
  match x:
    case B.Amt{c, k, n, r}:
      W.put_nat(c, W.put_nat(k, W.put_nat(n, W.put_nat(r, rest))))

def put_ask(x: B.Ask, rest: String) -> String:
  match x:
    case B.Ask{a, m}:
      put_amt(a, W.put_nat(m, rest))

def put_hold(h: B.Hold, rest: String) -> String:
  match h:
    case B.Hold{id, x}:
      W.put_nat(id, put_amt(x, rest))

def put_phase(p: B.Phase, rest: String) -> String:
  match p:
    case B.Working{}:
      W.put_nat(0n, rest)
    case B.WrapUp{}:
      W.put_nat(1n, rest)
    case B.Exhausted{}:
      W.put_nat(2n, rest)

def put_acct(a: B.Acct, rest: String) -> String:
  match a:
    case B.Acct{f, sp, l, o, h, u}:
      put_amt(f, put_amt(sp, put_amt(l, put_amt(o, W.put_list(~B.Hold, ~put_hold, h, W.put_nat(u, rest))))))

def put_dim(d: B.Dim, rest: String) -> String:
  match d:
    case B.Cost{}:
      W.put_nat(0n, rest)
    case B.Tok{}:
      W.put_nat(1n, rest)
    case B.Time{}:
      W.put_nat(2n, rest)
    case B.Calls{}:
      W.put_nat(3n, rest)
    case B.Reqs{}:
      W.put_nat(4n, rest)

def put_why(w: B.Why, rest: String) -> String:
  match w:
    case B.Short{d}:
      W.put_nat(0n, put_dim(d, rest))
    case B.Held{}:
      W.put_nat(1n, rest)
    case B.Stopped{}:
      W.put_nat(2n, rest)

def put_grant(g: B.Grant) -> String:
  match g:
    case B.Granted{i, c, a, t}:
      W.put_nat(0n, W.put_nat(i, put_ask(c, put_acct(a, W.put_bool(t, "")))))
    case B.Refused{w, p}:
      W.put_nat(1n, put_why(w, put_phase(p, "")))

def put_carve(c: B.Carve) -> String:
  match c:
    case B.Carved{p, k}:
      W.put_nat(0n, put_acct(p, put_acct(k, "")))
    case B.Kept{w}:
      W.put_nat(1n, put_why(w, ""))

def put_close(c: B.Close) -> String:
  match c:
    case B.Closed{p, k}:
      W.put_nat(0n, put_acct(p, put_acct(k, "")))
    case B.Busy{}:
      W.put_nat(1n, "")

# The entry
# ---------

# the reply of a request: the model's answer, encoded
def answer(q: Req) -> String:
  match q:
    case QReserve{u, p, id, now, base, keep, want, less, a}:
      put_grant(B.reserve(u, p, id, now, base, keep, want, less, a))
    case QSettle{id, act, a}:
      put_acct(B.settle(id, act, a), "")
    case QCarve{p, now, want, base, a}:
      put_carve(B.carve(p, now, want, base, a))
    case QClose{c, p}:
      put_close(B.close(c, p))
    case QFund{n, a}:
      put_acct(B.fund(n, a), "")

def ffi.done(q: Req, end: Bool) -> String:
  match end:
    case True{}:
      answer(q)
    case False{}:
      W.err("budget: malformed request")

def ffi.got(r: W.Dec<Req>) -> String:
  match r:
    case W.Got{q, +s}:
      ffi.done(q, W.end(s))
    case W.Bad{}:
      W.err("budget: malformed request")

# the entry: decode the request, answer the model's decision
def ffi(input: String) -> String:
  ffi.got(get_req(input))
