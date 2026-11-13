# ffi_budget_share: the entry of the compiled Bend core for the offer a
# reservation of an agent sharing its account starts from
# (bend/budget_share.bend; Rust: eukhe-bend rules/budget.rs share_start).
# Grammar: crates/eukhe-bend/WIRE.md; amounts and asks as
# bend/ffi_budget.bend spells them.
#
#   an amount   four Nats: money, tokens, tool calls, model requests
#   an ask      an amount, then a duration in ms (Nat)
#   request  n, the account's Working agents that hold nothing, the asker
#            among them (Nat); the use, a tag (0 work, 1 final answer, 2
#            side request); base, keep, the wanted ask; the smaller offers
#            (List of asks); what is free (an amount); now (Nat, ms); the
#            deadline (Nat, ms)
#   reply    the place among the wanted ask and then the smaller offers
#            the reservation starts from (Nat)
#
# Malformed input (an unknown tag, a missing field, input left after the
# request) answers `E budget_share: malformed request`, never a default.
# Pure: no IO, no @unsafe.

import Base
import ./wire.bend as W
import ./budget.bend as B
import ./ffi_budget.bend as FBg
import ./budget_share.bend as Bs

# A request of the entry
type Req is Data:
  Req{n: Nat, use: B.Use, base: B.Ask, keep: B.Ask, want: B.Ask, less: List<&2, B.Ask>, free: B.Amt, now: Nat, until: Nat}

# Decoders
# --------

def get_req.until(n: Nat, u: B.Use, base: B.Ask, keep: B.Ask, want: B.Ask, less: List<&2, B.Ask>, free: B.Amt, now: Nat, r: W.Dec<Nat>) -> W.Dec<Req>:
  match r:
    case W.Got{until, s}:
      W.Got{Req{n, u, base, keep, want, less, free, now, until}, s}
    case W.Bad{}:
      W.Bad{}

def get_req.now(n: Nat, u: B.Use, base: B.Ask, keep: B.Ask, want: B.Ask, less: List<&2, B.Ask>, free: B.Amt, r: W.Dec<Nat>) -> W.Dec<Req>:
  match r:
    case W.Got{now, s}:
      get_req.until(n, u, base, keep, want, less, free, now, W.get_nat(s))
    case W.Bad{}:
      W.Bad{}

def get_req.free(n: Nat, u: B.Use, base: B.Ask, keep: B.Ask, want: B.Ask, less: List<&2, B.Ask>, r: W.Dec<B.Amt>) -> W.Dec<Req>:
  match r:
    case W.Got{free, s}:
      get_req.now(n, u, base, keep, want, less, free, W.get_nat(s))
    case W.Bad{}:
      W.Bad{}

def get_req.less(n: Nat, u: B.Use, base: B.Ask, keep: B.Ask, want: B.Ask, r: W.Dec<List<&2, B.Ask>>) -> W.Dec<Req>:
  match r:
    case W.Got{less, s}:
      get_req.free(n, u, base, keep, want, less, FBg.get_amt(s))
    case W.Bad{}:
      W.Bad{}

def get_req.want(n: Nat, u: B.Use, base: B.Ask, keep: B.Ask, r: W.Dec<B.Ask>) -> W.Dec<Req>:
  match r:
    case W.Got{want, s}:
      get_req.less(n, u, base, keep, want, W.get_list(~B.Ask, ~FBg.get_ask, s))
    case W.Bad{}:
      W.Bad{}

def get_req.keep(n: Nat, u: B.Use, base: B.Ask, r: W.Dec<B.Ask>) -> W.Dec<Req>:
  match r:
    case W.Got{keep, s}:
      get_req.want(n, u, base, keep, FBg.get_ask(s))
    case W.Bad{}:
      W.Bad{}

def get_req.base(n: Nat, u: B.Use, r: W.Dec<B.Ask>) -> W.Dec<Req>:
  match r:
    case W.Got{base, s}:
      get_req.keep(n, u, base, FBg.get_ask(s))
    case W.Bad{}:
      W.Bad{}

# the use of tag t, then the rest of the request
def get_req.use(t: Nat, n: Nat, s: String) -> W.Dec<Req>:
  match t:
    case 0n:
      get_req.base(n, B.Work{}, FBg.get_ask(s))
    case 1n+a:
      match a:
        case 0n:
          get_req.base(n, B.Final{}, FBg.get_ask(s))
        case 1n+b:
          match b:
            case 0n:
              get_req.base(n, B.Side{}, FBg.get_ask(s))
            case 1n+c:
              W.Bad{}

def get_req.tag(n: Nat, r: W.Dec<Nat>) -> W.Dec<Req>:
  match r:
    case W.Got{t, s}:
      get_req.use(t, n, s)
    case W.Bad{}:
      W.Bad{}

def get_req.n(r: W.Dec<Nat>) -> W.Dec<Req>:
  match r:
    case W.Got{n, s}:
      get_req.tag(n, W.get_nat(s))
    case W.Bad{}:
      W.Bad{}

# the request at the start of s
def get_req(s: String) -> W.Dec<Req>:
  get_req.n(W.get_nat(s))

# The entry
# ---------

# the model's answer to a request
def answer(q: Req) -> Nat:
  match q:
    case Req{n, u, base, keep, want, less, free, now, until}:
      Bs.start(n, u, base, keep, want, less, free, now, until)

def ffi.done(q: Req, end: Bool) -> String:
  match end:
    case True{}:
      W.put_nat(answer(q), "")
    case False{}:
      W.err("budget_share: malformed request")

def ffi.got(r: W.Dec<Req>) -> String:
  match r:
    case W.Got{q, +s}:
      ffi.done(q, W.end(s))
    case W.Bad{}:
      W.err("budget_share: malformed request")

# the entry: decode the request, answer the place the reservation starts
# from
def ffi(input: String) -> String:
  ffi.got(get_req(input))
