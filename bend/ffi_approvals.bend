# ffi_approvals: the approval gate of one session as an entry of the
# compiled Bend core (bend/approvals.bend; Rust: crates/eukhe-bend/src/
# rules/approvals.rs, driven by crates/eukhe-daemon/src/shell_approval.rs).
# The codec is the wire format of bend/wire.bend (crates/eukhe-bend/
# WIRE.md).
#
# The call answers the default auto set:
#
#   call    nothing                  reply: List<Nat> (`Am.default_auto`)
#
# The stepper is one session's desk (`Am.D`, kept in the Bend heap): Rust
# sends each event as it arrives and does what the reply says.
#
#   open    nothing                  reply: empty
#   step    Ev                       reply: an ask's key (Nat), then Acts;
#                                    any other event: Acts
#   Ev      0, id: String, effects: List<Nat>, here: Here, parent: Bool
#                                    (a question reaches the session)
#           | 1, id: String, yes: Bool        (a client's answer)
#           | 2, here: Here, parent: Bool     (a client detached)
#           | 3, key: Nat                     (the step stopped waiting)
#           | 4, key: Nat, fate: Fate         (the parent's answer)
#   Here    0 nobody | 1 the phone gateway alone | 2 an interactive client
#   Fate    0 runs | 1 denied | 2 unanswered | 3 refused by the gateway rule
#   Acts    List<Act>
#   Act     0, key (show) | 1, key (settle) | 2, key (relay)
#           | 3, key, Fate (wake) | 4 (took) | 5 (gone)
#
# A call with input answers the error form "approvals: malformed request".
# A malformed event, or one with input left over, answers the error form
# "approvals: malformed event" and keeps the desk; an open with input
# opens the refused state, which answers every step "approvals: the open
# was refused". laws/approvals/ pins the entry. Pure: no IO, no @unsafe.

import Base
import ./wire.bend as W
import ./approvals.bend as Am

# The call
# --------

def ffi.end(whole: Bool) -> String:
  match whole:
    case True{}:
      W.put_list(~Nat, ~W.put_nat, Am.default_auto(), "")
    case False{}:
      W.err("approvals: malformed request")

# the call: the default auto set
def ffi(input: String) -> String:
  ffi.end(W.end(input))

# Decoders
# --------

def get_here(r: W.Dec<Nat>) -> W.Dec<Am.Here>:
  match r:
    case W.Got{t, s}:
      match t:
        case 0n:
          W.Got{Am.Nobody{}, s}
        case 1n:
          W.Got{Am.GatewayOnly{}, s}
        case 2n:
          W.Got{Am.Clients{}, s}
        case 3n+u:
          W.Bad{}
    case W.Bad{}:
      W.Bad{}

def get_fate(r: W.Dec<Nat>) -> W.Dec<Am.Fate>:
  match r:
    case W.Got{t, s}:
      match t:
        case 0n:
          W.Got{Am.Runs{}, s}
        case 1n:
          W.Got{Am.Denied{}, s}
        case 2n:
          W.Got{Am.Unheard{}, s}
        case 3n:
          W.Got{Am.GatewayRefused{}, s}
        case 4n+u:
          W.Bad{}
    case W.Bad{}:
      W.Bad{}

def ask.parent(id: String, es: List<&2, Nat>, h: Am.Here, r: W.Dec<Bool>) -> W.Dec<Am.Ev>:
  match r:
    case W.Got{p, s}:
      W.Got{Am.EAsk{id, es, h, p}, s}
    case W.Bad{}:
      W.Bad{}

def ask.here(id: String, es: List<&2, Nat>, r: W.Dec<Am.Here>) -> W.Dec<Am.Ev>:
  match r:
    case W.Got{h, s}:
      ask.parent(id, es, h, W.get_bool(s))
    case W.Bad{}:
      W.Bad{}

def ask.effs(id: String, r: W.Dec<List<&2, Nat>>) -> W.Dec<Am.Ev>:
  match r:
    case W.Got{es, s}:
      ask.here(id, es, get_here(W.get_nat(s)))
    case W.Bad{}:
      W.Bad{}

def ask.id(r: W.Dec<String>) -> W.Dec<Am.Ev>:
  match r:
    case W.Got{id, s}:
      ask.effs(id, W.get_list(~Nat, ~W.get_nat, s))
    case W.Bad{}:
      W.Bad{}

def answer.yes(id: String, r: W.Dec<Bool>) -> W.Dec<Am.Ev>:
  match r:
    case W.Got{y, s}:
      W.Got{Am.EAnswer{id, y}, s}
    case W.Bad{}:
      W.Bad{}

def answer.id(r: W.Dec<String>) -> W.Dec<Am.Ev>:
  match r:
    case W.Got{id, s}:
      answer.yes(id, W.get_bool(s))
    case W.Bad{}:
      W.Bad{}

def detach.parent(h: Am.Here, r: W.Dec<Bool>) -> W.Dec<Am.Ev>:
  match r:
    case W.Got{p, s}:
      W.Got{Am.EDetach{h, p}, s}
    case W.Bad{}:
      W.Bad{}

def detach.here(r: W.Dec<Am.Here>) -> W.Dec<Am.Ev>:
  match r:
    case W.Got{h, s}:
      detach.parent(h, W.get_bool(s))
    case W.Bad{}:
      W.Bad{}

def cancel.key(r: W.Dec<Nat>) -> W.Dec<Am.Ev>:
  match r:
    case W.Got{k, s}:
      W.Got{Am.ECancel{k}, s}
    case W.Bad{}:
      W.Bad{}

def back.fate(k: Nat, r: W.Dec<Am.Fate>) -> W.Dec<Am.Ev>:
  match r:
    case W.Got{f, s}:
      W.Got{Am.EBack{k, f}, s}
    case W.Bad{}:
      W.Bad{}

def back.key(r: W.Dec<Nat>) -> W.Dec<Am.Ev>:
  match r:
    case W.Got{k, s}:
      back.fate(k, get_fate(W.get_nat(s)))
    case W.Bad{}:
      W.Bad{}

def get_ev.tag(t: Nat, s: String) -> W.Dec<Am.Ev>:
  match t:
    case 0n:
      ask.id(W.get_str(s))
    case 1n:
      answer.id(W.get_str(s))
    case 2n:
      detach.here(get_here(W.get_nat(s)))
    case 3n:
      cancel.key(W.get_nat(s))
    case 4n:
      back.key(W.get_nat(s))
    case 5n+u:
      W.Bad{}

def get_ev.go(r: W.Dec<Nat>) -> W.Dec<Am.Ev>:
  match r:
    case W.Got{t, s}:
      get_ev.tag(t, s)
    case W.Bad{}:
      W.Bad{}

# the event at the start of s
def get_ev(s: String) -> W.Dec<Am.Ev>:
  get_ev.go(W.get_nat(s))

# Encoders
# --------

def put_fate(f: Am.Fate, rest: String) -> String:
  match f:
    case Am.Runs{}:
      W.put_nat(0n, rest)
    case Am.Denied{}:
      W.put_nat(1n, rest)
    case Am.Unheard{}:
      W.put_nat(2n, rest)
    case Am.GatewayRefused{}:
      W.put_nat(3n, rest)

def put_act(a: Am.Act, rest: String) -> String:
  match a:
    case Am.AShow{k}:
      W.put_nat(0n, W.put_nat(k, rest))
    case Am.ASettle{k}:
      W.put_nat(1n, W.put_nat(k, rest))
    case Am.ARelay{k}:
      W.put_nat(2n, W.put_nat(k, rest))
    case Am.AWake{k, f}:
      W.put_nat(3n, W.put_nat(k, put_fate(f, rest)))
    case Am.ATook{}:
      W.put_nat(4n, rest)
    case Am.AGone{}:
      W.put_nat(5n, rest)

def put_acts.go(as: List<&2, Am.Act>, rest: String) -> String:
  match as:
    case Nil{}:
      rest
    case a <> t:
      put_act(a, put_acts.go(t, rest))

def put_acts(+as: List<&2, Am.Act>) -> String:
  W.put_nat(List.length(&2, Am.Act, as), put_acts.go(as, ""))

# an ask's reply leads with the key it got (the desk's next key before it)
def put_reply(e: Am.Ev, n: Nat, as: List<&2, Am.Act>) -> String:
  match e:
    case Am.EAsk{id, es, h, p}:
      W.put_nat(n, put_acts(as))
    case Am.EAnswer{id, y}:
      put_acts(as)
    case Am.EDetach{h, p}:
      put_acts(as)
    case Am.ECancel{k}:
      put_acts(as)
    case Am.EBack{k, f}:
      put_acts(as)

# The stepper
# -----------

# the desk, or a refused open
type St is Data:
  Live{d: Am.D}
  Refused{}

def open.end(whole: Bool) -> St & String:
  match whole:
    case True{}:
      (Live{Am.D.empty()}, "")
    case False{}:
      (Refused{}, W.err("approvals: the open takes no input"))

# open: an empty desk, the first key next
def open(input: String) -> St & String:
  open.end(W.end(input))

def D.next(d: Am.D) -> Nat:
  match d:
    case Am.D{n, qs}:
      n

def step.reply(e: Am.Ev, n: Nat, r: Am.D & List<&2, Am.Act>) -> St & String:
  (d, as) = r
  (Live{d}, put_reply(e, n, as))

def step.end(whole: Bool, +d: Am.D, +e: Am.Ev) -> St & String:
  match whole:
    case True{}:
      step.reply(e, D.next(d), Am.dstep(d, e))
    case False{}:
      (Live{d}, W.err("approvals: malformed event"))

def step.ev(+d: Am.D, r: W.Dec<Am.Ev>) -> St & String:
  match r:
    case W.Got{e, rest}:
      step.end(W.end(rest), d, e)
    case W.Bad{}:
      (Live{d}, W.err("approvals: malformed event"))

# step: one event; the reply is what Rust does
def step(st: St, input: String) -> St & String:
  match st:
    case Live{d}:
      step.ev(d, get_ev(input))
    case Refused{}:
      (Refused{}, W.err("approvals: the open was refused"))
