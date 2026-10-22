# ffi_facts: the entry of the compiled Bend core for the thinking budgets
# of bend/facts.bend section 2 (crates/eukhe-ai `api/simple_options.rs`,
# `api/google_shared/options.rs`; crates/eukhe-core `memory/summarizer.rs`).
# One request, one reply, in the wire format of bend/wire.bend:
#
#   request (a constructor)                          reply
#   0 Level{l: ELv, c: Customs, d: Budgets}          Nat   budget(c, d, Lv.of(l))
#   1 Room{b: Nat, m: Nat, a: Nat}                   Nat   room(b, m, a)
#   2 Adjust{base: Maybe<Nat>, mm: Nat, l: ELv,      Fit   adjust(base, mm, l, c, d, a)
#       c: Customs, d: Budgets, a: Nat}                    (max, then budget)
#   3 Google{rule: Maybe<Budgets>, c: Customs,       GB    gbudget(rule, c, l)
#       l: Lv}                                             (0 Dynamic, 1 Tokens{n}, 2 Unordered)
#   4 Aux{c: Customs, d: Budgets, a: Nat, top: Nat}  Nat   aux(c, d, a, top)
#
# A level is its tag in declaration order (ELv: minimal 0 .. max 5; Lv:
# minimal 0 .. high 3), Customs are 4 Maybe<Nat>, Budgets 4 Nat, both in
# level order. A malformed request, or one with input left over, answers
# the error form. Pure: no IO, no @unsafe, no foreign effect.

import Base
import ./wire.bend as W
import ./facts.bend as Fx

# Decoding
# --------

# two decoded values, in order
type P2<-A: Data, -B: Data> is Data:
  P2{fst: A, snd: B}

# the value of d paired with the next value, read by get from d's rest
def seq.fin(~A: Data, ~B: Data, a: A, d: W.Dec<B>) -> W.Dec<P2<A, B>>:
  match d:
    case W.Got{b, r}:
      W.Got{P2{a, b}, r}
    case W.Bad{}:
      W.Bad{}

def seq(~A: Data, ~B: Data, ~get: String -> W.Dec<B>, d: W.Dec<A>) -> W.Dec<P2<A, B>>:
  match d:
    case W.Got{a, r}:
      seq.fin(~A, ~B, a, get(r))
    case W.Bad{}:
      W.Bad{}

# a Maybe<Nat>: 0 None, 1 then the Nat
def get_mnat.some(d: W.Dec<Nat>) -> W.Dec<Maybe<&2, Nat>>:
  match d:
    case W.Got{n, r}:
      W.Got{Some{n}, r}
    case W.Bad{}:
      W.Bad{}

def get_mnat.tag(t: Nat, s: String) -> W.Dec<Maybe<&2, Nat>>:
  match t:
    case 0n:
      W.Got{None{}, s}
    case 1n+p:
      match p:
        case 0n:
          get_mnat.some(W.get_nat(s))
        case 1n+q:
          W.Bad{}

def get_mnat.go(d: W.Dec<Nat>) -> W.Dec<Maybe<&2, Nat>>:
  match d:
    case W.Got{t, r}:
      get_mnat.tag(t, r)
    case W.Bad{}:
      W.Bad{}

def get_mnat(s: String) -> W.Dec<Maybe<&2, Nat>>:
  get_mnat.go(W.get_nat(s))

# a request's level (ELv), by tag
def get_elv.tag(t: Nat, s: String) -> W.Dec<Fx.ELv>:
  match t:
    case 0n:
      W.Got{Fx.EMinimal{}, s}
    case 1n+a:
      match a:
        case 0n:
          W.Got{Fx.ELow{}, s}
        case 1n+b:
          match b:
            case 0n:
              W.Got{Fx.EMedium{}, s}
            case 1n+c:
              match c:
                case 0n:
                  W.Got{Fx.EHigh{}, s}
                case 1n+e:
                  match e:
                    case 0n:
                      W.Got{Fx.EXhigh{}, s}
                    case 1n+f:
                      match f:
                        case 0n:
                          W.Got{Fx.EMax{}, s}
                        case 1n+g:
                          W.Bad{}

def get_elv.go(d: W.Dec<Nat>) -> W.Dec<Fx.ELv>:
  match d:
    case W.Got{t, r}:
      get_elv.tag(t, r)
    case W.Bad{}:
      W.Bad{}

def get_elv(s: String) -> W.Dec<Fx.ELv>:
  get_elv.go(W.get_nat(s))

# a budget level (Lv), by tag
def get_lv.tag(t: Nat, s: String) -> W.Dec<Fx.Lv>:
  match t:
    case 0n:
      W.Got{Fx.Minimal{}, s}
    case 1n+a:
      match a:
        case 0n:
          W.Got{Fx.Low{}, s}
        case 1n+b:
          match b:
            case 0n:
              W.Got{Fx.Medium{}, s}
            case 1n+c:
              match c:
                case 0n:
                  W.Got{Fx.High{}, s}
                case 1n+e:
                  W.Bad{}

def get_lv.go(d: W.Dec<Nat>) -> W.Dec<Fx.Lv>:
  match d:
    case W.Got{t, r}:
      get_lv.tag(t, r)
    case W.Bad{}:
      W.Bad{}

def get_lv(s: String) -> W.Dec<Fx.Lv>:
  get_lv.go(W.get_nat(s))

# the user's budgets: 4 Maybe<Nat>, minimal to high
def get_customs.of(d: W.Dec<P2<P2<P2<Maybe<&2, Nat>, Maybe<&2, Nat>>, Maybe<&2, Nat>>, Maybe<&2, Nat>>>) -> W.Dec<Fx.Customs>:
  match d:
    case W.Got{q, r}:
      P2{q3, hi} = q
      P2{q2, me} = q3
      P2{mi, lo} = q2
      W.Got{Fx.Customs{mi, lo, me, hi}, r}
    case W.Bad{}:
      W.Bad{}

def get_customs(s: String) -> W.Dec<Fx.Customs>:
  get_customs.of(seq(~P2<P2<Maybe<&2, Nat>, Maybe<&2, Nat>>, Maybe<&2, Nat>>, ~Maybe<&2, Nat>, ~get_mnat, seq(~P2<Maybe<&2, Nat>, Maybe<&2, Nat>>, ~Maybe<&2, Nat>, ~get_mnat, seq(~Maybe<&2, Nat>, ~Maybe<&2, Nat>, ~get_mnat, get_mnat(s)))))

# a budget table: 4 Nat, minimal to high
def get_budgets.of(d: W.Dec<P2<P2<P2<Nat, Nat>, Nat>, Nat>>) -> W.Dec<Fx.Budgets>:
  match d:
    case W.Got{q, r}:
      P2{q3, hi} = q
      P2{q2, me} = q3
      P2{mi, lo} = q2
      W.Got{Fx.Budgets{mi, lo, me, hi}, r}
    case W.Bad{}:
      W.Bad{}

def get_budgets(s: String) -> W.Dec<Fx.Budgets>:
  get_budgets.of(seq(~P2<P2<Nat, Nat>, Nat>, ~Nat, ~W.get_nat, seq(~P2<Nat, Nat>, ~Nat, ~W.get_nat, seq(~Nat, ~Nat, ~W.get_nat, W.get_nat(s)))))

# a Maybe<Budgets>: 0 None, 1 then the table
def get_mbudgets.some(d: W.Dec<Fx.Budgets>) -> W.Dec<Maybe<&2, Fx.Budgets>>:
  match d:
    case W.Got{b, r}:
      W.Got{Some{b}, r}
    case W.Bad{}:
      W.Bad{}

def get_mbudgets.tag(t: Nat, s: String) -> W.Dec<Maybe<&2, Fx.Budgets>>:
  match t:
    case 0n:
      W.Got{None{}, s}
    case 1n+p:
      match p:
        case 0n:
          get_mbudgets.some(get_budgets(s))
        case 1n+q:
          W.Bad{}

def get_mbudgets.go(d: W.Dec<Nat>) -> W.Dec<Maybe<&2, Fx.Budgets>>:
  match d:
    case W.Got{t, r}:
      get_mbudgets.tag(t, r)
    case W.Bad{}:
      W.Bad{}

def get_mbudgets(s: String) -> W.Dec<Maybe<&2, Fx.Budgets>>:
  get_mbudgets.go(W.get_nat(s))

# Requests
# --------

type Req is Data:
  Level{l: Fx.ELv, c: Fx.Customs, d: Fx.Budgets}
  Room{b: Nat, m: Nat, a: Nat}
  Adjust{base: Maybe<&2, Nat>, mm: Nat, l: Fx.ELv, c: Fx.Customs, d: Fx.Budgets, a: Nat}
  Google{rule: Maybe<&2, Fx.Budgets>, c: Fx.Customs, l: Fx.Lv}
  Aux{c: Fx.Customs, d: Fx.Budgets, a: Nat, top: Nat}

def get_level.of(d: W.Dec<P2<P2<Fx.ELv, Fx.Customs>, Fx.Budgets>>) -> W.Dec<Req>:
  match d:
    case W.Got{q, r}:
      P2{q2, b} = q
      P2{l, c} = q2
      W.Got{Level{l, c, b}, r}
    case W.Bad{}:
      W.Bad{}

def get_room.of(d: W.Dec<P2<P2<Nat, Nat>, Nat>>) -> W.Dec<Req>:
  match d:
    case W.Got{q, r}:
      P2{q2, a} = q
      P2{b, m} = q2
      W.Got{Room{b, m, a}, r}
    case W.Bad{}:
      W.Bad{}

def get_adjust.of(d: W.Dec<P2<P2<P2<P2<P2<Maybe<&2, Nat>, Nat>, Fx.ELv>, Fx.Customs>, Fx.Budgets>, Nat>>) -> W.Dec<Req>:
  match d:
    case W.Got{q, r}:
      P2{q5, a} = q
      P2{q4, b} = q5
      P2{q3, c} = q4
      P2{q2, l} = q3
      P2{base, mm} = q2
      W.Got{Adjust{base, mm, l, c, b, a}, r}
    case W.Bad{}:
      W.Bad{}

def get_google.of(d: W.Dec<P2<P2<Maybe<&2, Fx.Budgets>, Fx.Customs>, Fx.Lv>>) -> W.Dec<Req>:
  match d:
    case W.Got{q, r}:
      P2{q2, l} = q
      P2{rule, c} = q2
      W.Got{Google{rule, c, l}, r}
    case W.Bad{}:
      W.Bad{}

def get_aux.of(d: W.Dec<P2<P2<P2<Fx.Customs, Fx.Budgets>, Nat>, Nat>>) -> W.Dec<Req>:
  match d:
    case W.Got{q, r}:
      P2{q3, top} = q
      P2{q2, a} = q3
      P2{c, b} = q2
      W.Got{Aux{c, b, a, top}, r}
    case W.Bad{}:
      W.Bad{}

def get_req.tag(t: Nat, s: String) -> W.Dec<Req>:
  match t:
    case 0n:
      get_level.of(seq(~P2<Fx.ELv, Fx.Customs>, ~Fx.Budgets, ~get_budgets, seq(~Fx.ELv, ~Fx.Customs, ~get_customs, get_elv(s))))
    case 1n+a:
      match a:
        case 0n:
          get_room.of(seq(~P2<Nat, Nat>, ~Nat, ~W.get_nat, seq(~Nat, ~Nat, ~W.get_nat, W.get_nat(s))))
        case 1n+b:
          match b:
            case 0n:
              get_adjust.of(seq(~P2<P2<P2<P2<Maybe<&2, Nat>, Nat>, Fx.ELv>, Fx.Customs>, Fx.Budgets>, ~Nat, ~W.get_nat, seq(~P2<P2<P2<Maybe<&2, Nat>, Nat>, Fx.ELv>, Fx.Customs>, ~Fx.Budgets, ~get_budgets, seq(~P2<P2<Maybe<&2, Nat>, Nat>, Fx.ELv>, ~Fx.Customs, ~get_customs, seq(~P2<Maybe<&2, Nat>, Nat>, ~Fx.ELv, ~get_elv, seq(~Maybe<&2, Nat>, ~Nat, ~W.get_nat, get_mnat(s)))))))
            case 1n+c:
              match c:
                case 0n:
                  get_google.of(seq(~P2<Maybe<&2, Fx.Budgets>, Fx.Customs>, ~Fx.Lv, ~get_lv, seq(~Maybe<&2, Fx.Budgets>, ~Fx.Customs, ~get_customs, get_mbudgets(s))))
                case 1n+e:
                  match e:
                    case 0n:
                      get_aux.of(seq(~P2<P2<Fx.Customs, Fx.Budgets>, Nat>, ~Nat, ~W.get_nat, seq(~P2<Fx.Customs, Fx.Budgets>, ~Nat, ~W.get_nat, seq(~Fx.Customs, ~Fx.Budgets, ~get_budgets, get_customs(s)))))
                    case 1n+f:
                      W.Bad{}

def get_req.go(d: W.Dec<Nat>) -> W.Dec<Req>:
  match d:
    case W.Got{t, r}:
      get_req.tag(t, r)
    case W.Bad{}:
      W.Bad{}

# a request
def get_req(s: String) -> W.Dec<Req>:
  get_req.go(W.get_nat(s))

# Replies
# -------

def put_gb(g: Fx.GB, rest: String) -> String:
  match g:
    case Fx.Dynamic{}:
      W.put_nat(0n, rest)
    case Fx.Tokens{n}:
      W.put_nat(1n, W.put_nat(n, rest))
    case Fx.Unordered{}:
      W.put_nat(2n, rest)

def put_fit(f: Fx.Fit, rest: String) -> String:
  match f:
    case Fx.Fit{m, b}:
      W.put_nat(m, W.put_nat(b, rest))

# the reply to a request
def answer(q: Req) -> String:
  match q:
    case Level{l, c, d}:
      W.put_nat(Fx.budget(c, d, Fx.Lv.of(l)), "")
    case Room{b, m, a}:
      W.put_nat(Fx.room(b, m, a), "")
    case Adjust{base, mm, l, c, d, a}:
      put_fit(Fx.adjust(base, mm, l, c, d, a), "")
    case Google{rule, c, l}:
      put_gb(Fx.gbudget(rule, c, l), "")
    case Aux{c, d, a, top}:
      W.put_nat(Fx.aux(c, d, a, top), "")

# whole is W.end(rest): nothing is left after the request
def ffi.done(whole: Bool, q: Req) -> String:
  match whole:
    case True{}:
      answer(q)
    case False{}:
      W.err("budget request: input left over")

def ffi.go(d: W.Dec<Req>) -> String:
  match d:
    case W.Got{q, r}:
      ffi.done(W.end(r), q)
    case W.Bad{}:
      W.err("budget request: malformed")

# the entry: decode the request, answer it
def ffi(input: String) -> String:
  ffi.go(get_req(input))
