# ffi_quirks: the quirks rulebook (bend/infer.bend section 1: `verdicts`,
# `lookup`) as a stepper of the compiled Bend core
# (crates/eukhe-ai/src/quirks, through crates/eukhe-bend/src/rules/quirks.rs).
# The state holds a rulebook that compiles; each lookup ships only the
# query. In the wire format of bend/wire.bend:
#
#   open  (known: List<Nat>, rules: List<Nat>)    the known directives; the
#                                                 rules, four Nats each:
#                                                 layer (0 family, 1 model,
#                                                 2 host), target, directive,
#                                                 value
#   reply (compiles: Bool, verdicts: List<V>)     one verdict per rule: 0
#                                                 fine, 1 unknown directive,
#                                                 2 then j: clashes with the
#                                                 rule of index j (the first
#                                                 later one)
#   step  [family, model, host, directive]        a lookup, as a List<Nat>
#   reply 0 | 1 then the value                    Unknown | Known
#
# A rulebook that compiles opens the state that answers lookups; one that
# does not, or a malformed open, opens the refused state, which answers
# every step with the error form. A malformed lookup answers the error
# form and keeps the rulebook. laws/quirks.bend pins the entry. Pure: no
# IO, no @unsafe, no foreign effect.

import Base
import ./wire.bend as W
import ./infer.bend as If

# a rulebook that compiles, or the refused state
type St is Data:
  Book{rs: List<&2, If.Rule>}
  Shut{}

# Decoding
# --------

def lay(n: Nat) -> Maybe<&2, If.Lay>:
  match n:
    case 0n:
      Some{If.Fam{}}
    case 1n:
      Some{If.Mod{}}
    case 2n:
      Some{If.Host{}}
    case 3n+p:
      None{}

def rules.cons(m: Maybe<&2, If.Lay>, t: Nat, d: Nat, v: Nat, r: Maybe<&2, List<&2, If.Rule>>) -> Maybe<&2, List<&2, If.Rule>>:
  match m:
    case None{}:
      None{}
    case Some{l}:
      match r:
        case None{}:
          None{}
        case Some{rs}:
          Some{If.Rule{l, t, d, v} <> rs}

# the rules a flat list spells, four Nats each
def rules(xs: List<&2, Nat>) -> Maybe<&2, List<&2, If.Rule>>:
  match xs:
    case Nil{}:
      Some{Nil{}}
    case l <> a:
      match a:
        case Nil{}:
          None{}
        case t <> b:
          match b:
            case Nil{}:
              None{}
            case d <> c:
              match c:
                case Nil{}:
                  None{}
                case v <> rest:
                  rules.cons(lay(l), t, d, v, rules(rest))

# a lookup: the query and the directive
type Ask is Data:
  Ask{q: If.Query, d: Nat}

# the lookup a list spells: exactly four Nats
def ask(xs: List<&2, Nat>) -> Maybe<&2, Ask>:
  match xs:
    case Nil{}:
      None{}
    case f <> a:
      match a:
        case Nil{}:
          None{}
        case m <> b:
          match b:
            case Nil{}:
              None{}
            case h <> c:
              match c:
                case Nil{}:
                  None{}
                case d <> e:
                  match e:
                    case Nil{}:
                      Some{Ask{If.Query{f, m, h}, d}}
                    case x <> y:
                      None{}

# Encoding
# --------

def put_verdict(v: If.Verdict, rest: String) -> String:
  match v:
    case If.Fine{}:
      W.put_nat(0n, rest)
    case If.Unheard{}:
      W.put_nat(1n, rest)
    case If.ClashAt{j}:
      W.put_nat(2n, W.put_nat(j, rest))

def put_ans(a: If.Ans, rest: String) -> String:
  match a:
    case If.Unknown{}:
      W.put_nat(0n, rest)
    case If.Known{v}:
      W.put_nat(1n, W.put_nat(v, rest))

# Open
# ----

def malformed() -> String:
  W.err("quirks: malformed rulebook")

# ok: every verdict is fine (the rulebook compiles)
def open.reply(ok: Bool, rs: List<&2, If.Rule>, vs: List<&2, If.Verdict>) -> St & String:
  match ok:
    case True{}:
      (Book{rs}, W.put_bool(True{}, W.put_list(~If.Verdict, ~put_verdict, vs, "")))
    case False{}:
      (Shut{}, W.put_bool(False{}, W.put_list(~If.Verdict, ~put_verdict, vs, "")))

def open.book(+known: List<&2, Nat>, m: Maybe<&2, List<&2, If.Rule>>) -> St & String:
  match m:
    case None{}:
      (Shut{}, malformed())
    case Some{+rs}:
      +vs = If.verdicts(known, rs)
      open.reply(If.fine_all(vs), rs, vs)

# whole is W.end(rest): nothing is left after the request
def open.end(whole: Bool, known: List<&2, Nat>, xs: List<&2, Nat>) -> St & String:
  match whole:
    case True{}:
      open.book(known, rules(xs))
    case False{}:
      (Shut{}, malformed())

def open.rules(known: List<&2, Nat>, d: W.Dec<List<&2, Nat>>) -> St & String:
  match d:
    case W.Got{xs, s}:
      open.end(W.end(s), known, xs)
    case W.Bad{}:
      (Shut{}, malformed())

def open.known(d: W.Dec<List<&2, Nat>>) -> St & String:
  match d:
    case W.Got{known, s}:
      open.rules(known, W.get_list(~Nat, ~W.get_nat, s))
    case W.Bad{}:
      (Shut{}, malformed())

# open: compile the rulebook; keep it when it compiles
def open(input: String) -> St & String:
  open.known(W.get_list(~Nat, ~W.get_nat, input))

# Step
# ----

def bad_lookup() -> String:
  W.err("quirks: malformed lookup")

def step.ask(+rs: List<&2, If.Rule>, m: Maybe<&2, Ask>) -> St & String:
  match m:
    case None{}:
      (Book{rs}, bad_lookup())
    case Some{a}:
      match a:
        case Ask{q, d}:
          (Book{rs}, put_ans(If.lookup(rs, q, d), ""))

def step.end(whole: Bool, rs: List<&2, If.Rule>, xs: List<&2, Nat>) -> St & String:
  match whole:
    case True{}:
      step.ask(rs, ask(xs))
    case False{}:
      (Book{rs}, bad_lookup())

def step.book(rs: List<&2, If.Rule>, d: W.Dec<List<&2, Nat>>) -> St & String:
  match d:
    case W.Got{xs, s}:
      step.end(W.end(s), rs, xs)
    case W.Bad{}:
      (Book{rs}, bad_lookup())

# step: one lookup in the rulebook
def step(s: St, input: String) -> St & String:
  match s:
    case Book{rs}:
      step.book(rs, W.get_list(~Nat, ~W.get_nat, input))
    case Shut{}:
      (Shut{}, W.err("quirks: no rulebook"))
