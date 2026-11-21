# ffi_undo: the entry of the compiled Bend core for the per-turn workspace
# snapshots (bend/undo.bend; Rust: eukhe-bend rules/undo.rs, called by
# crates/eukhe-core/src/undo). Grammar: crates/eukhe-bend/WIRE.md.
#
#   request  0, live (List<Nat>), base (Nat), event (Nat)   a step
#            1, rows (List<Nat>)                          what /undo does
#            2, rows (List<Nat>)                          what /diff says
#   base     0 none, 1 + t the first turn t
#   event    0 undo, 1 diff the turn, 2 diff all, 3 + t turn t starts
#   rows     three Nats per row: before, now (0 absent, 1 + b blob b), held
#            (0 no, 1 yes)
#   reply    step: the answer (0 took, 1 restore + turn, 2 refused,
#            3 compare + turn, 4 no snapshot), the live turns (List<Nat>),
#            the base (Nat)
#            undo: one Nat per row (0 keep, 1 remove, 2 write)
#            diff: one Nat per row (0 same, 1 differs, 2 skipped)
#
# Malformed input (a row cut short, a held flag past 1, an unknown tag),
# or input left after the request, answers `E undo: malformed request`,
# never a default. Pure: no IO, no @unsafe.

import Base
import ./wire.bend as W
import ./undo.bend as U

# A request of the entry
type Req is Data:
  QStep{st: U.St, ev: U.Ev}
  QFix{rows: List<&2, U.Row>}
  QSeen{rows: List<&2, U.Row>}

# Requests
# --------

# a Nat that may be absent: 0 none, 1 + t some t
def maybe_of(n: Nat) -> Maybe<&2, Nat>:
  match n:
    case 0n:
      None{}
    case 1n+t:
      Some{t}

def ev_of(n: Nat) -> U.Ev:
  match n:
    case 0n:
      U.Undo{}
    case 1n:
      U.Diff{U.Turn{}}
    case 2n:
      U.Diff{U.All{}}
    case 3n+t:
      U.TurnStart{t}

def rows_of.cons(r: U.Row, m: Maybe<&2, List<&2, U.Row>>) -> Maybe<&2, List<&2, U.Row>>:
  match m:
    case None{}:
      None{}
    case Some{rs}:
      Some{r <> rs}

# the rows of a list of Nats, three per row
def rows_of(ns: List<&2, Nat>) -> Maybe<&2, List<&2, U.Row>>:
  match ns:
    case Nil{}:
      Some{Nil{}}
    case Con{b, t1}:
      match t1:
        case Nil{}:
          None{}
        case Con{n, t2}:
          match t2:
            case Nil{}:
              None{}
            case Con{h, t3}:
              match h:
                case 0n:
                  rows_of.cons(U.Row{maybe_of(b), maybe_of(n), False{}}, rows_of(t3))
                case 1n:
                  rows_of.cons(U.Row{maybe_of(b), maybe_of(n), True{}}, rows_of(t3))
                case 2n+x:
                  None{}

def get_req.ev(live: List<&2, Nat>, base: Nat, r: W.Dec<Nat>) -> W.Dec<Req>:
  match r:
    case W.Got{e, s}:
      W.Got{QStep{U.St{live, maybe_of(base)}, ev_of(e)}, s}
    case W.Bad{}:
      W.Bad{}

def get_req.base(live: List<&2, Nat>, r: W.Dec<Nat>) -> W.Dec<Req>:
  match r:
    case W.Got{b, s}:
      get_req.ev(live, b, W.get_nat(s))
    case W.Bad{}:
      W.Bad{}

def get_req.live(r: W.Dec<List<&2, Nat>>) -> W.Dec<Req>:
  match r:
    case W.Got{l, s}:
      get_req.base(l, W.get_nat(s))
    case W.Bad{}:
      W.Bad{}

def get_req.fix(m: Maybe<&2, List<&2, U.Row>>, s: String) -> W.Dec<Req>:
  match m:
    case None{}:
      W.Bad{}
    case Some{rows}:
      W.Got{QFix{rows}, s}

def get_req.fix_rows(r: W.Dec<List<&2, Nat>>) -> W.Dec<Req>:
  match r:
    case W.Got{ns, s}:
      get_req.fix(rows_of(ns), s)
    case W.Bad{}:
      W.Bad{}

def get_req.seen(m: Maybe<&2, List<&2, U.Row>>, s: String) -> W.Dec<Req>:
  match m:
    case None{}:
      W.Bad{}
    case Some{rows}:
      W.Got{QSeen{rows}, s}

def get_req.seen_rows(r: W.Dec<List<&2, Nat>>) -> W.Dec<Req>:
  match r:
    case W.Got{ns, s}:
      get_req.seen(rows_of(ns), s)
    case W.Bad{}:
      W.Bad{}

def get_req.tag(r: W.Dec<Nat>) -> W.Dec<Req>:
  match r:
    case W.Got{t, s}:
      match t:
        case 0n:
          get_req.live(W.get_list(~Nat, ~W.get_nat, s))
        case 1n:
          get_req.fix_rows(W.get_list(~Nat, ~W.get_nat, s))
        case 2n:
          get_req.seen_rows(W.get_list(~Nat, ~W.get_nat, s))
        case 3n+k:
          W.Bad{}
    case W.Bad{}:
      W.Bad{}

# the request at the start of s
def get_req(s: String) -> W.Dec<Req>:
  get_req.tag(W.get_nat(s))

# Replies
# -------

def put_act(a: U.Act, rest: String) -> String:
  match a:
    case U.Took{}:
      W.put_nat(0n, rest)
    case U.Restore{t}:
      W.put_nat(1n, W.put_nat(t, rest))
    case U.Refused{}:
      W.put_nat(2n, rest)
    case U.Compare{t}:
      W.put_nat(3n, W.put_nat(t, rest))
    case U.NoSnapshot{}:
      W.put_nat(4n, rest)

def code_of_maybe(m: Maybe<&2, Nat>) -> Nat:
  match m:
    case None{}:
      0n
    case Some{t}:
      1n+t

def put_step(r: U.St & U.Act) -> String:
  (st, a) = r
  match st:
    case U.St{live, base}:
      put_act(a, W.put_list(~Nat, ~W.put_nat, live, W.put_nat(code_of_maybe(base), "")))

def fix_codes(fs: List<&2, U.Fix>) -> List<&2, Nat>:
  match fs:
    case Nil{}:
      Nil{}
    case Con{f, t}:
      match f:
        case U.Keep{}:
          0n <> fix_codes(t)
        case U.Remove{}:
          1n <> fix_codes(t)
        case U.Write{}:
          2n <> fix_codes(t)

def seen_codes(ss: List<&2, U.Seen>) -> List<&2, Nat>:
  match ss:
    case Nil{}:
      Nil{}
    case Con{x, t}:
      match x:
        case U.Same{}:
          0n <> seen_codes(t)
        case U.Differs{}:
          1n <> seen_codes(t)
        case U.Skipped{}:
          2n <> seen_codes(t)

# The entry
# ---------

# the reply of a request: the model's answer, encoded
def answer(q: Req) -> String:
  match q:
    case QStep{st, ev}:
      put_step(U.step(st, ev))
    case QFix{rows}:
      W.put_list(~Nat, ~W.put_nat, fix_codes(U.fixes(rows)), "")
    case QSeen{rows}:
      W.put_list(~Nat, ~W.put_nat, seen_codes(U.seens(rows)), "")

def ffi.done(q: Req, end: Bool) -> String:
  match end:
    case True{}:
      answer(q)
    case False{}:
      W.err("undo: malformed request")

def ffi.got(r: W.Dec<Req>) -> String:
  match r:
    case W.Got{q, +s}:
      ffi.done(q, W.end(s))
    case W.Bad{}:
      W.err("undo: malformed request")

# the entry: decode the request, answer the model's decision
def ffi(input: String) -> String:
  ffi.got(get_req(input))
