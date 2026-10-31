# ffi_rebase: the entry of the compiled Bend core for the three-way rebase
# of a stale edit (bend/rebase.bend; Rust: eukhe-bend rules/rebase.rs).
# Grammar: crates/eukhe-bend/WIRE.md.
#
#   request  the base's line ids, the head's line ids, the edits against
#            the base (List<Nat> each); the edits are flat: for each edit
#            its start, its end, the count of its lines, then their ids
#   reply    0, the edits against the head (List<Nat>, flat the same way)
#            | 1, the refusal: its tag (0 Invalid | 1 Moved | 2 Ambiguous |
#            3 Crossed, then the edit's index, a Nat | 4 TooLarge)
#
# The work bound: an input whose edits times its lines (the base's and the
# head's) pass work_max() answers TooLarge, before any scan.
# Malformed input (an edit cut short, a count past the ids left), or input
# left after the request, answers `E rebase: malformed request`, never a
# default.
# Pure: no IO, no @unsafe.

import Base
import ./wire.bend as W
import ./rebase.bend as R

# A request of the entry: the base, the head, the flat edits
type Req is Data:
  Req{base: List<&2, Nat>, head: List<&2, Nat>, edits: List<&2, Nat>}

# The first ids of a flat list and the ids after them
type Cut is Data:
  Cut{taken: List<&2, Nat>, rest: List<&2, Nat>}

# the most edits times lines one rebase scans
def work_max() -> Nat:
  1048576n

# Requests
# --------

def get_req.edits(b: List<&2, Nat>, h: List<&2, Nat>, x: W.Dec<List<&2, Nat>>) -> W.Dec<Req>:
  match x:
    case W.Got{es, s}:
      W.Got{Req{b, h, es}, s}
    case W.Bad{}:
      W.Bad{}

def get_req.head(b: List<&2, Nat>, x: W.Dec<List<&2, Nat>>) -> W.Dec<Req>:
  match x:
    case W.Got{h, s}:
      get_req.edits(b, h, W.get_list(~Nat, ~W.get_nat, s))
    case W.Bad{}:
      W.Bad{}

def get_req.base(x: W.Dec<List<&2, Nat>>) -> W.Dec<Req>:
  match x:
    case W.Got{b, s}:
      get_req.head(b, W.get_list(~Nat, ~W.get_nat, s))
    case W.Bad{}:
      W.Bad{}

# the request at the start of s
def get_req(s: String) -> W.Dec<Req>:
  get_req.base(W.get_list(~Nat, ~W.get_nat, s))

# Flat edits
# ----------

# the edits, flat: start, end, the count of lines, the lines
def flat(es: List<&2, R.Edit>) -> List<&2, Nat>:
  match es:
    case Nil{}:
      Nil{}
    case Con{e, rest}:
      match e:
        case R.Edit{s, t, +ls}:
          s <> (t <> (List.length(&2, Nat, ls) <> List.append(&2, Nat, ls, flat(rest))))

def split.cons(+x: Nat, m: Maybe<&2, Cut>) -> Maybe<&2, Cut>:
  match m:
    case None{}:
      None{}
    case Some{c}:
      match c:
        case Cut{ls, rest}:
          Some{Cut{x <> ls, rest}}

# the first n ids of xs and the ids after them; none when xs has fewer
def split(n: Nat, xs: List<&2, Nat>) -> Maybe<&2, Cut>:
  match n xs:
    case 0n _:
      Some{Cut{Nil{}, xs}}
    case 1n+p Nil{}:
      None{}
    case 1n+p Con{x, t}:
      split.cons(x, split(p, t))

def unflat.cons(e: R.Edit, m: Maybe<&2, List<&2, R.Edit>>) -> Maybe<&2, List<&2, R.Edit>>:
  match m:
    case None{}:
      None{}
    case Some{es}:
      Some{e <> es}

def unflat.at(+s: Nat, +t: Nat, m: Maybe<&2, Cut>, go: List<&2, Nat> -> Maybe<&2, List<&2, R.Edit>>) -> Maybe<&2, List<&2, R.Edit>>:
  match m:
    case None{}:
      None{}
    case Some{c}:
      match c:
        case Cut{ls, rest}:
          unflat.cons(R.Edit{s, t, ls}, go(rest))

# the flat edits xs read back, with fuel edits at most; none when they are
# cut short or the fuel ends first
def unflat(f: Nat, xs: List<&2, Nat>) -> Maybe<&2, List<&2, R.Edit>>:
  match f xs:
    case _ Nil{}:
      Some{Nil{}}
    case 0n Con{x, xt}:
      None{}
    case 1n+p Con{s, r1}:
      match r1:
        case Nil{}:
          None{}
        case Con{t, r2}:
          match r2:
            case Nil{}:
              None{}
            case Con{n, r3}:
              unflat.at(s, t, split(n, r3), rest => unflat(p, rest))

# Replies
# -------

def put_why(w: R.Why, rest: String) -> String:
  match w:
    case R.Invalid{i}:
      W.put_nat(0n, W.put_nat(i, rest))
    case R.Moved{i}:
      W.put_nat(1n, W.put_nat(i, rest))
    case R.Ambiguous{i}:
      W.put_nat(2n, W.put_nat(i, rest))
    case R.Crossed{i}:
      W.put_nat(3n, W.put_nat(i, rest))
    case R.TooLarge{}:
      W.put_nat(4n, rest)

def put_outcome(o: R.Outcome) -> String:
  match o:
    case R.Rebased{fs}:
      W.put_nat(0n, W.put_list(~Nat, ~W.put_nat, flat(fs), ""))
    case R.Conflict{w}:
      W.put_nat(1n, put_why(w, ""))

def bounded.at(ok: Bool, +b: List<&2, Nat>, +h: List<&2, Nat>, +es: List<&2, R.Edit>) -> R.Outcome:
  match ok:
    case True{}:
      R.rebase(b, h, es)
    case False{}:
      R.Conflict{R.TooLarge{}}

# the rebase within the work bound: the edits times the lines of the base
# and the head at most work_max(), else TooLarge
def bounded(+b: List<&2, Nat>, +h: List<&2, Nat>, +es: List<&2, R.Edit>) -> R.Outcome:
  bounded.at(Nat.is_le(Nat.mul(List.length(&2, R.Edit, es), Nat.add(List.length(&2, Nat, b), List.length(&2, Nat, h))), work_max()), b, h, es)

def answer.of(m: Maybe<&2, List<&2, R.Edit>>, +b: List<&2, Nat>, +h: List<&2, Nat>) -> String:
  match m:
    case None{}:
      W.err("rebase: malformed request")
    case Some{es}:
      put_outcome(bounded(b, h, es))

# the reply of a request: the model's answer, encoded
def answer(q: Req) -> String:
  match q:
    case Req{+b, +h, +xs}:
      answer.of(unflat(List.length(&2, Nat, xs), xs), b, h)

def ffi.done(q: Req, end: Bool) -> String:
  match end:
    case True{}:
      answer(q)
    case False{}:
      W.err("rebase: malformed request")

def ffi.got(r: W.Dec<Req>) -> String:
  match r:
    case W.Got{q, +s}:
      ffi.done(q, W.end(s))
    case W.Bad{}:
      W.err("rebase: malformed request")

# the entry: decode the request, answer the model's decision
def ffi(input: String) -> String:
  ffi.got(get_req(input))
