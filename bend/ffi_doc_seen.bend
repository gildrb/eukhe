# ffi_doc_seen: the entry of the compiled Bend core for the seen-line
# guard (bend/doc_seen.bend `check`; Rust: crates/eukhe-docs
# hashline/seen.rs). Pure: no IO, no @unsafe, no foreign effect.
#
# Request (a record): the seen runs, then the anchors
#   seen   List<Iv>   Iv = lo: Nat, hi: Nat
#   ats    List<At>   At = line: Nat, width: Maybe<Nat>
# Reply (a record, M.Check):
#   unseen List<Nat>
#   shown  List<Show> Show = line: Nat, cut: Maybe<Nat>
#   whole  Bool
# A malformed request, or one with input left over, answers the wire
# error form.

import Base
import ./wire.bend as W
import ./doc_seen.bend as M

# Maybe<Nat>
# ----------

def put_mnat(m: Maybe<&2, Nat>, rest: String) -> String:
  match m:
    case None{}:
      W.put_nat(0n, rest)
    case Some{x}:
      W.put_nat(1n, W.put_nat(x, rest))

def get_mnat.some(r: W.Dec<Nat>) -> W.Dec<Maybe<&2, Nat>>:
  match r:
    case W.Got{x, s}:
      W.Got{Some{x}, s}
    case W.Bad{}:
      W.Bad{}

def get_mnat.tag(r: W.Dec<Nat>) -> W.Dec<Maybe<&2, Nat>>:
  match r:
    case W.Got{t, s}:
      match t:
        case 0n:
          W.Got{None{}, s}
        case 1n:
          get_mnat.some(W.get_nat(s))
        case 2n+p:
          W.Bad{}
    case W.Bad{}:
      W.Bad{}

def get_mnat(s: String) -> W.Dec<Maybe<&2, Nat>>:
  get_mnat.tag(W.get_nat(s))

# Iv
# --

def put_iv(iv: M.Iv, rest: String) -> String:
  match iv:
    case M.Iv{lo, hi}:
      W.put_nat(lo, W.put_nat(hi, rest))

def get_iv.hi(lo: Nat, r: W.Dec<Nat>) -> W.Dec<M.Iv>:
  match r:
    case W.Got{hi, s}:
      W.Got{M.Iv{lo, hi}, s}
    case W.Bad{}:
      W.Bad{}

def get_iv.lo(r: W.Dec<Nat>) -> W.Dec<M.Iv>:
  match r:
    case W.Got{lo, s}:
      get_iv.hi(lo, W.get_nat(s))
    case W.Bad{}:
      W.Bad{}

def get_iv(s: String) -> W.Dec<M.Iv>:
  get_iv.lo(W.get_nat(s))

# At
# --

def put_at(a: M.At, rest: String) -> String:
  match a:
    case M.At{n, w}:
      W.put_nat(n, put_mnat(w, rest))

def get_at.w(n: Nat, r: W.Dec<Maybe<&2, Nat>>) -> W.Dec<M.At>:
  match r:
    case W.Got{w, s}:
      W.Got{M.At{n, w}, s}
    case W.Bad{}:
      W.Bad{}

def get_at.n(r: W.Dec<Nat>) -> W.Dec<M.At>:
  match r:
    case W.Got{n, s}:
      get_at.w(n, get_mnat(s))
    case W.Bad{}:
      W.Bad{}

def get_at(s: String) -> W.Dec<M.At>:
  get_at.n(W.get_nat(s))

# Show and Check (the reply)
# --------------------------

def put_show(x: M.Show, rest: String) -> String:
  match x:
    case M.Show{n, c}:
      W.put_nat(n, put_mnat(c, rest))

def put_check(c: M.Check, rest: String) -> String:
  match c:
    case M.Check{u, s, w}:
      W.put_list(~Nat, ~W.put_nat, u, W.put_list(~M.Show, ~put_show, s, W.put_bool(w, rest)))

# The request
# -----------

# the encoding of a request (what Rust writes; the laws read it back)
def put_req(seen: List<&2, M.Iv>, ats: List<&2, M.At>, rest: String) -> String:
  W.put_list(~M.Iv, ~put_iv, seen, W.put_list(~M.At, ~put_at, ats, rest))

def run.done(seen: List<&2, M.Iv>, ats: List<&2, M.At>, done: Bool) -> String:
  match done:
    case True{}:
      put_check(M.check(seen, ats), "")
    case False{}:
      W.err("doc_seen: input left over")

def run.ats(seen: List<&2, M.Iv>, r: W.Dec<List<&2, M.At>>) -> String:
  match r:
    case W.Got{ats, s}:
      run.done(seen, ats, W.end(s))
    case W.Bad{}:
      W.err("doc_seen: malformed anchors")

def run.seen(r: W.Dec<List<&2, M.Iv>>) -> String:
  match r:
    case W.Got{seen, s}:
      run.ats(seen, W.get_list(~M.At, ~get_at, s))
    case W.Bad{}:
      W.err("doc_seen: malformed seen runs")

# the entry: a request in, the guard's verdict out
def ffi(input: String) -> String:
  run.seen(W.get_list(~M.Iv, ~get_iv, input))
