# ffi_doc_lines: the entry of the compiled Bend core for the separators an
# edited file persists with (bend/doc_lines.bend `plan`; Rust:
# crates/eukhe-docs hashline/endings.rs). Pure: no IO, no @unsafe, no
# foreign effect.
#
# Request (a record):
#   runs   List<Run>  Run = end: Maybe<End>, n: Nat
#   carry  End        End = Lf (tag 0) | CrLf (tag 1)
# Reply: List<Seps>   Seps = end: End, n: Nat
# A malformed request, or one with input left over, answers the wire
# error form.

import Base
import ./wire.bend as W
import ./doc_lines.bend as M

# End
# ---

def put_end(e: M.End, rest: String) -> String:
  match e:
    case M.Lf{}:
      W.put_nat(0n, rest)
    case M.CrLf{}:
      W.put_nat(1n, rest)

def get_end.tag(r: W.Dec<Nat>) -> W.Dec<M.End>:
  match r:
    case W.Got{t, s}:
      match t:
        case 0n:
          W.Got{M.Lf{}, s}
        case 1n:
          W.Got{M.CrLf{}, s}
        case 2n+p:
          W.Bad{}
    case W.Bad{}:
      W.Bad{}

def get_end(s: String) -> W.Dec<M.End>:
  get_end.tag(W.get_nat(s))

# Maybe<End>
# ----------

def put_mend(m: Maybe<&2, M.End>, rest: String) -> String:
  match m:
    case None{}:
      W.put_nat(0n, rest)
    case Some{e}:
      W.put_nat(1n, put_end(e, rest))

def get_mend.some(r: W.Dec<M.End>) -> W.Dec<Maybe<&2, M.End>>:
  match r:
    case W.Got{e, s}:
      W.Got{Some{e}, s}
    case W.Bad{}:
      W.Bad{}

def get_mend.tag(r: W.Dec<Nat>) -> W.Dec<Maybe<&2, M.End>>:
  match r:
    case W.Got{t, s}:
      match t:
        case 0n:
          W.Got{None{}, s}
        case 1n:
          get_mend.some(get_end(s))
        case 2n+p:
          W.Bad{}
    case W.Bad{}:
      W.Bad{}

def get_mend(s: String) -> W.Dec<Maybe<&2, M.End>>:
  get_mend.tag(W.get_nat(s))

# Run and Seps
# ------------

def get_run.n(o: Maybe<&2, M.End>, r: W.Dec<Nat>) -> W.Dec<M.Run>:
  match r:
    case W.Got{n, s}:
      W.Got{M.Run{o, n}, s}
    case W.Bad{}:
      W.Bad{}

def get_run.end(r: W.Dec<Maybe<&2, M.End>>) -> W.Dec<M.Run>:
  match r:
    case W.Got{o, s}:
      get_run.n(o, W.get_nat(s))
    case W.Bad{}:
      W.Bad{}

def put_run(r: M.Run, rest: String) -> String:
  match r:
    case M.Run{o, n}:
      put_mend(o, W.put_nat(n, rest))

def get_run(s: String) -> W.Dec<M.Run>:
  get_run.end(get_mend(s))

def put_seps(x: M.Seps, rest: String) -> String:
  match x:
    case M.Seps{e, n}:
      put_end(e, W.put_nat(n, rest))

# the encoding of a request (what Rust writes; the laws read it back)
def put_req(rs: List<&2, M.Run>, c: M.End, rest: String) -> String:
  W.put_list(~M.Run, ~put_run, rs, put_end(c, rest))

# The request
# -----------

def run.done(rs: List<&2, M.Run>, c: M.End, done: Bool) -> String:
  match done:
    case True{}:
      W.put_list(~M.Seps, ~put_seps, M.plan(rs, c), "")
    case False{}:
      W.err("doc_lines: input left over")

def run.carry(rs: List<&2, M.Run>, r: W.Dec<M.End>) -> String:
  match r:
    case W.Got{c, s}:
      run.done(rs, c, W.end(s))
    case W.Bad{}:
      W.err("doc_lines: malformed carry")

def run.runs(r: W.Dec<List<&2, M.Run>>) -> String:
  match r:
    case W.Got{rs, s}:
      run.carry(rs, get_end(s))
    case W.Bad{}:
      W.err("doc_lines: malformed runs")

# the entry: runs of line endings and the first carry in, the separators out
def ffi(input: String) -> String:
  run.runs(W.get_list(~M.Run, ~get_run, input))
