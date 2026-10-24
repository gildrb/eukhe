# ffi_doc_lines: the entry of the compiled Bend core for the line endings
# of a file (bend/doc_lines.bend `plan`, `carry`, `write`; Rust:
# crates/eukhe-docs hashline/endings.rs, text.rs). Pure: no IO, no
# @unsafe, no foreign effect.
#
# Three requests:
#   plan   runs: List<Run>, carry: End      Run = end: Maybe<End>, n: Nat
#          reply: List<Seps>                Seps = end: End, n: Nat
#   `L` then a projection                   (the carry of a loaded file)
#          reply: End
#   `W` then two projections                (a whole-file write: the file
#          reply: bom: Bool, sep: End,       on disk, then the content)
#                 warn: Bool
# End = Lf (tag 0) | CrLf (tag 1); Maybe<End> = 0 | 1 then the End.
# A projection is bom: Bool, then List<Line>, Line = len: Nat, end:
# Maybe<End>. A plan request starts with a digit (its count), so the
# entry reads it first; an input that is no plan is read as `L` or `W`.
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

# Projections
# -----------

def get_line.end(n: Nat, r: W.Dec<Maybe<&2, M.End>>) -> W.Dec<M.Line>:
  match r:
    case W.Got{o, s}:
      W.Got{M.Line{n, o}, s}
    case W.Bad{}:
      W.Bad{}

def get_line.len(r: W.Dec<Nat>) -> W.Dec<M.Line>:
  match r:
    case W.Got{n, s}:
      get_line.end(n, get_mend(s))
    case W.Bad{}:
      W.Bad{}

def get_line(s: String) -> W.Dec<M.Line>:
  get_line.len(W.get_nat(s))

def get_proj.lines(b: Bool, r: W.Dec<List<&2, M.Line>>) -> W.Dec<M.Proj>:
  match r:
    case W.Got{ls, s}:
      W.Got{M.Proj{b, ls}, s}
    case W.Bad{}:
      W.Bad{}

def get_proj.bom(r: W.Dec<Bool>) -> W.Dec<M.Proj>:
  match r:
    case W.Got{b, s}:
      get_proj.lines(b, W.get_list(~M.Line, ~get_line, s))
    case W.Bad{}:
      W.Bad{}

def get_proj(s: String) -> W.Dec<M.Proj>:
  get_proj.bom(W.get_bool(s))

def put_kept(k: M.Kept) -> String:
  match k:
    case M.Kept{b, e, w}:
      W.put_bool(b, put_end(e, W.put_bool(w, "")))

# The requests
# ------------

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

def load.done(p: M.Proj, done: Bool) -> String:
  match done:
    case True{}:
      put_end(M.carry(p), "")
    case False{}:
      W.err("doc_lines: input left over")

def load.run(r: W.Dec<M.Proj>) -> String:
  match r:
    case W.Got{p, s}:
      load.done(p, W.end(s))
    case W.Bad{}:
      W.err("doc_lines: malformed projection")

def write.done(p: M.Proj, q: M.Proj, done: Bool) -> String:
  match done:
    case True{}:
      put_kept(M.write(p, q))
    case False{}:
      W.err("doc_lines: input left over")

def write.next(p: M.Proj, r: W.Dec<M.Proj>) -> String:
  match r:
    case W.Got{q, s}:
      write.done(p, q, W.end(s))
    case W.Bad{}:
      W.err("doc_lines: malformed projection")

def write.run(r: W.Dec<M.Proj>) -> String:
  match r:
    case W.Got{p, s}:
      write.next(p, get_proj(s))
    case W.Bad{}:
      W.err("doc_lines: malformed projection")

def kind.pick(l: Bool, w: Bool, t: String) -> String:
  match l:
    case True{}:
      load.run(get_proj(t))
    case False{}:
      match w:
        case True{}:
          write.run(get_proj(t))
        case False{}:
          W.err("doc_lines: malformed runs")

# an input that is no plan: `L` (76) or `W` (87), then its projections
def kind(input: String) -> String:
  match input:
    case SNil{}:
      W.err("doc_lines: malformed runs")
    case SCon{c, t}:
      match c:
        case Chr{+x}:
          kind.pick(U32.is_eq(x, 76), U32.is_eq(x, 87), t)

def run.runs(r: W.Dec<List<&2, M.Run>>, input: String) -> String:
  match r:
    case W.Got{rs, s}:
      run.carry(rs, get_end(s))
    case W.Bad{}:
      kind(input)

# the entry: a plan (runs of line endings and the first carry in, the
# separators out), or the carry of a projection, or a write's decision
def ffi(+input: String) -> String:
  run.runs(W.get_list(~M.Run, ~get_run, input), input)
