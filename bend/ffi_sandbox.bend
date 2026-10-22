import Base
import ./wire.bend as W
import ./sandbox.bend as M

# ffi_sandbox: the hand-back's plan of one path (bend/sandbox.bend `plan`)
# as an entry of the compiled Bend core. The request is the path's three
# contents, the parent's, the base's and the child's, each as a
# Maybe<Nat> (None: no file; equal contents are equal ids). The reply is
# the Plan: its tag (Keep 0, Clash 1, Take 2, Drop 3), then Keep's taken.

def put_doc(m: Maybe<&2, Nat>, rest: String) -> String:
  match m:
    case None{}:
      W.put_nat(0n, rest)
    case Some{x}:
      W.put_nat(1n, W.put_nat(x, rest))

def get_doc.some(r: W.Dec<Nat>) -> W.Dec<Maybe<&2, Nat>>:
  match r:
    case W.Got{x, s}:
      W.Got{Some{x}, s}
    case W.Bad{}:
      W.Bad{}

def get_doc.tag(t: Nat, s: String) -> W.Dec<Maybe<&2, Nat>>:
  match t:
    case 0n:
      W.Got{None{}, s}
    case 1n+p:
      match p:
        case 0n:
          get_doc.some(W.get_nat(s))
        case 1n+q:
          W.Bad{}

def get_doc.go(r: W.Dec<Nat>) -> W.Dec<Maybe<&2, Nat>>:
  match r:
    case W.Got{t, s}:
      get_doc.tag(t, s)
    case W.Bad{}:
      W.Bad{}

def get_doc(s: String) -> W.Dec<Maybe<&2, Nat>>:
  get_doc.go(W.get_nat(s))

# the request
def put_req(p: Maybe<&2, Nat>, b: Maybe<&2, Nat>, c: Maybe<&2, Nat>) -> String:
  put_doc(p, put_doc(b, put_doc(c, "")))

def put_plan(x: M.Plan, rest: String) -> String:
  match x:
    case M.Keep{t}:
      W.put_nat(0n, W.put_bool(t, rest))
    case M.Clash{}:
      W.put_nat(1n, rest)
    case M.Take{}:
      W.put_nat(2n, rest)
    case M.Drop{}:
      W.put_nat(3n, rest)

def run.end(left: Bool, +p: Maybe<&2, Nat>, +b: Maybe<&2, Nat>, +c: Maybe<&2, Nat>) -> String:
  match left:
    case True{}:
      put_plan(M.plan(p, b, c), "")
    case False{}:
      W.err("sandbox: input left over")

def run.c(+p: Maybe<&2, Nat>, +b: Maybe<&2, Nat>, r: W.Dec<Maybe<&2, Nat>>) -> String:
  match r:
    case W.Got{+c, s}:
      run.end(W.end(s), p, b, c)
    case W.Bad{}:
      W.err("sandbox: bad child content")

def run.b(+p: Maybe<&2, Nat>, r: W.Dec<Maybe<&2, Nat>>) -> String:
  match r:
    case W.Got{+b, s}:
      run.c(p, b, get_doc(s))
    case W.Bad{}:
      W.err("sandbox: bad base content")

def run.p(r: W.Dec<Maybe<&2, Nat>>) -> String:
  match r:
    case W.Got{+p, s}:
      run.b(p, get_doc(s))
    case W.Bad{}:
      W.err("sandbox: bad parent content")

# the entry
def ffi(input: String) -> String:
  run.p(get_doc(input))
