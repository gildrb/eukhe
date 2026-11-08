import Base
import ./wire.bend as W
import ./compactor.bend as C

# ffi_compactor: the compactor's decisions (bend/compactor.bend `line.open`,
# `line.step`, `Pend.after`; spec/README.md M2) as an entry of the
# compiled Bend core. Rust keeps the texts (the replies, the best one, the
# node's input) and sends their lengths in UTF-8 bytes; the model decides.
# Request: a tag, then
#   0  a line opens: the tries it has
#   1  a reply of a line: the tries left, the calls made, the node's size
#      in bytes, the length of the shortest reply so far (Maybe: none
#      before the first), then the reply: 0 a provider error | 1 a text
#      (thinking dropped, trimmed) of that many bytes
#   2  a call of a pending line ended: the line (0 built | 1 owed, then
#      the failures it has left), then how: 0 its line was saved, 1 the
#      call failed, 2 the disk failed, 3 a waiting turn stopped it
# Reply to 0 and 1: 0 the line ends, then the calls made and how (0 the
# reply whole, 1 the reply cut to the node, 2 the shortest reply before it
# cut so, 3 the input cut so, 4 the call failed) | 1 the next call goes,
# then the tries left, the calls made and the shortest reply's length
# (Maybe). Reply to 2: the line (0 built | 1 owed, then the failures
# left). Any other input: the error form.

# A request of the entry
type Req is Data:
  QOpen{tries: Nat}
  QStep{left: Nat, made: Nat, node: Nat, bl: Maybe<&2, Nat>, r: Rep}
  QAfter{p: C.Pend, o: C.Outcome}

# a reply of the model, by its length
type Rep is Data:
  RErr{}
  RSays{len: Nat}

# Decoding
# --------

def get_mnat.some(r: W.Dec<Nat>) -> W.Dec<Maybe<&2, Nat>>:
  match r:
    case W.Got{n, s}:
      W.Got{Some{n}, s}
    case W.Bad{}:
      W.Bad{}

def get_mnat.tag(t: Nat, s: String) -> W.Dec<Maybe<&2, Nat>>:
  match t:
    case 0n:
      W.Got{None{}, s}
    case 1n:
      get_mnat.some(W.get_nat(s))
    case 2n+p:
      W.Bad{}

def get_mnat(r: W.Dec<Nat>) -> W.Dec<Maybe<&2, Nat>>:
  match r:
    case W.Got{t, s}:
      get_mnat.tag(t, s)
    case W.Bad{}:
      W.Bad{}

def get_open(r: W.Dec<Nat>) -> W.Dec<Req>:
  match r:
    case W.Got{t, s}:
      W.Got{QOpen{t}, s}
    case W.Bad{}:
      W.Bad{}

def get_step.says(l: Nat, m: Nat, n: Nat, b: Maybe<&2, Nat>, r: W.Dec<Nat>) -> W.Dec<Req>:
  match r:
    case W.Got{len, s}:
      W.Got{QStep{l, m, n, b, RSays{len}}, s}
    case W.Bad{}:
      W.Bad{}

def get_step.rep(l: Nat, m: Nat, n: Nat, b: Maybe<&2, Nat>, t: Nat, s: String) -> W.Dec<Req>:
  match t:
    case 0n:
      W.Got{QStep{l, m, n, b, RErr{}}, s}
    case 1n:
      get_step.says(l, m, n, b, W.get_nat(s))
    case 2n+p:
      W.Bad{}

def get_step.tag(l: Nat, m: Nat, n: Nat, b: Maybe<&2, Nat>, r: W.Dec<Nat>) -> W.Dec<Req>:
  match r:
    case W.Got{t, s}:
      get_step.rep(l, m, n, b, t, s)
    case W.Bad{}:
      W.Bad{}

def get_step.kind(l: Nat, m: Nat, n: Nat, r: W.Dec<Maybe<&2, Nat>>) -> W.Dec<Req>:
  match r:
    case W.Got{b, s}:
      get_step.tag(l, m, n, b, W.get_nat(s))
    case W.Bad{}:
      W.Bad{}

def get_step.node(l: Nat, m: Nat, r: W.Dec<Nat>) -> W.Dec<Req>:
  match r:
    case W.Got{n, s}:
      get_step.kind(l, m, n, get_mnat(W.get_nat(s)))
    case W.Bad{}:
      W.Bad{}

def get_step.made(l: Nat, r: W.Dec<Nat>) -> W.Dec<Req>:
  match r:
    case W.Got{m, s}:
      get_step.node(l, m, W.get_nat(s))
    case W.Bad{}:
      W.Bad{}

def get_step(r: W.Dec<Nat>) -> W.Dec<Req>:
  match r:
    case W.Got{l, s}:
      get_step.made(l, W.get_nat(s))
    case W.Bad{}:
      W.Bad{}

def get_outcome(p: C.Pend, t: Nat, s: String) -> W.Dec<Req>:
  match t:
    case 0n:
      W.Got{QAfter{p, C.Built{}}, s}
    case 1n:
      W.Got{QAfter{p, C.Failed{}}, s}
    case 2n:
      W.Got{QAfter{p, C.Disk{}}, s}
    case 3n:
      W.Got{QAfter{p, C.Stopped{}}, s}
    case 4n+q:
      W.Bad{}

def get_after.how(p: C.Pend, r: W.Dec<Nat>) -> W.Dec<Req>:
  match r:
    case W.Got{t, s}:
      get_outcome(p, t, s)
    case W.Bad{}:
      W.Bad{}

def get_after.owed(r: W.Dec<Nat>) -> W.Dec<Req>:
  match r:
    case W.Got{n, s}:
      get_after.how(C.Owed{n}, W.get_nat(s))
    case W.Bad{}:
      W.Bad{}

def get_after.tag(t: Nat, s: String) -> W.Dec<Req>:
  match t:
    case 0n:
      get_after.how(C.Made{}, W.get_nat(s))
    case 1n:
      get_after.owed(W.get_nat(s))
    case 2n+p:
      W.Bad{}

def get_after(r: W.Dec<Nat>) -> W.Dec<Req>:
  match r:
    case W.Got{t, s}:
      get_after.tag(t, s)
    case W.Bad{}:
      W.Bad{}

def get_req.tag(t: Nat, s: String) -> W.Dec<Req>:
  match t:
    case 0n:
      get_open(W.get_nat(s))
    case 1n:
      get_step(W.get_nat(s))
    case 2n:
      get_after(W.get_nat(s))
    case 3n+p:
      W.Bad{}

def get_req.go(r: W.Dec<Nat>) -> W.Dec<Req>:
  match r:
    case W.Got{t, s}:
      get_req.tag(t, s)
    case W.Bad{}:
      W.Bad{}

# the request at the start of s
def get_req(s: String) -> W.Dec<Req>:
  get_req.go(W.get_nat(s))

# Encoding
# --------

def put_fin(e: C.Fin, rest: String) -> String:
  match e:
    case C.Whole{t}:
      W.put_nat(0n, rest)
    case C.CutReply{t}:
      W.put_nat(1n, rest)
    case C.CutBest{t}:
      W.put_nat(2n, rest)
    case C.CutInput{t}:
      W.put_nat(3n, rest)
    case C.Lost{}:
      W.put_nat(4n, rest)

def put_best(b: Maybe<&2, List<&2, C.W>>, bl: Nat, rest: String) -> String:
  match b:
    case None{}:
      W.put_nat(0n, rest)
    case Some{t}:
      W.put_nat(1n, W.put_nat(bl, rest))

def put_next(n: C.Next) -> String:
  match n:
    case C.Ends{c, e}:
      W.put_nat(0n, W.put_nat(c, put_fin(e, "")))
    case C.Asks{st}:
      match st:
        case C.Lst{l, m, node, b, bl, i}:
          W.put_nat(1n, W.put_nat(l, W.put_nat(m, put_best(b, bl, ""))))

def put_pend(p: C.Pend) -> String:
  match p:
    case C.Made{}:
      W.put_nat(0n, "")
    case C.Owed{n}:
      W.put_nat(1n, W.put_nat(n, ""))

# The decisions
# -------------

# the shortest reply so far as the model holds it: the texts stay in Rust,
# so the model sees an empty one of the length Rust sent
def best.of(m: Maybe<&2, Nat>) -> Maybe<&2, List<&2, C.W>>:
  match m:
    case None{}:
      None{}
    case Some{n}:
      Some{Nil{}}

def best.len(m: Maybe<&2, Nat>) -> Nat:
  match m:
    case None{}:
      0n
    case Some{n}:
      n

# a reply of len bytes to a line with 1+p tries left (line.step)
def reply.says(len: Nat, p: Nat, made: Nat, +node: Nat, +bl: Maybe<&2, Nat>) -> C.Next:
  match len:
    case 0n:
      C.Ends{1n+made, C.end.of(best.of(bl), Nil{})}
    case 1n+k:
      +n = {1n+k : Nat}
      +b = best.of(bl)
      C.line.says(Nat.is_le(n, node), C.shorter(n, b, best.len(bl)), p, made, node, b, Nil{}, Nil{}, n)

def reply(left: Nat, made: Nat, +node: Nat, +bl: Maybe<&2, Nat>, r: Rep) -> C.Next:
  match left:
    case 0n:
      C.Ends{made, C.end.of(best.of(bl), Nil{})}
    case 1n+p:
      match r:
        case RErr{}:
          C.Ends{1n+made, C.Lost{}}
        case RSays{len}:
          reply.says(len, p, made, node, bl)

# the answer to a request
def answer(q: Req) -> String:
  match q:
    case QOpen{t}:
      put_next(C.line.open(t, 0n, Nil{}))
    case QStep{l, m, n, b, r}:
      put_next(reply(l, m, n, b, r))
    case QAfter{p, o}:
      put_pend(C.Pend.after(p, o))

def fail() -> String:
  W.err("compactor: malformed request")

def run.end(whole: Bool, q: Req) -> String:
  match whole:
    case True{}:
      answer(q)
    case False{}:
      fail()

def run(r: W.Dec<Req>) -> String:
  match r:
    case W.Got{q, s}:
      run.end(W.end(s), q)
    case W.Bad{}:
      fail()

def ffi(input: String) -> String:
  run(get_req(input))
