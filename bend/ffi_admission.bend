# ffi_admission: the entry of the compiled Bend core for one provider's
# admission (crates/eukhe-core/src/admission.rs): the live controller's
# state and one op in, the next state out (bend/admission.bend
# `Live.step`). The codec is the wire format of bend/wire.bend:
#
#   request  Live, then Op
#   Live     Lim, q: Nat, ts: List<Lv>, next: Nat
#   Lim      0 (unlimited) | 1, p: Nat (1 + p slots)
#   Lv       k: Nat, Cls, Sts
#   Cls      0 interactive | 1 background
#   Sts      0 queued | 1 granted | 2 held | 3 preempted | 4 ended
#   Op       0 Cls (admit) | 1 k (collect) | 2 k (release) | 3 k (leave)
#            | 4 Lim, q (limits)
#   reply    Live
#
# A malformed request, or one with input left over, answers the wire's
# error form.

import Base
import ./wire.bend as W
import ./admission.bend as M

# Encoders
# --------

def put_cls(c: M.Cls, rest: String) -> String:
  match c:
    case M.Ia{}:
      W.put_nat(0n, rest)
    case M.Bg{}:
      W.put_nat(1n, rest)

def put_sts(s: M.Sts, rest: String) -> String:
  match s:
    case M.Queued{}:
      W.put_nat(0n, rest)
    case M.Granted{}:
      W.put_nat(1n, rest)
    case M.Held{}:
      W.put_nat(2n, rest)
    case M.Preempted{}:
      W.put_nat(3n, rest)
    case M.Ended{}:
      W.put_nat(4n, rest)

def put_lim(l: M.Lim, rest: String) -> String:
  match l:
    case M.Unl{}:
      W.put_nat(0n, rest)
    case M.Cap{p}:
      W.put_nat(1n, W.put_nat(p, rest))

def put_lv(t: M.Lv, rest: String) -> String:
  match t:
    case M.Lv{k, c, s}:
      W.put_nat(k, put_cls(c, put_sts(s, rest)))

def put_live(x: M.Live, rest: String) -> String:
  match x:
    case M.Live{l, q, ts, n}:
      put_lim(l, W.put_nat(q, W.put_list(~M.Lv, ~put_lv, ts, W.put_nat(n, rest))))

def put_op(o: M.Op, rest: String) -> String:
  match o:
    case M.Admit{c}:
      W.put_nat(0n, put_cls(c, rest))
    case M.Collect{k}:
      W.put_nat(1n, W.put_nat(k, rest))
    case M.Release{k}:
      W.put_nat(2n, W.put_nat(k, rest))
    case M.Leave{k}:
      W.put_nat(3n, W.put_nat(k, rest))
    case M.Limit{l, q}:
      W.put_nat(4n, put_lim(l, W.put_nat(q, rest)))

# Decoders
# --------

def get_cls.tag(n: Nat, s: String) -> W.Dec<M.Cls>:
  match n:
    case 0n:
      W.Got{M.Ia{}, s}
    case 1n+m:
      match m:
        case 0n:
          W.Got{M.Bg{}, s}
        case 1n+x:
          W.Bad{}

def get_cls.go(r: W.Dec<Nat>) -> W.Dec<M.Cls>:
  match r:
    case W.Got{n, s}:
      get_cls.tag(n, s)
    case W.Bad{}:
      W.Bad{}

def get_cls(s: String) -> W.Dec<M.Cls>:
  get_cls.go(W.get_nat(s))

def get_sts.tag(n: Nat, s: String) -> W.Dec<M.Sts>:
  match n:
    case 0n:
      W.Got{M.Queued{}, s}
    case 1n+a:
      match a:
        case 0n:
          W.Got{M.Granted{}, s}
        case 1n+b:
          match b:
            case 0n:
              W.Got{M.Held{}, s}
            case 1n+c:
              match c:
                case 0n:
                  W.Got{M.Preempted{}, s}
                case 1n+d:
                  match d:
                    case 0n:
                      W.Got{M.Ended{}, s}
                    case 1n+e:
                      W.Bad{}

def get_sts.go(r: W.Dec<Nat>) -> W.Dec<M.Sts>:
  match r:
    case W.Got{n, s}:
      get_sts.tag(n, s)
    case W.Bad{}:
      W.Bad{}

def get_sts(s: String) -> W.Dec<M.Sts>:
  get_sts.go(W.get_nat(s))

def get_lim.cap(r: W.Dec<Nat>) -> W.Dec<M.Lim>:
  match r:
    case W.Got{p, s}:
      W.Got{M.Cap{p}, s}
    case W.Bad{}:
      W.Bad{}

def get_lim.tag(n: Nat, s: String) -> W.Dec<M.Lim>:
  match n:
    case 0n:
      W.Got{M.Unl{}, s}
    case 1n+m:
      match m:
        case 0n:
          get_lim.cap(W.get_nat(s))
        case 1n+x:
          W.Bad{}

def get_lim.go(r: W.Dec<Nat>) -> W.Dec<M.Lim>:
  match r:
    case W.Got{n, s}:
      get_lim.tag(n, s)
    case W.Bad{}:
      W.Bad{}

def get_lim(s: String) -> W.Dec<M.Lim>:
  get_lim.go(W.get_nat(s))

def get_lv.sts(k: Nat, c: M.Cls, r: W.Dec<M.Sts>) -> W.Dec<M.Lv>:
  match r:
    case W.Got{st, s}:
      W.Got{M.Lv{k, c, st}, s}
    case W.Bad{}:
      W.Bad{}

def get_lv.cls(k: Nat, r: W.Dec<M.Cls>) -> W.Dec<M.Lv>:
  match r:
    case W.Got{c, s}:
      get_lv.sts(k, c, get_sts(s))
    case W.Bad{}:
      W.Bad{}

def get_lv.go(r: W.Dec<Nat>) -> W.Dec<M.Lv>:
  match r:
    case W.Got{k, s}:
      get_lv.cls(k, get_cls(s))
    case W.Bad{}:
      W.Bad{}

def get_lv(s: String) -> W.Dec<M.Lv>:
  get_lv.go(W.get_nat(s))

def get_live.next(l: M.Lim, q: Nat, ts: List<&2, M.Lv>, r: W.Dec<Nat>) -> W.Dec<M.Live>:
  match r:
    case W.Got{n, s}:
      W.Got{M.Live{l, q, ts, n}, s}
    case W.Bad{}:
      W.Bad{}

def get_live.ts(l: M.Lim, q: Nat, r: W.Dec<List<&2, M.Lv>>) -> W.Dec<M.Live>:
  match r:
    case W.Got{ts, s}:
      get_live.next(l, q, ts, W.get_nat(s))
    case W.Bad{}:
      W.Bad{}

def get_live.q(l: M.Lim, r: W.Dec<Nat>) -> W.Dec<M.Live>:
  match r:
    case W.Got{q, s}:
      get_live.ts(l, q, W.get_list(~M.Lv, ~get_lv, s))
    case W.Bad{}:
      W.Bad{}

def get_live.go(r: W.Dec<M.Lim>) -> W.Dec<M.Live>:
  match r:
    case W.Got{l, s}:
      get_live.q(l, W.get_nat(s))
    case W.Bad{}:
      W.Bad{}

def get_live(s: String) -> W.Dec<M.Live>:
  get_live.go(get_lim(s))

def get_op.k(r: W.Dec<Nat>, t: Nat) -> W.Dec<M.Op>:
  match r:
    case W.Got{k, s}:
      match t:
        case 0n:
          W.Got{M.Collect{k}, s}
        case 1n+a:
          match a:
            case 0n:
              W.Got{M.Release{k}, s}
            case 1n+b:
              W.Got{M.Leave{k}, s}
    case W.Bad{}:
      W.Bad{}

def get_op.admit(r: W.Dec<M.Cls>) -> W.Dec<M.Op>:
  match r:
    case W.Got{c, s}:
      W.Got{M.Admit{c}, s}
    case W.Bad{}:
      W.Bad{}

def get_op.q(l: M.Lim, r: W.Dec<Nat>) -> W.Dec<M.Op>:
  match r:
    case W.Got{q, s}:
      W.Got{M.Limit{l, q}, s}
    case W.Bad{}:
      W.Bad{}

def get_op.limit(r: W.Dec<M.Lim>) -> W.Dec<M.Op>:
  match r:
    case W.Got{l, s}:
      get_op.q(l, W.get_nat(s))
    case W.Bad{}:
      W.Bad{}

def get_op.tag(n: Nat, s: String) -> W.Dec<M.Op>:
  match n:
    case 0n:
      get_op.admit(get_cls(s))
    case 1n+a:
      match a:
        case 0n:
          get_op.k(W.get_nat(s), 0n)
        case 1n+b:
          match b:
            case 0n:
              get_op.k(W.get_nat(s), 1n)
            case 1n+c:
              match c:
                case 0n:
                  get_op.k(W.get_nat(s), 2n)
                case 1n+d:
                  match d:
                    case 0n:
                      get_op.limit(get_lim(s))
                    case 1n+e:
                      W.Bad{}

def get_op.go(r: W.Dec<Nat>) -> W.Dec<M.Op>:
  match r:
    case W.Got{n, s}:
      get_op.tag(n, s)
    case W.Bad{}:
      W.Bad{}

def get_op(s: String) -> W.Dec<M.Op>:
  get_op.go(W.get_nat(s))

# The entry
# ---------

def ffi.end(done: Bool, x: M.Live, o: M.Op) -> String:
  match done:
    case True{}:
      put_live(M.Live.step(x, o), "")
    case False{}:
      W.err("admission: input left over")

def ffi.op(x: M.Live, r: W.Dec<M.Op>) -> String:
  match r:
    case W.Got{o, s}:
      ffi.end(W.end(s), x, o)
    case W.Bad{}:
      W.err("admission: malformed op")

def ffi.go(r: W.Dec<M.Live>) -> String:
  match r:
    case W.Got{x, s}:
      ffi.op(x, get_op(s))
    case W.Bad{}:
      W.err("admission: malformed state")

# One op of the live controller: the state and the op in, the next state
# out.
def ffi(input: String) -> String:
  ffi.go(get_live(input))
