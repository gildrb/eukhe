# eukhe: the proof of LAW infer_force_steps
# Induction on the replies, generalized over the attempt i, with the
# retries written i + q (q retries left): a miss on attempt i retries
# exactly when q > 0, and the next attempt has i + 1 and q - 1, the same
# sum (Nat.add_succ). A retry's flag is the provider's support, as in
# force.go.

import Base
import ../../bend/infer.bend as If
import ../../bend/infer_force.bend as M
import ../../laws/infer_force.bend as InferForce
import ../base/nat.bend as LNat

# no retry is left at i + 0
def ifs.lt0(i: Nat) -> {Nat.is_lt(i, Nat.add(i, 0n)) == False{} : Bool}:
  match i:
    case 0n:
      {==}
    case 1n+p:
      ifs.lt0(p)

# a retry is left at i + (1 + q)
def ifs.lt_s(i: Nat, -q: Nat) -> {Nat.is_lt(i, Nat.add(i, 1n+q)) == True{} : Bool}:
  match i:
    case 0n:
      {==}
    case 1n+p:
      ifs.lt_s(p, q)

# a miss with no retry left fails the call
def ifs.fails(-more: Bool, -f: Bool, -X: List<&2, If.Try> & If.Forced, e: {more == False{} : Bool}) -> {InferForce.drive.next(M.after.miss(more), f, X) == ([If.Try{f}], If.Missed{}) : List<&2, If.Try> & If.Forced}:
  %Equal.sym(Bool, more, False{}, e) : {InferForce.drive.next(M.after.miss(_), f, X) == ([If.Try{f}], If.Missed{}) : List<&2, If.Try> & If.Forced}
  {==}

def ifs.again(-f: Bool, X: List<&2, If.Try> & If.Forced) -> {InferForce.drive.next(M.Again{}, f, X) == If.force.next(If.Try{f}, X) : List<&2, If.Try> & If.Forced}:
  (ts, o) = X
  {==}

# a miss with a retry left: the next attempt, as force.go's
def ifs.retry(-more: Bool, f: Bool, -X: List<&2, If.Try> & If.Forced, Y: List<&2, If.Try> & If.Forced, e: {more == True{} : Bool}, h: {X == Y : List<&2, If.Try> & If.Forced}) -> {InferForce.drive.next(M.after.miss(more), f, X) == If.force.next(If.Try{f}, Y) : List<&2, If.Try> & If.Forced}:
  %Equal.sym(Bool, more, True{}, e) : {InferForce.drive.next(M.after.miss(_), f, X) == If.force.next(If.Try{f}, Y) : List<&2, If.Try> & If.Forced}
  %Equal.sym(List<&2, If.Try> & If.Forced, X, Y, h) : {InferForce.drive.next(M.Again{}, f, _) == If.force.next(If.Try{f}, Y) : List<&2, If.Try> & If.Forced}
  ifs.again(f, Y)

# the next attempt's retries: i + (1 + q) is (1 + i) + q
def ifs.shift(-rest: List<&2, Bool>, i: Nat, -q: Nat, -sup: Bool, -free: Bool) -> {InferForce.drive(rest, 1n+i, Nat.add(i, 1n+q), sup, free) == InferForce.drive(rest, 1n+i, 1n+Nat.add(i, q), sup, free) : List<&2, If.Try> & If.Forced}:
  %LNat.add_succ(i, q) : {InferForce.drive(rest, 1n+i, Nat.add(i, 1n+q), sup, free) == InferForce.drive(rest, 1n+i, _, sup, free) : List<&2, If.Try> & If.Forced}
  {==}

def ifs.go(replies: List<&2, Bool>, +i: Nat, +q: Nat, +sup: Bool, +free: Bool) -> {InferForce.drive(replies, i, Nat.add(i, q), sup, free) == If.force.go(replies, q, M.flag(i, sup, free), sup) : List<&2, If.Try> & If.Forced}:
  match replies:
    case Nil{}:
      {==}
    case c <> +rest:
      match c:
        case True{}:
          match q:
            case 0n:
              {==}
            case 1n+p:
              {==}
        case False{}:
          match q:
            case 0n:
              ifs.fails(Nat.is_lt(i, Nat.add(i, 0n)), M.flag(i, sup, free), InferForce.drive(rest, 1n+i, Nat.add(i, 0n), sup, free), ifs.lt0(i))
            case 1n++p:
              ifs.retry(Nat.is_lt(i, Nat.add(i, 1n+p)), M.flag(i, sup, free), InferForce.drive(rest, 1n+i, Nat.add(i, 1n+p), sup, free), If.force.go(rest, p, sup, sup), ifs.lt_s(i, p),
                Equal.trans(List<&2, If.Try> & If.Forced, InferForce.drive(rest, 1n+i, Nat.add(i, 1n+p), sup, free), InferForce.drive(rest, 1n+i, 1n+Nat.add(i, p), sup, free), If.force.go(rest, p, sup, sup),
                  ifs.shift(rest, i, p, sup, free), ifs.go(rest, 1n+i, p, sup, free)))

def InferForce.infer_force_steps(replies, r, sup, free):
  ifs.go(replies, 0n, r, sup, free)
