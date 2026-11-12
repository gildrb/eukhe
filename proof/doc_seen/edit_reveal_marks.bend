# eukhe: the proof of LAW edit_reveal_marks
#
# PROOF: the edit ends in edit.fin on the verdict's unseen lines and whole
# flag; nothing unseen keeps the seen lines; a rejection appends a run of
# one line per unseen line when whole (membership in an append is the or of
# the two, a run of one line holds exactly that line), else keeps them.

import Base
import ../../bend/doc_seen.bend as Ds
import ../../laws/doc_seen.bend as DocSeen
import ./base.bend as LA

def erm.or_f(b: Bool) -> {b == Bool.or(b, False{}) : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def erm.or_and_f(b: Bool, w: Bool) -> {b == Bool.or(b, Bool.and(w, False{})) : Bool}:
  match w:
    case True{}:
      erm.or_f(b)
    case False{}:
      erm.or_f(b)

def erm.or_assoc(a: Bool, -b: Bool, -c: Bool) -> {Bool.or(a, Bool.or(b, c)) == Bool.or(Bool.or(a, b), c) : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

def erm.or_comm(a: Bool, b: Bool) -> {Bool.or(a, b) == Bool.or(b, a) : Bool}:
  match a b:
    case True{} True{}:
      {==}
    case True{} False{}:
      {==}
    case False{} True{}:
      {==}
    case False{} False{}:
      {==}

# lo <= n <= hi with lo = hi = x: n is x
def erm.le2(x: Nat, n: Nat) -> {Bool.and(Nat.is_le(x, n), Nat.is_le(n, x)) == Nat.is_eq(x, n) : Bool}:
  match x n:
    case 0n 0n:
      {==}
    case 0n 1n+m:
      {==}
    case 1n+k 0n:
      {==}
    case 1n+k 1n+m:
      erm.le2(k, m)

# a line of runs xs then ys is a line of xs or of ys
def erm.in_app(+n: Nat, xs: List<&2, Ds.Iv>, +ys: List<&2, Ds.Iv>) -> {DocSeen.seen.In(n, List.append(&2, Ds.Iv, xs, ys)) == Bool.or(DocSeen.seen.In(n, xs), DocSeen.seen.In(n, ys)) : Bool}:
  match xs:
    case Nil{}:
      {==}
    case iv <> +rest:
      +a = DocSeen.seen.Inside(n, iv)
      %Equal.sym(Bool, DocSeen.seen.In(n, List.append(&2, Ds.Iv, rest, ys)), Bool.or(DocSeen.seen.In(n, rest), DocSeen.seen.In(n, ys)), erm.in_app(n, rest, ys)) : {Bool.or(a, _) == Bool.or(Bool.or(a, DocSeen.seen.In(n, rest)), DocSeen.seen.In(n, ys)) : Bool}
      erm.or_assoc(a, DocSeen.seen.In(n, rest), DocSeen.seen.In(n, ys))

# a line of the runs of one line each of xs is one of xs
def erm.in_points(+n: Nat, xs: List<&2, Nat>) -> {DocSeen.seen.In(n, Ds.points(xs)) == DocSeen.seen.NatIn(n, xs) : Bool}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +rest:
      %Equal.sym(Bool, DocSeen.seen.In(n, Ds.points(rest)), DocSeen.seen.NatIn(n, rest), erm.in_points(n, rest)) : {Bool.or(Bool.and(Nat.is_le(x, n), Nat.is_le(n, x)), _) == Bool.or(Nat.is_eq(x, n), DocSeen.seen.NatIn(n, rest)) : Bool}
      %Equal.sym(Bool, Bool.and(Nat.is_le(x, n), Nat.is_le(n, x)), Nat.is_eq(x, n), erm.le2(x, n)) : {Bool.or(_, DocSeen.seen.NatIn(n, rest)) == Bool.or(Nat.is_eq(x, n), DocSeen.seen.NatIn(n, rest)) : Bool}
      {==}

def erm.fin(+n: Nat, +seen: List<&2, Ds.Iv>, u: List<&2, Nat>, w: Bool) -> {DocSeen.seen.In(n, Ds.Step.seen(Ds.edit.fin(seen, u, w))) == Bool.or(DocSeen.seen.In(n, seen), Bool.and(w, DocSeen.seen.NatIn(n, u))) : Bool}:
  match u:
    case Nil{}:
      erm.or_and_f(DocSeen.seen.In(n, seen), w)
    case +x <> +rest:
      match w:
        case True{}:
          +ps = Ds.points(x <> rest)
          %Equal.sym(Bool, DocSeen.seen.In(n, List.append(&2, Ds.Iv, ps, seen)), Bool.or(DocSeen.seen.In(n, ps), DocSeen.seen.In(n, seen)), erm.in_app(n, ps, seen)) : {_ == Bool.or(DocSeen.seen.In(n, seen), DocSeen.seen.NatIn(n, x <> rest)) : Bool}
          %Equal.sym(Bool, DocSeen.seen.In(n, ps), DocSeen.seen.NatIn(n, x <> rest), erm.in_points(n, x <> rest)) : {Bool.or(_, DocSeen.seen.In(n, seen)) == Bool.or(DocSeen.seen.In(n, seen), DocSeen.seen.NatIn(n, x <> rest)) : Bool}
          erm.or_comm(DocSeen.seen.NatIn(n, x <> rest), DocSeen.seen.In(n, seen))
        case False{}:
          erm.or_f(DocSeen.seen.In(n, seen))

def DocSeen.edit_reveal_marks(seen, ats, n):
  +u = Ds.unseen(seen, ats)
  erm.fin(n, seen, Ds.lines(u), Ds.whole.go(Nat.is_le(List.length(&2, Ds.At, u), Ds.cap), u))
