# eukhe: the proof of LAW reveal_then_retry

import Base
import ../../bend/doc_seen.bend as Ds
import ../../LAWS.bend as Laws
import ./base.bend as LA

def pv.or_t(a: Bool) -> {Bool.or(a, True{}) == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

def pv.le_succ(m: Nat, k: Nat, h: {Nat.is_le(m, k) == True{} : Bool}) -> {Nat.is_le(m, 1n+k) == True{} : Bool}:
  match m k:
    case 0n k:
      {==}
    case 1n+p 0n:
      LA.documents.pv.absurd({Nat.is_le(1n+p, 1n) == True{} : Bool}, Equal.sym(Bool, False{}, True{}, h))
    case 1n+p 1n+q:
      pv.le_succ(p, q, h)

def pv.le_refl(a: Nat) -> {Nat.is_le(a, a) == True{} : Bool}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      pv.le_refl(p)

def pv.in_head(+a: Nat, ys: List<&2, Ds.Iv>) -> {Laws.seen.In(a, Ds.Iv{a, a} <> ys) == True{} : Bool}:
  %Equal.sym(Bool, Nat.is_le(a, a), True{}, pv.le_refl(a)) : {Bool.or(Bool.and(_, _), Laws.seen.In(a, ys)) == True{} : Bool}
  {==}

def pv.in_cons(b: Ds.Iv, +x: Nat, ys: List<&2, Ds.Iv>, h: {Laws.seen.In(x, ys) == True{} : Bool}) -> {Laws.seen.In(x, b <> ys) == True{} : Bool}:
  %Equal.sym(Bool, Laws.seen.In(x, ys), True{}, h) : {Bool.or(Laws.seen.Inside(x, b), _) == True{} : Bool}
  pv.or_t(Laws.seen.Inside(x, b))

def pv.in_app(+a: Nat, xs: List<&2, Ds.Iv>, +ys: List<&2, Ds.Iv>, h: {Laws.seen.In(a, ys) == True{} : Bool}) -> {Laws.seen.In(a, List.append(&2, Ds.Iv, xs, ys)) == True{} : Bool}:
  match xs:
    case Nil{}:
      h
    case x <> +rest:
      pv.in_cons(x, a, List.append(&2, Ds.Iv, rest, ys), pv.in_app(a, rest, ys, h))

def pv.sub_cons(xs: List<&2, Nat>, +b: Ds.Iv, +ys: List<&2, Ds.Iv>, +h: {Laws.seen.Sub(xs, ys) == True{} : Bool}) -> {Laws.seen.Sub(xs, b <> ys) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +rest:
      +hm = LA.documents.pv.and_l(Laws.seen.In(x, ys), Laws.seen.Sub(rest, ys), h)
      +hr = LA.documents.pv.and_r(Laws.seen.In(x, ys), Laws.seen.Sub(rest, ys), h)
      LA.pv.and_tt(Laws.seen.In(x, b <> ys), Laws.seen.Sub(rest, b <> ys), pv.in_cons(b, x, ys, hm), pv.sub_cons(rest, b, ys, hr))

# A rejection, then a retry
# -------------------------

# every anchor is seen or unseen
def pv.cover.go(+seen: List<&2, Ds.Iv>, +a: Ds.At, +rest: List<&2, Ds.At>, b: Bool, e: {Ds.mem(Ds.At.line(a), seen) == b : Bool}, ih: {Laws.seen.Sub(Ds.lines(rest), List.append(&2, Ds.Iv, Ds.points(Ds.lines(Ds.unseen(seen, rest))), seen)) == True{} : Bool}) -> {Laws.seen.Sub(Ds.lines(a <> rest), List.append(&2, Ds.Iv, Ds.points(Ds.lines(Ds.unseen.put(a, Ds.unseen(seen, rest), b))), seen)) == True{} : Bool}:
  match b:
    case True{}:
      +u = Ds.points(Ds.lines(Ds.unseen(seen, rest)))
      LA.pv.and_tt(Laws.seen.In(Ds.At.line(a), List.append(&2, Ds.Iv, u, seen)), Laws.seen.Sub(Ds.lines(rest), List.append(&2, Ds.Iv, u, seen)), pv.in_app(Ds.At.line(a), u, seen, LA.pv.in_of_mem(Ds.At.line(a), seen, e)), ih)
    case False{}:
      +l = Ds.At.line(a)
      +y = List.append(&2, Ds.Iv, Ds.points(Ds.lines(Ds.unseen(seen, rest))), seen)
      LA.pv.and_tt(Laws.seen.In(l, Ds.Iv{l, l} <> y), Laws.seen.Sub(Ds.lines(rest), Ds.Iv{l, l} <> y), pv.in_head(l, y), pv.sub_cons(Ds.lines(rest), Ds.Iv{l, l}, y, ih))

def pv.cover(+seen: List<&2, Ds.Iv>, ats: List<&2, Ds.At>) -> {Laws.seen.Sub(Ds.lines(ats), List.append(&2, Ds.Iv, Ds.points(Ds.lines(Ds.unseen(seen, ats))), seen)) == True{} : Bool}:
  match ats:
    case Nil{}:
      {==}
    case +a <> +rest:
      pv.cover.go(seen, a, rest, Ds.mem(Ds.At.line(a), seen), {==}, pv.cover(seen, rest))

def pv.short.go(+a: Ds.At, u: List<&2, Ds.At>, +k: Nat, b: Bool, ih: {Nat.is_le(List.length(&2, Ds.At, u), k) == True{} : Bool}) -> {Nat.is_le(List.length(&2, Ds.At, Ds.unseen.put(a, u, b)), 1n+k) == True{} : Bool}:
  match b:
    case True{}:
      pv.le_succ(List.length(&2, Ds.At, u), k, ih)
    case False{}:
      ih

# a rejection has no more unseen anchors than anchors
def pv.short(+seen: List<&2, Ds.Iv>, ats: List<&2, Ds.At>, n: Nat, h: {Nat.is_le(List.length(&2, Ds.At, ats), n) == True{} : Bool}) -> {Nat.is_le(List.length(&2, Ds.At, Ds.unseen(seen, ats)), n) == True{} : Bool}:
  match ats n:
    case Nil{} 0n:
      {==}
    case Nil{} 1n+k:
      {==}
    case +a <> rest 0n:
      LA.documents.pv.absurd({Nat.is_le(List.length(&2, Ds.At, Ds.unseen(seen, a <> rest)), 0n) == True{} : Bool}, Equal.sym(Bool, False{}, True{}, h))
    case +a <> +rest 1n+(+k):
      pv.short.go(a, Ds.unseen(seen, rest), k, Ds.mem(Ds.At.line(a), seen), pv.short(seen, rest, k, h))

# the retry after a rejection with unseen anchors x <> rest, whole or not
def pv.retry.fit(+seen: List<&2, Ds.Iv>, +ats: List<&2, Ds.At>, +x: Ds.At, +rest: List<&2, Ds.At>, eu: {Ds.unseen(seen, ats) == x <> rest : List<&2, Ds.At>}, cover: {Laws.seen.Sub(Ds.lines(ats), List.append(&2, Ds.Iv, Ds.points(Ds.lines(x <> rest)), seen)) == True{} : Bool}, b: Bool) -> {Ds.Step.applied(Ds.edit(Ds.reveal(Ds.lines(x <> rest), seen, b), ats)) == b : Bool}:
  match b:
    case True{}:
      LA.pv.edit_seen_applies(List.append(&2, Ds.Iv, Ds.points(Ds.lines(x <> rest)), seen), ats, cover)
    case False{}:
      %Equal.sym(List<&2, Ds.At>, Ds.unseen(seen, ats), x <> rest, eu) : {Ds.Step.applied(Ds.edit.go(seen, Ds.check.go(_))) == False{} : Bool}
      {==}

def pv.retry.go(+seen: List<&2, Ds.Iv>, +ats: List<&2, Ds.At>, +u: List<&2, Ds.At>, eu: {Ds.unseen(seen, ats) == u : List<&2, Ds.At>}, few: {Nat.is_le(List.length(&2, Ds.At, u), Ds.cap) == True{} : Bool}, cover: {Laws.seen.Sub(Ds.lines(ats), List.append(&2, Ds.Iv, Ds.points(Ds.lines(u)), seen)) == True{} : Bool}) -> {Ds.Step.applied(Ds.edit(Ds.Step.seen(Ds.edit.go(seen, Ds.check.go(u))), ats)) == Ds.fits(u) : Bool}:
  match u:
    case Nil{}:
      %Equal.sym(List<&2, Ds.At>, Ds.unseen(seen, ats), Nil{}, eu) : {Ds.Step.applied(Ds.edit.go(seen, Ds.check.go(_))) == True{} : Bool}
      {==}
    case +x <> +rest:
      %Equal.sym(Bool, Nat.is_le(List.length(&2, Ds.At, x <> rest), Ds.cap), True{}, few) : {Ds.Step.applied(Ds.edit(Ds.reveal(Ds.lines(x <> rest), seen, Ds.whole.go(_, x <> rest)), ats)) == Ds.fits(x <> rest) : Bool}
      pv.retry.fit(seen, ats, x, rest, eu, cover, Ds.fits(x <> rest))

def Laws.reveal_then_retry(seen, ats, few):
  %LA.pv.unseen_eq(seen, ats) : {Ds.Step.applied(Ds.edit(Ds.Step.seen(Ds.edit(seen, ats)), ats)) == Laws.seen.Fits(_) : Bool}
  %LA.pv.fits_eq(Ds.unseen(seen, ats)) : {Ds.Step.applied(Ds.edit(Ds.Step.seen(Ds.edit(seen, ats)), ats)) == _ : Bool}
  pv.retry.go(seen, ats, Ds.unseen(seen, ats), {==}, pv.short(seen, ats, Ds.cap, few), pv.cover(seen, ats))
