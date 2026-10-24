# eukhe: the proof of LAW cvar_refusal_exact
# The model walks the declarations onto the ones it kept; the spec, onto
# their ids. An id is taken in the kept ones exactly when it is one of
# their ids (rf.mem), the kept ones grow by the declaration and the ids by
# its id (rf.snoc), and the type test is the spec's (LR.re.ty).

import Base
import ../../bend/cvar.bend as Cv
import ../../laws/cvar.bend as Cvar
import ./base/resolve.bend as LR

# the ids of ds, in order
def rf.ids(ds: List<&2, Cv.Decl>) -> List<&2, Nat>:
  match ds:
    case Nil{}:
      Nil{}
    case d <> r:
      Cvar.spec_id(d) <> rf.ids(r)

def rf.mem_go(b: Bool, +d: Cv.Decl, +r: List<&2, Cv.Decl>, +x: Nat, ih: {Maybe.is_some(&2, Cv.Decl, Cv.find(r, x)) == Cvar.spec_mem(x, rf.ids(r)) : Bool}) -> {Maybe.is_some(&2, Cv.Decl, Cv.find.go(d <> r, x, b)) == Bool.or(b, Cvar.spec_mem(x, rf.ids(r))) : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      ih

# x is taken in ds exactly when it is one of their ids
def rf.mem(ds: List<&2, Cv.Decl>, +x: Nat) -> {Maybe.is_some(&2, Cv.Decl, Cv.find(ds, x)) == Cvar.spec_mem(x, rf.ids(ds)) : Bool}:
  match ds:
    case Nil{}:
      {==}
    case Cv.Decl{+i, +t, +c, +p, +r, +v} <> +rest:
      rf.mem_go(Nat.is_eq(i, x), Cv.Decl{i, t, c, p, r, v}, rest, x, rf.mem(rest, x))

# the ids of ds then d
def rf.snoc(ds: List<&2, Cv.Decl>, +d: Cv.Decl) -> {rf.ids(List.append(&2, Cv.Decl, ds, [d])) == List.append(&2, Nat, rf.ids(ds), [Cvar.spec_id(d)]) : List<&2, Nat>}:
  match ds:
    case Nil{}:
      {==}
    case +h <> +r:
      Equal.cong(List<&2, Nat>, List<&2, Nat>, t => Cvar.spec_id(h) <> t, rf.ids(List.append(&2, Cv.Decl, r, [d])), List.append(&2, Nat, rf.ids(r), [Cvar.spec_id(d)]), rf.snoc(r, d))

def rf.at(taken: Bool, good: Bool, +d: Cv.Decl, +i: Nat, +rest: List<&2, Cv.Decl>, +ds: List<&2, Cv.Decl>, ei: {Cv.Decl.id(d) == i : Nat},
  ih: {Cv.refusal.go(rest, List.append(&2, Cv.Decl, ds, [d]), Cv.taken.at(rest, List.append(&2, Cv.Decl, ds, [d])), Cv.typed.first(rest)) == Cvar.spec_refusal(rest, rf.ids(List.append(&2, Cv.Decl, ds, [d]))) : Cv.Refusal})
  -> {Cv.refusal.go(d <> rest, ds, taken, good) == Cvar.spec_refusal.pick(taken, good, i, Cvar.spec_refusal(rest, rf.ids(List.append(&2, Cv.Decl, ds, [d])))) : Cv.Refusal}:
  match taken:
    case True{}:
      Equal.cong(Nat, Cv.Refusal, k => Cv.Twice{k}, Cv.Decl.id(d), i, ei)
    case False{}:
      match good:
        case True{}:
          ih
        case False{}:
          Equal.cong(Nat, Cv.Refusal, k => Cv.BadInit{k}, Cv.Decl.id(d), i, ei)

# the walk onto the kept ds is the spec's walk onto their ids
def rf.go(xs: List<&2, Cv.Decl>, +ds: List<&2, Cv.Decl>) -> {Cv.refusal.go(xs, ds, Cv.taken.at(xs, ds), Cv.typed.first(xs)) == Cvar.spec_refusal(xs, rf.ids(ds)) : Cv.Refusal}:
  match xs:
    case Nil{}:
      {==}
    case Cv.Decl{+i, +t, +c, +p, +r, +v} <> +rest:
      +d = {Cv.Decl{i, t, c, p, r, v} : Cv.Decl}
      +kept = List.append(&2, Cv.Decl, ds, [d])
      %rf.snoc(ds, d) : {Cv.refusal.go(d <> rest, ds, Maybe.is_some(&2, Cv.Decl, Cv.find(ds, i)), Cv.Ty.eq(Cv.Val.ty(v), t)) == Cvar.spec_refusal.pick(Cvar.spec_mem(i, rf.ids(ds)), Cvar.spec_typed(v, t), i, Cvar.spec_refusal(rest, _)) : Cv.Refusal}
      %rf.mem(ds, i) : {Cv.refusal.go(d <> rest, ds, Maybe.is_some(&2, Cv.Decl, Cv.find(ds, i)), Cv.Ty.eq(Cv.Val.ty(v), t)) == Cvar.spec_refusal.pick(_, Cvar.spec_typed(v, t), i, Cvar.spec_refusal(rest, rf.ids(kept))) : Cv.Refusal}
      %LR.re.ty(v, t) : {Cv.refusal.go(d <> rest, ds, Maybe.is_some(&2, Cv.Decl, Cv.find(ds, i)), Cv.Ty.eq(Cv.Val.ty(v), t)) == Cvar.spec_refusal.pick(Maybe.is_some(&2, Cv.Decl, Cv.find(ds, i)), _, i, Cvar.spec_refusal(rest, rf.ids(kept))) : Cv.Refusal}
      rf.at(Maybe.is_some(&2, Cv.Decl, Cv.find(ds, i)), Cv.Ty.eq(Cv.Val.ty(v), t), d, i, rest, ds, {==}, rf.go(rest, kept))

def Cvar.cvar_refusal_exact(xs):
  rf.go(xs, Nil{})
