# eukhe: lemmas the proofs of area doc_seen share

import Base
import ../../bend/doc_seen.bend as Ds
import ../../LAWS.bend as Laws

# ==== seen ====
# proof_doc_seen: the seen-line laws of LAWS.bend section documents (F11):
# an edit applies exactly on seen anchors, a rejection names the unseen
# anchors, shows the first `cap` of them that are lines (cut past
# `cols`), and marks them seen only when it showed them all whole, so a
# straight retry applies exactly then.
# Logic and numbers
# -----------------

def documents.pv.BD(b: Bool, t: Type, f: Type) -> Type:
  match b:
    case True{}:
      t
    case False{}:
      f

def documents.pv.absurd(-A: Type, e: {True{} == False{} : Bool}) -> A:
  %e : documents.pv.BD(_, Unit, A)
  Unit{}

def documents.pv.and_l(p: Bool, q: Bool, h: {Bool.and(p, q) == True{} : Bool}) -> {p == True{} : Bool}:
  match p:
    case True{}:
      {==}
    case False{}:
      documents.pv.absurd({False{} == True{} : Bool}, Equal.sym(Bool, False{}, True{}, h))

def documents.pv.and_r(p: Bool, q: Bool, h: {Bool.and(p, q) == True{} : Bool}) -> {q == True{} : Bool}:
  match p:
    case True{}:
      h
    case False{}:
      documents.pv.absurd({q == True{} : Bool}, Equal.sym(Bool, False{}, True{}, h))

def pv.and_tt(p: Bool, q: Bool, hp: {p == True{} : Bool}, hq: {q == True{} : Bool}) -> {Bool.and(p, q) == True{} : Bool}:
  %Equal.sym(Bool, p, True{}, hp) : {Bool.and(_, q) == True{} : Bool}
  hq

# Membership in the seen runs
# ---------------------------

# the guard's tail loop is the spec's membership
def pv.mem_go(ivs: List<&2, Ds.Iv>, +n: Nat, h: Bool) -> {Ds.mem.go(ivs, n, h) == Bool.or(h, Laws.seen.In(n, ivs)) : Bool}:
  match ivs:
    case Nil{}:
      match h:
        case True{}:
          {==}
        case False{}:
          {==}
    case iv <> +rest:
      match iv:
        case Ds.Iv{+lo, +hi}:
          match h:
            case True{}:
              {==}
            case False{}:
              pv.mem_go(rest, n, Bool.and(Nat.is_le(lo, n), Nat.is_le(n, hi)))

def pv.mem_eq(+n: Nat, ivs: List<&2, Ds.Iv>) -> {Ds.mem(n, ivs) == Laws.seen.In(n, ivs) : Bool}:
  pv.mem_go(ivs, n, False{})

def pv.in_of_mem(+n: Nat, +ivs: List<&2, Ds.Iv>, h: {Ds.mem(n, ivs) == True{} : Bool}) -> {Laws.seen.In(n, ivs) == True{} : Bool}:
  %pv.mem_eq(n, ivs) : {_ == True{} : Bool}
  h

def pv.mem_of_in(+n: Nat, +ivs: List<&2, Ds.Iv>, h: {Laws.seen.In(n, ivs) == True{} : Bool}) -> {Ds.mem(n, ivs) == True{} : Bool}:
  %Equal.sym(Bool, Ds.mem(n, ivs), Laws.seen.In(n, ivs), pv.mem_eq(n, ivs)) : {_ == True{} : Bool}
  h

# The spec of the unseen anchors, shown lines and whole reveal
# ------------------------------------------------------------

def pv.put_keep(+a: Ds.At, u: List<&2, Ds.At>, b: Bool) -> {Ds.unseen.put(a, u, b) == Laws.seen.Unseen.keep(a, u, b) : List<&2, Ds.At>}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def pv.unseen_eq(+seen: List<&2, Ds.Iv>, ats: List<&2, Ds.At>) -> {Ds.unseen(seen, ats) == Laws.seen.Unseen(seen, ats) : List<&2, Ds.At>}:
  match ats:
    case Nil{}:
      {==}
    case +a <> +rest:
      %pv.unseen_eq(seen, rest) : {Ds.unseen.put(a, Ds.unseen(seen, rest), Ds.mem(Ds.At.line(a), seen)) == Laws.seen.Unseen.keep(a, _, Laws.seen.In(Ds.At.line(a), seen)) : List<&2, Ds.At>}
      %pv.mem_eq(Ds.At.line(a), seen) : {Ds.unseen.put(a, Ds.unseen(seen, rest), Ds.mem(Ds.At.line(a), seen)) == Laws.seen.Unseen.keep(a, Ds.unseen(seen, rest), _) : List<&2, Ds.At>}
      pv.put_keep(a, Ds.unseen(seen, rest), Ds.mem(Ds.At.line(a), seen))

def pv.fit_and(w: Maybe<&2, Nat>, q: Bool) -> {Bool.and(Ds.fits.w(w), q) == Bool.and(Laws.seen.Fit(w), q) : Bool}:
  match w:
    case None{}:
      {==}
    case Some{x}:
      {==}

def pv.fits_eq(us: List<&2, Ds.At>) -> {Ds.fits(us) == Laws.seen.Fits(us) : Bool}:
  match us:
    case Nil{}:
      {==}
    case a <> +rest:
      match a:
        case Ds.At{n, w}:
          %pv.fits_eq(rest) : {Bool.and(Ds.fits.w(w), Ds.fits(rest)) == Bool.and(Laws.seen.Fit(w), _) : Bool}
          pv.fit_and(w, Ds.fits(rest))

def pv.whole_eq(b: Bool, +u: List<&2, Ds.At>) -> {Ds.whole.go(b, u) == Bool.and(b, Laws.seen.Fits(u)) : Bool}:
  match b:
    case True{}:
      pv.fits_eq(u)
    case False{}:
      {==}

# Seen anchors: the edit applies
# ------------------------------

def pv.subset_nil(+seen: List<&2, Ds.Iv>, ats: List<&2, Ds.At>, +h: {Laws.seen.Sub(Ds.lines(ats), seen) == True{} : Bool}) -> {Ds.unseen(seen, ats) == Nil{} : List<&2, Ds.At>}:
  match ats:
    case Nil{}:
      {==}
    case +a <> +rest:
      +hm = pv.mem_of_in(Ds.At.line(a), seen, documents.pv.and_l(Laws.seen.In(Ds.At.line(a), seen), Laws.seen.Sub(Ds.lines(rest), seen), h))
      +hr = documents.pv.and_r(Laws.seen.In(Ds.At.line(a), seen), Laws.seen.Sub(Ds.lines(rest), seen), h)
      %Equal.sym(Bool, Ds.mem(Ds.At.line(a), seen), True{}, hm) : {Ds.unseen.put(a, Ds.unseen(seen, rest), _) == Nil{} : List<&2, Ds.At>}
      pv.subset_nil(seen, rest, hr)

def pv.edit_seen_applies(+seen: List<&2, Ds.Iv>, +ats: List<&2, Ds.At>, all: {Laws.seen.Sub(Ds.lines(ats), seen) == True{} : Bool}) -> {Ds.Step.applied(Ds.edit(seen, ats)) == True{} : Bool}:
  %Equal.sym(List<&2, Ds.At>, Ds.unseen(seen, ats), Nil{}, pv.subset_nil(seen, ats, all)) : {Ds.Step.applied(Ds.edit.go(seen, Ds.check.go(_))) == True{} : Bool}
  {==}
