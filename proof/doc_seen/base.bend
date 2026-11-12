# eukhe: lemmas the proofs of area doc_seen share

import Base
import ../../bend/doc_seen.bend as Ds
import ../../laws/doc_seen.bend as DocSeen

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
def pv.mem_go(ivs: List<&2, Ds.Iv>, +n: Nat, h: Bool) -> {Ds.mem.go(ivs, n, h) == Bool.or(h, DocSeen.seen.In(n, ivs)) : Bool}:
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

def pv.mem_eq(+n: Nat, ivs: List<&2, Ds.Iv>) -> {Ds.mem(n, ivs) == DocSeen.seen.In(n, ivs) : Bool}:
  pv.mem_go(ivs, n, False{})

def pv.in_of_mem(+n: Nat, +ivs: List<&2, Ds.Iv>, h: {Ds.mem(n, ivs) == True{} : Bool}) -> {DocSeen.seen.In(n, ivs) == True{} : Bool}:
  %pv.mem_eq(n, ivs) : {_ == True{} : Bool}
  h

def pv.mem_of_in(+n: Nat, +ivs: List<&2, Ds.Iv>, h: {DocSeen.seen.In(n, ivs) == True{} : Bool}) -> {Ds.mem(n, ivs) == True{} : Bool}:
  %Equal.sym(Bool, Ds.mem(n, ivs), DocSeen.seen.In(n, ivs), pv.mem_eq(n, ivs)) : {_ == True{} : Bool}
  h

# The spec of the unseen anchors, shown lines and whole reveal
# ------------------------------------------------------------

def pv.put_keep(+a: Ds.At, u: List<&2, Ds.At>, b: Bool) -> {Ds.unseen.put(a, u, b) == DocSeen.seen.Unseen.keep(a, u, b) : List<&2, Ds.At>}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def pv.unseen_eq(+seen: List<&2, Ds.Iv>, ats: List<&2, Ds.At>) -> {Ds.unseen(seen, ats) == DocSeen.seen.Unseen(seen, ats) : List<&2, Ds.At>}:
  match ats:
    case Nil{}:
      {==}
    case +a <> +rest:
      %pv.unseen_eq(seen, rest) : {Ds.unseen.put(a, Ds.unseen(seen, rest), Ds.mem(Ds.At.line(a), seen)) == DocSeen.seen.Unseen.keep(a, _, DocSeen.seen.In(Ds.At.line(a), seen)) : List<&2, Ds.At>}
      %pv.mem_eq(Ds.At.line(a), seen) : {Ds.unseen.put(a, Ds.unseen(seen, rest), Ds.mem(Ds.At.line(a), seen)) == DocSeen.seen.Unseen.keep(a, Ds.unseen(seen, rest), _) : List<&2, Ds.At>}
      pv.put_keep(a, Ds.unseen(seen, rest), Ds.mem(Ds.At.line(a), seen))

def pv.fit_and(w: Maybe<&2, Nat>, q: Bool) -> {Bool.and(Ds.fits.w(w), q) == Bool.and(DocSeen.seen.Fit(w), q) : Bool}:
  match w:
    case None{}:
      {==}
    case Some{x}:
      {==}

def pv.fits_eq(us: List<&2, Ds.At>) -> {Ds.fits(us) == DocSeen.seen.Fits(us) : Bool}:
  match us:
    case Nil{}:
      {==}
    case a <> +rest:
      match a:
        case Ds.At{n, w}:
          %pv.fits_eq(rest) : {Bool.and(Ds.fits.w(w), Ds.fits(rest)) == Bool.and(DocSeen.seen.Fit(w), _) : Bool}
          pv.fit_and(w, Ds.fits(rest))

def pv.whole_eq(b: Bool, +u: List<&2, Ds.At>) -> {Ds.whole.go(b, u) == Bool.and(b, DocSeen.seen.Fits(u)) : Bool}:
  match b:
    case True{}:
      pv.fits_eq(u)
    case False{}:
      {==}

# Seen anchors: the edit applies
# ------------------------------

def pv.subset_nil(+seen: List<&2, Ds.Iv>, ats: List<&2, Ds.At>, +h: {DocSeen.seen.Sub(Ds.lines(ats), seen) == True{} : Bool}) -> {Ds.unseen(seen, ats) == Nil{} : List<&2, Ds.At>}:
  match ats:
    case Nil{}:
      {==}
    case +a <> +rest:
      +hm = pv.mem_of_in(Ds.At.line(a), seen, documents.pv.and_l(DocSeen.seen.In(Ds.At.line(a), seen), DocSeen.seen.Sub(Ds.lines(rest), seen), h))
      +hr = documents.pv.and_r(DocSeen.seen.In(Ds.At.line(a), seen), DocSeen.seen.Sub(Ds.lines(rest), seen), h)
      %Equal.sym(Bool, Ds.mem(Ds.At.line(a), seen), True{}, hm) : {Ds.unseen.put(a, Ds.unseen(seen, rest), _) == Nil{} : List<&2, Ds.At>}
      pv.subset_nil(seen, rest, hr)

def pv.edit_seen_applies(+seen: List<&2, Ds.Iv>, +ats: List<&2, Ds.At>, all: {DocSeen.seen.Sub(Ds.lines(ats), seen) == True{} : Bool}) -> {Ds.Step.applied(Ds.edit(seen, ats)) == True{} : Bool}:
  %Equal.sym(List<&2, Ds.At>, Ds.unseen(seen, ats), Nil{}, pv.subset_nil(seen, ats, all)) : {Ds.Step.applied(Ds.edit.go(seen, Ds.check.go(_))) == True{} : Bool}
  {==}

# The reveal: lists, lengths and the guard's pieces
# -------------------------------------------------

def dsr.put_app(+a: Ds.At, r: List<&2, Ds.At>, ys: List<&2, Ds.At>, b: Bool) -> {Ds.unseen.put(a, List.append(&2, Ds.At, r, ys), b) == List.append(&2, Ds.At, Ds.unseen.put(a, r, b), ys) : List<&2, Ds.At>}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

# the unseen anchors of xs then ys: those of xs, then those of ys
def dsr.unseen_app(+seen: List<&2, Ds.Iv>, xs: List<&2, Ds.At>, +ys: List<&2, Ds.At>) -> {Ds.unseen(seen, List.append(&2, Ds.At, xs, ys)) == List.append(&2, Ds.At, Ds.unseen(seen, xs), Ds.unseen(seen, ys)) : List<&2, Ds.At>}:
  match xs:
    case Nil{}:
      {==}
    case +a <> +rest:
      +m = Ds.mem(Ds.At.line(a), seen)
      %Equal.sym(List<&2, Ds.At>, Ds.unseen(seen, List.append(&2, Ds.At, rest, ys)), List.append(&2, Ds.At, Ds.unseen(seen, rest), Ds.unseen(seen, ys)), dsr.unseen_app(seen, rest, ys)) : {Ds.unseen.put(a, _, m) == List.append(&2, Ds.At, Ds.unseen.put(a, Ds.unseen(seen, rest), m), Ds.unseen(seen, ys)) : List<&2, Ds.At>}
      dsr.put_app(a, Ds.unseen(seen, rest), Ds.unseen(seen, ys), m)

def dsr.shows_put_app(+n: Nat, w: Maybe<&2, Nat>, r: List<&2, Ds.Show>, ys: List<&2, Ds.Show>) -> {Ds.shows.put(n, w, List.append(&2, Ds.Show, r, ys)) == List.append(&2, Ds.Show, Ds.shows.put(n, w, r), ys) : List<&2, Ds.Show>}:
  match w:
    case None{}:
      {==}
    case Some{x}:
      {==}

# the lines shown of xs then ys: those of xs, then those of ys
def dsr.shows_app(xs: List<&2, Ds.At>, +ys: List<&2, Ds.At>) -> {Ds.shows(List.append(&2, Ds.At, xs, ys)) == List.append(&2, Ds.Show, Ds.shows(xs), Ds.shows(ys)) : List<&2, Ds.Show>}:
  match xs:
    case Nil{}:
      {==}
    case a <> +rest:
      match a:
        case Ds.At{+n, +w}:
          %Equal.sym(List<&2, Ds.Show>, Ds.shows(List.append(&2, Ds.At, rest, ys)), List.append(&2, Ds.Show, Ds.shows(rest), Ds.shows(ys)), dsr.shows_app(rest, ys)) : {Ds.shows.put(n, w, _) == List.append(&2, Ds.Show, Ds.shows.put(n, w, Ds.shows(rest)), Ds.shows(ys)) : List<&2, Ds.Show>}
          dsr.shows_put_app(n, w, Ds.shows(rest), Ds.shows(ys))

def dsr.and_assoc(a: Bool, -b: Bool, -c: Bool) -> {Bool.and(a, Bool.and(b, c)) == Bool.and(Bool.and(a, b), c) : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

# xs then ys fit whole: both do
def dsr.fits_app(xs: List<&2, Ds.At>, +ys: List<&2, Ds.At>) -> {Ds.fits(List.append(&2, Ds.At, xs, ys)) == Bool.and(Ds.fits(xs), Ds.fits(ys)) : Bool}:
  match xs:
    case Nil{}:
      {==}
    case a <> +rest:
      match a:
        case Ds.At{n, +w}:
          %Equal.sym(Bool, Ds.fits(List.append(&2, Ds.At, rest, ys)), Bool.and(Ds.fits(rest), Ds.fits(ys)), dsr.fits_app(rest, ys)) : {Bool.and(Ds.fits.w(w), _) == Bool.and(Bool.and(Ds.fits.w(w), Ds.fits(rest)), Ds.fits(ys)) : Bool}
          dsr.and_assoc(Ds.fits.w(w), Ds.fits(rest), Ds.fits(ys))

# a list no longer than n is its own first n items
def dsr.take_all(xs: List<&2, Ds.At>, n: Nat, h: {Nat.is_le(List.length(&2, Ds.At, xs), n) == True{} : Bool}) -> {List.take(&2, Ds.At, xs, n) == xs : List<&2, Ds.At>}:
  match xs n:
    case Nil{} m:
      {==}
    case +x <> t 0n:
      documents.pv.absurd({List.take(&2, Ds.At, x <> t, 0n) == x <> t : List<&2, Ds.At>}, Equal.sym(Bool, False{}, True{}, h))
    case +x <> +t 1n+p:
      %Equal.sym(List<&2, Ds.At>, List.take(&2, Ds.At, t, p), t, dsr.take_all(t, p, h)) : {x <> _ == x <> t : List<&2, Ds.At>}
      {==}

# a list is its own first length items
def dsr.take_self(xs: List<&2, Ds.At>) -> {List.take(&2, Ds.At, xs, List.length(&2, Ds.At, xs)) == xs : List<&2, Ds.At>}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +t:
      %Equal.sym(List<&2, Ds.At>, List.take(&2, Ds.At, t, List.length(&2, Ds.At, t)), t, dsr.take_self(t)) : {x <> _ == x <> t : List<&2, Ds.At>}
      {==}

# the first length(xs) items of xs then ys are xs
def dsr.take_len(xs: List<&2, Ds.At>, ys: List<&2, Ds.At>) -> {List.take(&2, Ds.At, List.append(&2, Ds.At, xs, ys), List.length(&2, Ds.At, xs)) == xs : List<&2, Ds.At>}:
  match xs:
    case Nil{}:
      match ys:
        case Nil{}:
          {==}
        case y <> r:
          {==}
    case +x <> +t:
      %Equal.sym(List<&2, Ds.At>, List.take(&2, Ds.At, List.append(&2, Ds.At, t, ys), List.length(&2, Ds.At, t)), t, dsr.take_len(t, ys)) : {x <> _ == x <> t : List<&2, Ds.At>}
      {==}

def dsr.len_app(xs: List<&2, Ds.At>, +ys: List<&2, Ds.At>) -> {List.length(&2, Ds.At, List.append(&2, Ds.At, xs, ys)) == Nat.add(List.length(&2, Ds.At, xs), List.length(&2, Ds.At, ys)) : Nat}:
  match xs:
    case Nil{}:
      {==}
    case x <> +t:
      %Equal.sym(Nat, List.length(&2, Ds.At, List.append(&2, Ds.At, t, ys)), Nat.add(List.length(&2, Ds.At, t), List.length(&2, Ds.At, ys)), dsr.len_app(t, ys)) : {1n+_ == 1n+Nat.add(List.length(&2, Ds.At, t), List.length(&2, Ds.At, ys)) : Nat}
      {==}

def dsr.le_succ(a: Nat, m: Nat, h: {Nat.is_le(1n+a, m) == True{} : Bool}) -> {Nat.is_le(a, m) == True{} : Bool}:
  match a m:
    case 0n 0n:
      {==}
    case 0n 1n+j:
      {==}
    case 1n+k 0n:
      documents.pv.absurd({Nat.is_le(1n+k, 0n) == True{} : Bool}, Equal.sym(Bool, False{}, True{}, h))
    case 1n+k 1n+j:
      dsr.le_succ(k, j, h)

def dsr.le_add_l(a: Nat, -b: Nat, m: Nat, h: {Nat.is_le(Nat.add(a, b), m) == True{} : Bool}) -> {Nat.is_le(a, m) == True{} : Bool}:
  match a m:
    case 0n 0n:
      {==}
    case 0n 1n+j:
      {==}
    case 1n+k 0n:
      documents.pv.absurd({Nat.is_le(1n+k, 0n) == True{} : Bool}, Equal.sym(Bool, False{}, True{}, h))
    case 1n+k 1n+j:
      dsr.le_add_l(k, b, j, h)

def dsr.le_add_r(a: Nat, +b: Nat, +m: Nat, h: {Nat.is_le(Nat.add(a, b), m) == True{} : Bool}) -> {Nat.is_le(b, m) == True{} : Bool}:
  match a:
    case 0n:
      h
    case 1n++k:
      dsr.le_add_r(k, b, m, dsr.le_succ(Nat.add(k, b), m, h))

# the premises on the spec's unseen anchors, on the guard's
def dsr.le_unseen(+seen: List<&2, Ds.Iv>, +ats: List<&2, Ds.At>, +m: Nat, -v: Bool, h: {Nat.is_le(List.length(&2, Ds.At, DocSeen.seen.Unseen(seen, ats)), m) == v : Bool}) -> {Nat.is_le(List.length(&2, Ds.At, Ds.unseen(seen, ats)), m) == v : Bool}:
  %Equal.sym(List<&2, Ds.At>, Ds.unseen(seen, ats), DocSeen.seen.Unseen(seen, ats), pv.unseen_eq(seen, ats)) : {Nat.is_le(List.length(&2, Ds.At, _), m) == v : Bool}
  h

def dsr.len_unseen(+seen: List<&2, Ds.Iv>, +ats: List<&2, Ds.At>, -k: Nat, h: {List.length(&2, Ds.At, DocSeen.seen.Unseen(seen, ats)) == k : Nat}) -> {List.length(&2, Ds.At, Ds.unseen(seen, ats)) == k : Nat}:
  %Equal.sym(List<&2, Ds.At>, Ds.unseen(seen, ats), DocSeen.seen.Unseen(seen, ats), pv.unseen_eq(seen, ats)) : {List.length(&2, Ds.At, _) == k : Nat}
  h

# a seen line's membership in the guard's tail loop, as a Bool equation
def dsr.mem_is(+n: Nat, +seen: List<&2, Ds.Iv>, -v: Bool, h: {DocSeen.seen.In(n, seen) == v : Bool}) -> {Ds.mem(n, seen) == v : Bool}:
  Equal.trans(Bool, Ds.mem(n, seen), DocSeen.seen.In(n, seen), v, pv.mem_eq(n, seen), h)
