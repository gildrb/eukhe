# eukhe: the proof of LAW reject_joins
#
# PROOF: the unseen anchors of xs then ys are those of xs then those of
# ys; at most 40 of them, so are those of each part, and the first 40 of
# each list are the whole list; the lines shown of an append are those of
# each part, and an append fits whole when both parts do.

import Base
import ../../bend/doc_seen.bend as Ds
import ../../laws/doc_seen.bend as DocSeen
import ./base.bend as LA

def rj.h2(+A: List<&2, Ds.At>, +B: List<&2, Ds.At>, hf: {Nat.is_le(List.length(&2, Ds.At, List.append(&2, Ds.At, A, B)), 40n) == True{} : Bool}) -> {Nat.is_le(Nat.add(List.length(&2, Ds.At, A), List.length(&2, Ds.At, B)), 40n) == True{} : Bool}:
  %LA.dsr.len_app(A, B) : {Nat.is_le(_, 40n) == True{} : Bool}
  hf

def rj.shown(+A: List<&2, Ds.At>, +B: List<&2, Ds.At>, +hf: {Nat.is_le(List.length(&2, Ds.At, List.append(&2, Ds.At, A, B)), 40n) == True{} : Bool}) -> {Ds.shows(List.take(&2, Ds.At, List.append(&2, Ds.At, A, B), 40n)) == List.append(&2, Ds.Show, Ds.shows(List.take(&2, Ds.At, A, 40n)), Ds.shows(List.take(&2, Ds.At, B, 40n))) : List<&2, Ds.Show>}:
  +la = List.length(&2, Ds.At, A)
  +lb = List.length(&2, Ds.At, B)
  +h2 = rj.h2(A, B, hf)
  %Equal.sym(List<&2, Ds.At>, List.take(&2, Ds.At, A, 40n), A, LA.dsr.take_all(A, 40n, LA.dsr.le_add_l(la, lb, 40n, h2))) : {Ds.shows(List.take(&2, Ds.At, List.append(&2, Ds.At, A, B), 40n)) == List.append(&2, Ds.Show, Ds.shows(_), Ds.shows(List.take(&2, Ds.At, B, 40n))) : List<&2, Ds.Show>}
  %Equal.sym(List<&2, Ds.At>, List.take(&2, Ds.At, B, 40n), B, LA.dsr.take_all(B, 40n, LA.dsr.le_add_r(la, lb, 40n, h2))) : {Ds.shows(List.take(&2, Ds.At, List.append(&2, Ds.At, A, B), 40n)) == List.append(&2, Ds.Show, Ds.shows(A), Ds.shows(_)) : List<&2, Ds.Show>}
  %Equal.sym(List<&2, Ds.At>, List.take(&2, Ds.At, List.append(&2, Ds.At, A, B), 40n), List.append(&2, Ds.At, A, B), LA.dsr.take_all(List.append(&2, Ds.At, A, B), 40n, hf)) : {Ds.shows(_) == List.append(&2, Ds.Show, Ds.shows(A), Ds.shows(B)) : List<&2, Ds.Show>}
  LA.dsr.shows_app(A, B)

def rj.whole(+A: List<&2, Ds.At>, +B: List<&2, Ds.At>, +hf: {Nat.is_le(List.length(&2, Ds.At, List.append(&2, Ds.At, A, B)), 40n) == True{} : Bool}) -> {Ds.whole.go(Nat.is_le(List.length(&2, Ds.At, List.append(&2, Ds.At, A, B)), 40n), List.append(&2, Ds.At, A, B)) == Bool.and(Ds.whole.go(Nat.is_le(List.length(&2, Ds.At, A), 40n), A), Ds.whole.go(Nat.is_le(List.length(&2, Ds.At, B), 40n), B)) : Bool}:
  +la = List.length(&2, Ds.At, A)
  +lb = List.length(&2, Ds.At, B)
  +h2 = rj.h2(A, B, hf)
  %Equal.sym(Bool, Nat.is_le(la, 40n), True{}, LA.dsr.le_add_l(la, lb, 40n, h2)) : {Ds.whole.go(Nat.is_le(List.length(&2, Ds.At, List.append(&2, Ds.At, A, B)), 40n), List.append(&2, Ds.At, A, B)) == Bool.and(Ds.whole.go(_, A), Ds.whole.go(Nat.is_le(lb, 40n), B)) : Bool}
  %Equal.sym(Bool, Nat.is_le(lb, 40n), True{}, LA.dsr.le_add_r(la, lb, 40n, h2)) : {Ds.whole.go(Nat.is_le(List.length(&2, Ds.At, List.append(&2, Ds.At, A, B)), 40n), List.append(&2, Ds.At, A, B)) == Bool.and(Ds.fits(A), Ds.whole.go(_, B)) : Bool}
  %Equal.sym(Bool, Nat.is_le(List.length(&2, Ds.At, List.append(&2, Ds.At, A, B)), 40n), True{}, hf) : {Ds.whole.go(_, List.append(&2, Ds.At, A, B)) == Bool.and(Ds.fits(A), Ds.fits(B)) : Bool}
  LA.dsr.fits_app(A, B)

def rj.hf(+seen: List<&2, Ds.Iv>, +xs: List<&2, Ds.At>, +ys: List<&2, Ds.At>, few: {Nat.is_le(List.length(&2, Ds.At, DocSeen.seen.Unseen(seen, List.append(&2, Ds.At, xs, ys))), 40n) == True{} : Bool}) -> {Nat.is_le(List.length(&2, Ds.At, List.append(&2, Ds.At, Ds.unseen(seen, xs), Ds.unseen(seen, ys))), 40n) == True{} : Bool}:
  %LA.dsr.unseen_app(seen, xs, ys) : {Nat.is_le(List.length(&2, Ds.At, _), 40n) == True{} : Bool}
  LA.dsr.le_unseen(seen, List.append(&2, Ds.At, xs, ys), 40n, True{}, few)

def DocSeen.reject_joins(seen, xs, ys, few):
  +A = Ds.unseen(seen, xs)
  +B = Ds.unseen(seen, ys)
  +hf = rj.hf(seen, xs, ys, few)
  +e = Equal.sym(List<&2, Ds.At>, Ds.unseen(seen, List.append(&2, Ds.At, xs, ys)), List.append(&2, Ds.At, A, B), LA.dsr.unseen_app(seen, xs, ys))
  +s = {%e : {Ds.shows(List.take(&2, Ds.At, _, 40n)) == List.append(&2, Ds.Show, Ds.shows(List.take(&2, Ds.At, A, 40n)), Ds.shows(List.take(&2, Ds.At, B, 40n))) : List<&2, Ds.Show>}; rj.shown(A, B, hf) : {Ds.shows(List.take(&2, Ds.At, Ds.unseen(seen, List.append(&2, Ds.At, xs, ys)), 40n)) == List.append(&2, Ds.Show, Ds.shows(List.take(&2, Ds.At, A, 40n)), Ds.shows(List.take(&2, Ds.At, B, 40n))) : List<&2, Ds.Show>}}
  +w = {%e : {Ds.whole.go(Nat.is_le(List.length(&2, Ds.At, _), 40n), _) == Bool.and(Ds.whole.go(Nat.is_le(List.length(&2, Ds.At, A), 40n), A), Ds.whole.go(Nat.is_le(List.length(&2, Ds.At, B), 40n), B)) : Bool}; rj.whole(A, B, hf) : {Ds.whole.go(Nat.is_le(List.length(&2, Ds.At, Ds.unseen(seen, List.append(&2, Ds.At, xs, ys))), 40n), Ds.unseen(seen, List.append(&2, Ds.At, xs, ys))) == Bool.and(Ds.whole.go(Nat.is_le(List.length(&2, Ds.At, A), 40n), A), Ds.whole.go(Nat.is_le(List.length(&2, Ds.At, B), 40n), B)) : Bool}}
  (s, w)
