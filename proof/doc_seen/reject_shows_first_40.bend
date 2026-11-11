# eukhe: the proof of LAW reject_shows_first_40
#
# PROOF: the unseen anchors of xs then ys are those of xs (40 of them)
# then those of ys; the first 40 of that list are those of xs, which are
# their own first 40.

import Base
import ../../bend/doc_seen.bend as Ds
import ../../laws/doc_seen.bend as DocSeen
import ./base.bend as LA

def DocSeen.reject_shows_first_40(seen, xs, ys, full):
  +A = Ds.unseen(seen, xs)
  +B = Ds.unseen(seen, ys)
  +hl = LA.dsr.len_unseen(seen, xs, 40n, full)
  %Equal.sym(List<&2, Ds.At>, Ds.unseen(seen, List.append(&2, Ds.At, xs, ys)), List.append(&2, Ds.At, A, B), LA.dsr.unseen_app(seen, xs, ys)) : {Ds.shows(List.take(&2, Ds.At, _, 40n)) == Ds.shows(List.take(&2, Ds.At, A, 40n)) : List<&2, Ds.Show>}
  %hl : {Ds.shows(List.take(&2, Ds.At, List.append(&2, Ds.At, A, B), _)) == Ds.shows(List.take(&2, Ds.At, A, _)) : List<&2, Ds.Show>}
  %Equal.sym(List<&2, Ds.At>, List.take(&2, Ds.At, List.append(&2, Ds.At, A, B), List.length(&2, Ds.At, A)), A, LA.dsr.take_len(A, B)) : {Ds.shows(_) == Ds.shows(List.take(&2, Ds.At, A, List.length(&2, Ds.At, A))) : List<&2, Ds.Show>}
  %Equal.sym(List<&2, Ds.At>, List.take(&2, Ds.At, A, List.length(&2, Ds.At, A)), A, LA.dsr.take_self(A)) : {Ds.shows(A) == Ds.shows(_) : List<&2, Ds.Show>}
  {==}
