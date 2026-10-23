# eukhe: the proof of LAW edit_marks_whole_reveal

import Base
import ../../bend/doc_seen.bend as Ds
import ../../LAWS.bend as Laws
import ./base.bend as LA

def pv.points_eq(xs: List<&2, Nat>) -> {Ds.points(xs) == Laws.seen.Points(xs) : List<&2, Ds.Iv>}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +rest:
      %pv.points_eq(rest) : {Ds.Iv{x, x} <> Ds.points(rest) == Ds.Iv{x, x} <> _ : List<&2, Ds.Iv>}
      {==}

def pv.reveal_after(+u: List<&2, Nat>, +seen: List<&2, Ds.Iv>, b: Bool) -> {Ds.reveal(u, seen, b) == Laws.seen.After.go(b, Laws.seen.Points(u), seen) : List<&2, Ds.Iv>}:
  match b:
    case True{}:
      %pv.points_eq(u) : {List.append(&2, Ds.Iv, Ds.points(u), seen) == List.append(&2, Ds.Iv, _, seen) : List<&2, Ds.Iv>}
      {==}
    case False{}:
      {==}

def pv.after_go(+seen: List<&2, Ds.Iv>, +u: List<&2, Ds.At>) -> {Ds.Step.seen(Ds.edit.go(seen, Ds.check.go(u))) == Laws.seen.After(seen, u) : List<&2, Ds.Iv>}:
  match u:
    case Nil{}:
      {==}
    case +a <> +rest:
      +le = Nat.is_le(List.length(&2, Ds.At, a <> rest), Ds.cap)
      %LA.pv.whole_eq(le, a <> rest) : {Ds.reveal(Ds.lines(a <> rest), seen, Ds.whole.go(le, a <> rest)) == Laws.seen.After.go(_, Laws.seen.Points(Ds.lines(a <> rest)), seen) : List<&2, Ds.Iv>}
      pv.reveal_after(Ds.lines(a <> rest), seen, Ds.whole.go(le, a <> rest))

def Laws.edit_marks_whole_reveal(seen, ats):
  %LA.pv.unseen_eq(seen, ats) : {Ds.Step.seen(Ds.edit(seen, ats)) == Laws.seen.After(seen, _) : List<&2, Ds.Iv>}
  pv.after_go(seen, Ds.unseen(seen, ats))
