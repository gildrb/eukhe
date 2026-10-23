# eukhe: the proof of LAW edit_only_seen_lines

import Base
import ../../bend/doc_seen.bend as Ds
import ../../laws/doc_seen.bend as DocSeen
import ./base.bend as LA

def pv.LD(xs: List<&2, Nat>, A: Type) -> Type:
  match xs:
    case Nil{}:
      A
    case x <> rest:
      Unit

def pv.cons_nil(-A: Type, +a: Nat, u: List<&2, Nat>, e: {a <> u == Nil{} : List<&2, Nat>}) -> A:
  %e : pv.LD(_, A)
  Unit{}

def pv.AD(xs: List<&2, Ds.At>, A: Type) -> Type:
  match xs:
    case Nil{}:
      A
    case x <> rest:
      Unit

# An applied edit: its anchors are seen
# -------------------------------------

def pv.applied_nil(+seen: List<&2, Ds.Iv>, u: List<&2, Nat>, w: Bool, h: {Ds.Step.applied(Ds.edit.fin(seen, u, w)) == True{} : Bool}) -> {u == Nil{} : List<&2, Nat>}:
  match u:
    case Nil{}:
      {==}
    case x <> rest:
      LA.documents.pv.absurd({x <> rest == Nil{} : List<&2, Nat>}, Equal.sym(Bool, False{}, True{}, h))

def pv.lines_nil(us: List<&2, Ds.At>, h: {Ds.lines(us) == Nil{} : List<&2, Nat>}) -> {us == Nil{} : List<&2, Ds.At>}:
  match us:
    case Nil{}:
      {==}
    case a <> rest:
      pv.cons_nil({a <> rest == Nil{} : List<&2, Ds.At>}, Ds.At.line(a), Ds.lines(rest), h)

def pv.put_nil_seen(+a: Ds.At, u: List<&2, Ds.At>, b: Bool, h: {Ds.unseen.put(a, u, b) == Nil{} : List<&2, Ds.At>}) -> {b == True{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      %h : pv.AD(_, {False{} == True{} : Bool})
      Unit{}

def pv.put_nil_rest(+a: Ds.At, u: List<&2, Ds.At>, b: Bool, h: {Ds.unseen.put(a, u, b) == Nil{} : List<&2, Ds.At>}) -> {u == Nil{} : List<&2, Ds.At>}:
  match b:
    case True{}:
      h
    case False{}:
      %h : pv.AD(_, {u == Nil{} : List<&2, Ds.At>})
      Unit{}

def pv.nil_subset(+seen: List<&2, Ds.Iv>, ats: List<&2, Ds.At>, +h: {Ds.unseen(seen, ats) == Nil{} : List<&2, Ds.At>}) -> {DocSeen.seen.Sub(Ds.lines(ats), seen) == True{} : Bool}:
  match ats:
    case Nil{}:
      {==}
    case +a <> +rest:
      +u = Ds.unseen(seen, rest)
      +b = Ds.mem(Ds.At.line(a), seen)
      LA.pv.and_tt(DocSeen.seen.In(Ds.At.line(a), seen), DocSeen.seen.Sub(Ds.lines(rest), seen), LA.pv.in_of_mem(Ds.At.line(a), seen, pv.put_nil_seen(a, u, b, h)), pv.nil_subset(seen, rest, pv.put_nil_rest(a, u, b, h)))

def pv.edit_only_seen_lines(+seen: List<&2, Ds.Iv>, +ats: List<&2, Ds.At>, ok: {Ds.Step.applied(Ds.edit(seen, ats)) == True{} : Bool}) -> {DocSeen.seen.Sub(Ds.lines(ats), seen) == True{} : Bool}:
  +u = Ds.unseen(seen, ats)
  pv.nil_subset(seen, ats, pv.lines_nil(u, pv.applied_nil(seen, Ds.lines(u), Ds.Check.whole(Ds.check.go(u)), ok)))

# (F11) Seen lines

def DocSeen.edit_only_seen_lines(seen, ats, ok):
  pv.edit_only_seen_lines(seen, ats, ok)
