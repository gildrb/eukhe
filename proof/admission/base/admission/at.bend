# eukhe: lemmas the proofs of area admission share: admission/at
#
# Ticket k of the laws is the ticket after k others (pre ++ t <> post);
# the model reads it with Ad.get and rewrites it with Ad.put; the newest
# ticket is the last one appended.

import Base
import ../../../../bend/admission.bend as Ad
import ../../../../laws/admission.bend as Admission

# the ticket after the tickets pre is ticket length(pre)
def pat.get(pre: List<&2, Ad.Tk>, +t: Ad.Tk, +post: List<&2, Ad.Tk>) -> {Ad.get(List.append(&2, Ad.Tk, pre, t <> post), List.length(&2, Ad.Tk, pre)) == Some{t} : Maybe<&2, Ad.Tk>}:
  match pre:
    case Nil{}:
      {==}
    case h <> r:
      pat.get(r, t, post)

# the same, the other way round (a rewrite of the model's read)
def pat.got(+pre: List<&2, Ad.Tk>, +t: Ad.Tk, +post: List<&2, Ad.Tk>) -> {Some{t} == Ad.get(List.append(&2, Ad.Tk, pre, t <> post), List.length(&2, Ad.Tk, pre)) : Maybe<&2, Ad.Tk>}:
  Equal.sym(Maybe<&2, Ad.Tk>, Ad.get(List.append(&2, Ad.Tk, pre, t <> post), List.length(&2, Ad.Tk, pre)), Some{t}, pat.get(pre, t, post))

# a new status for that ticket rewrites it in place
def pat.put(pre: List<&2, Ad.Tk>, +c: Ad.Cls, +s: Ad.Sts, +post: List<&2, Ad.Tk>, +x: Ad.Sts) -> {Ad.put(List.append(&2, Ad.Tk, pre, Ad.Tk{c, s} <> post), List.length(&2, Ad.Tk, pre), x) == List.append(&2, Ad.Tk, pre, Ad.Tk{c, x} <> post) : List<&2, Ad.Tk>}:
  match pre:
    case Nil{}:
      {==}
    case h <> r:
      match h:
        case Ad.Tk{+hc, +hs}:
          %pat.put(r, c, s, post, x) : {Ad.Tk{hc, hs} <> Ad.put(List.append(&2, Ad.Tk, r, Ad.Tk{c, s} <> post), List.length(&2, Ad.Tk, r), x) == Ad.Tk{hc, hs} <> _ : List<&2, Ad.Tk>}
          {==}

def pat.last.go(r: List<&2, Ad.Tk>, a: Ad.Tk, +t: Ad.Tk) -> {Admission.adm_last.go(List.append(&2, Ad.Tk, r, [t]), a) == Some{t} : Maybe<&2, Ad.Tk>}:
  match r:
    case Nil{}:
      {==}
    case b <> v:
      pat.last.go(v, b, t)

# the newest ticket is the one appended last
def pat.last(a: List<&2, Ad.Tk>, +t: Ad.Tk) -> {Admission.adm_last(List.append(&2, Ad.Tk, a, [t])) == Some{t} : Maybe<&2, Ad.Tk>}:
  match a:
    case Nil{}:
      {==}
    case b <> v:
      pat.last.go(v, b, t)

def pat.lasted(+a: List<&2, Ad.Tk>, +t: Ad.Tk) -> {Some{t} == Admission.adm_last(List.append(&2, Ad.Tk, a, [t])) : Maybe<&2, Ad.Tk>}:
  Equal.sym(Maybe<&2, Ad.Tk>, Admission.adm_last(List.append(&2, Ad.Tk, a, [t])), Some{t}, pat.last(a, t))
