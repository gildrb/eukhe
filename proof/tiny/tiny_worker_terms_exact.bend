# eukhe: the proof of LAW tiny_worker_terms_exact
#
# PROOF: each term is the same recursion as its spec, by induction on the
# events (W.tag: a case per worker).

import Base
import ../../bend/tiny.bend as Tn
import ../../laws/tiny/pick.bend as Tiny

def tw.needs(es: List<&2, Tn.Ev>) -> {Tn.needs(es) == Tiny.sp_needs(es) : Nat}:
  match es:
    case Nil{}:
      {==}
    case e <> rest:
      match e:
        case Tn.Need{p, t}:
          %tw.needs(rest) : {1n+Tn.needs(rest) == 1n+_ : Nat}
          {==}
        case Tn.Gone{}:
          tw.needs(rest)

def tw.last(es: List<&2, Tn.Ev>, m: Maybe<&2, Nat>) -> {Tn.last_tag(es, m) == Tiny.sp_last_tag(es, m) : Maybe<&2, Nat>}:
  match es:
    case Nil{}:
      {==}
    case e <> rest:
      match e:
        case Tn.Need{p, t}:
          tw.last(rest, Some{t})
        case Tn.Gone{}:
          tw.last(rest, None{})

def tw.tag(w: Tn.W) -> {Tn.W.tag(w) == Tiny.sp_wtag(w) : Maybe<&2, Nat>}:
  match w:
    case Tn.NoWorker{}:
      {==}
    case Tn.Worker{o, t}:
      {==}

def Tiny.tiny_worker_terms_exact(es, m, w):
  (tw.needs(es), (tw.last(es, m), tw.tag(w)))
