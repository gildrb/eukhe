# eukhe: the proof of LAW fallback_terms_exact

import Base
import ../../bend/aux_fallback.bend as Af
import ../../laws/aux_fallback.bend as AuxFallback
import ./base/spec.bend as LX

def pft.subs(es: List<&2, Af.Ev>) -> {Af.subs(es) == AuxFallback.afs_subs(es) : List<&2, Af.Key>}:
  match es:
    case Nil{}:
      {==}
    case e <> +rest:
      match e:
        case Af.Stay{}:
          pft.subs(rest)
        case Af.Went{}:
          pft.subs(rest)
        case Af.Sub{+k}:
          %pft.subs(rest) : {k <> Af.subs(rest) == k <> _ : List<&2, Af.Key>}
          {==}
        case Af.Note{k}:
          pft.subs(rest)

def pft.notes(es: List<&2, Af.Ev>) -> {Af.notes(es) == AuxFallback.afs_notes(es) : List<&2, Af.Key>}:
  match es:
    case Nil{}:
      {==}
    case e <> +rest:
      match e:
        case Af.Stay{}:
          pft.notes(rest)
        case Af.Went{}:
          pft.notes(rest)
        case Af.Sub{k}:
          pft.notes(rest)
        case Af.Note{+k}:
          %pft.notes(rest) : {k <> Af.notes(rest) == k <> _ : List<&2, Af.Key>}
          {==}

def AuxFallback.fallback_terms_exact(ks, k, es, fs):
  (LX.pxe.shown(ks, k), (pft.subs(es), pft.notes(fs)))
