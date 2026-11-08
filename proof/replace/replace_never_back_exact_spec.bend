# eukhe: the proof of LAW replace_never_back_exact_spec
#
# PROOF of LAW replace_never_back_exact_spec: the model keeps the builds seen,
# the spec their ranks (rnb.ranks); a build's rank is the same both ways
# (rnb.rank) and the model's order is rank_below (rk.lt_spec), so
# not_below is rp_not_below (rnb.not_below) and never_back.go is
# rp_never_back_spec.go for any builds seen (rnb.go).

import Base
import ../../bend/replace.bend as Rp
import ../../laws/replace.bend as Replace
import ./base.bend as LAReplace

def rnb.rank(b: Rp.Build) -> {Rp.Build.rank(b) == Replace.rp_rank_of(b) : List<&2, Nat>}:
  match b:
    case Rp.Build{r, i}:
      {==}

# the ranks of builds
def rnb.ranks(bs: List<&2, Rp.Build>) -> List<&2, List<&2, Nat>>:
  match bs:
    case Nil{}:
      Nil{}
    case e <> t:
      Replace.rp_rank_of(e) <> rnb.ranks(t)

def rnb.not_below(seen: List<&2, Rp.Build>, +b: Rp.Build) -> {Rp.not_below(seen, b) == Replace.rp_rank_not_below(rnb.ranks(seen), Replace.rp_rank_of(b)) : Bool}:
  match seen:
    case Nil{}:
      {==}
    case +e <> +t:
      %rnb.not_below(t, b) : {Rp.not_below(e <> t, b) == Bool.and(Bool.not(Replace.rank_below(Replace.rp_rank_of(b), Replace.rp_rank_of(e))), _) : Bool}
      %rnb.rank(b) : {Rp.not_below(e <> t, b) == Bool.and(Bool.not(Replace.rank_below(_, Replace.rp_rank_of(e))), Rp.not_below(t, b)) : Bool}
      %rnb.rank(e) : {Rp.not_below(e <> t, b) == Bool.and(Bool.not(Replace.rank_below(Rp.Build.rank(b), _)), Rp.not_below(t, b)) : Bool}
      %LAReplace.rk.lt_spec(Rp.Build.rank(b), Rp.Build.rank(e)) : {Rp.not_below(e <> t, b) == Bool.and(Bool.not(_), Rp.not_below(t, b)) : Bool}
      {==}

def rnb.go(xs: List<&2, Rp.Build>, +seen: List<&2, Rp.Build>) -> {Rp.never_back.go(xs, seen) == Replace.rp_never_back_spec.go(xs, rnb.ranks(seen)) : Bool}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +t:
      %rnb.go(t, x <> seen) : {Rp.never_back.go(x <> t, seen) == Bool.and(Replace.rp_rank_not_below(rnb.ranks(seen), Replace.rp_rank_of(x)), _) : Bool}
      %rnb.not_below(seen, x) : {Rp.never_back.go(x <> t, seen) == Bool.and(_, Rp.never_back.go(t, x <> seen)) : Bool}
      {==}

def Replace.replace_never_back_exact_spec(xs):
  rnb.go(xs, Nil{})
