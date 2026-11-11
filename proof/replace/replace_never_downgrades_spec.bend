# eukhe: the proof of LAW replace_never_downgrades_spec
#
# The model's never_back keeps the builds seen, the spec its ranks
# (rnb.ranks); a build's rank is the same both ways (rnb.rank) and the
# model's order is rank_below (rk.lt_spec), so not_below is rp_not_below
# (rnb.not_below) and never_back.go is rp_never_back_spec.go for any builds
# seen (rnb.go). The model's never_back holds of every trace: a start
# replaces the daemon only with a build of a higher rank
# (`pr.replace_older`), and the rank order is transitive (`pr.lt_trans`),
# so the daemon after a start is below no daemon before it (`pr.rising`).

import Base
import ../../bend/replace.bend as Rp
import ../../laws/replace.bend as Replace
import ../base/bool.bend as LBool
import ../base/logic/logic.bend as LLogicLogic
import ./base.bend as LA

# The spec's order is the model's never_back
# ------------------------------------------

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
      %LA.rk.lt_spec(Rp.Build.rank(b), Rp.Build.rank(e)) : {Rp.not_below(e <> t, b) == Bool.and(Bool.not(_), Rp.not_below(t, b)) : Bool}
      {==}

def rnb.go(xs: List<&2, Rp.Build>, +seen: List<&2, Rp.Build>) -> {Rp.never_back.go(xs, seen) == Replace.rp_never_back_spec.go(xs, rnb.ranks(seen)) : Bool}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +t:
      %rnb.go(t, x <> seen) : {Rp.never_back.go(x <> t, seen) == Bool.and(Replace.rp_rank_not_below(rnb.ranks(seen), Replace.rp_rank_of(x)), _) : Bool}
      %rnb.not_below(seen, x) : {Rp.never_back.go(x <> t, seen) == Bool.and(_, Rp.never_back.go(t, x <> seen)) : Bool}
      {==}

# The model's never_back holds of every trace
# -------------------------------------------

def pr.nb_self(-S: List<&2, Rp.Build>, +b: Rp.Build, inv: {Rp.not_below(S, b) == True{} : Bool}) -> {Rp.not_below(b <> S, b) == True{} : Bool}:
  %Equal.sym(Bool, Rp.lt(Rp.Build.rank(b), Rp.Build.rank(b)), False{}, LA.pr.lt_irrefl(Rp.Build.rank(b))) : {Bool.and(Bool.not(_), Rp.not_below(S, b)) == True{} : Bool}
  inv

def pr.lift.put(p: Bool, q: Bool, rb: List<&2, Nat>, rc: List<&2, Nat>, re: List<&2, Nat>, -t1: Bool, -t2: Bool, ep: {Rp.lt(rb, re) == p : Bool}, eq: {Rp.lt(rc, re) == q : Bool}, h: {Rp.lt(rb, rc) == True{} : Bool}, inv: {Bool.and(Bool.not(p), t1) == True{} : Bool}, ih: {t1 == True{} : Bool} -> {t2 == True{} : Bool}) -> {Bool.and(Bool.not(q), t2) == True{} : Bool}:
  match p q:
    case True{} True{}:
      LLogicLogic.supervisor.ps.absurdF({Bool.and(Bool.not(True{}), t2) == True{} : Bool}, inv)
    case True{} False{}:
      LLogicLogic.supervisor.ps.absurdF({Bool.and(Bool.not(False{}), t2) == True{} : Bool}, inv)
    case False{} True{}:
      LA.pr.clash({Bool.and(Bool.not(True{}), t2) == True{} : Bool}, Rp.lt(rb, re), LA.pr.lt_trans(rb, rc, re, h, eq), ep)
    case False{} False{}:
      ih(inv)

# b below none of S and c above b: c below none of S
def pr.lift(S: List<&2, Rp.Build>, +b: Rp.Build, +c: Rp.Build, +h: {Rp.lt(Rp.Build.rank(b), Rp.Build.rank(c)) == True{} : Bool}, inv: {Rp.not_below(S, b) == True{} : Bool}) -> {Rp.not_below(S, c) == True{} : Bool}:
  match S:
    case Nil{}:
      {==}
    case +e <> +t:
      pr.lift.put(Rp.lt(Rp.Build.rank(b), Rp.Build.rank(e)), Rp.lt(Rp.Build.rank(c), Rp.Build.rank(e)), Rp.Build.rank(b), Rp.Build.rank(c), Rp.Build.rank(e), Rp.not_below(t, b), Rp.not_below(t, c), {==}, {==}, h, inv, i => pr.lift(t, b, c, h, i))

def pr.next.put(v: Rp.Verdict, +c: Rp.Build, +b: Rp.Build, -k: Rp.Caller, +S: List<&2, Rp.Build>, ev: {Rp.verdict(c, b, k) == v : Rp.Verdict}, inv: {Rp.not_below(S, b) == True{} : Bool}) -> {Rp.not_below(b <> S, Rp.after.put(v, c, b)) == True{} : Bool}:
  match v:
    case Rp.Replace{}:
      pr.lift(b <> S, b, c, LA.pr.replace_older(c, b, k, ev), pr.nb_self(S, b, inv))
    case Rp.Keep{r}:
      pr.nb_self(S, b, inv)

# from the daemon b, below none of S, no daemon goes back
def pr.rising(ss: List<&2, Rp.Start>, +b: Rp.Build, +S: List<&2, Rp.Build>, +inv: {Rp.not_below(S, b) == True{} : Bool}) -> {Rp.never_back.go(Rp.trace.go(ss, Some{b}), b <> S) == True{} : Bool}:
  match ss:
    case Nil{}:
      {==}
    case s <> +rest:
      match s:
        case Rp.Start{+c, +k}:
          LBool.supervisor.ps.and_t(Rp.not_below(b <> S, Rp.after.put(Rp.verdict(c, b, k), c, b)), Rp.never_back.go(Rp.trace.go(rest, Some{Rp.after.put(Rp.verdict(c, b, k), c, b)}), Rp.after.put(Rp.verdict(c, b, k), c, b) <> (b <> S)), pr.next.put(Rp.verdict(c, b, k), c, b, k, S, {==}, inv), pr.rising(rest, Rp.after.put(Rp.verdict(c, b, k), c, b), b <> S, pr.next.put(Rp.verdict(c, b, k), c, b, k, S, {==}, inv)))

def pr.never_back_daemons(ss: List<&2, Rp.Start>) -> {Rp.never_back(Rp.daemons(ss)) == True{} : Bool}:
  match ss:
    case Nil{}:
      {==}
    case s <> rest:
      match s:
        case Rp.Start{+c, k}:
          pr.rising(rest, c, Nil{}, {==})

def rnd.go(+ss: List<&2, Rp.Start>) -> {Replace.rp_never_back_spec(Rp.daemons(ss)) == True{} : Bool}:
  %rnb.go(Rp.daemons(ss), Nil{}) : {_ == True{} : Bool}
  pr.never_back_daemons(ss)

def Replace.replace_never_downgrades_spec(ss):
  rnd.go(ss)
