# eukhe: the proof of LAW replace_never_downgrades

import Base
import ../../bend/replace.bend as Rp
import ../../LAWS.bend as Laws
import ../base.bend as L
import ./base.bend as LA

# (D1) replace_never_downgrades
# -----------------------------

def pr.nb_self(-S: List<&2, Rp.Build>, +b: Rp.Build, inv: {Rp.not_below(S, b) == True{} : Bool}) -> {Rp.not_below(b <> S, b) == True{} : Bool}:
  %Equal.sym(Bool, Rp.lt(Rp.Build.rank(b), Rp.Build.rank(b)), False{}, LA.pr.lt_irrefl(Rp.Build.rank(b))) : {Bool.and(Bool.not(_), Rp.not_below(S, b)) == True{} : Bool}
  inv

def pr.lift.put(p: Bool, q: Bool, rb: List<&2, Nat>, rc: List<&2, Nat>, re: List<&2, Nat>, -t1: Bool, -t2: Bool, ep: {Rp.lt(rb, re) == p : Bool}, eq: {Rp.lt(rc, re) == q : Bool}, h: {Rp.lt(rb, rc) == True{} : Bool}, inv: {Bool.and(Bool.not(p), t1) == True{} : Bool}, ih: {t1 == True{} : Bool} -> {t2 == True{} : Bool}) -> {Bool.and(Bool.not(q), t2) == True{} : Bool}:
  match p q:
    case True{} True{}:
      L.supervisor.ps.absurdF({Bool.and(Bool.not(True{}), t2) == True{} : Bool}, inv)
    case True{} False{}:
      L.supervisor.ps.absurdF({Bool.and(Bool.not(False{}), t2) == True{} : Bool}, inv)
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
          L.supervisor.ps.and_t(Rp.not_below(b <> S, Rp.after.put(Rp.verdict(c, b, k), c, b)), Rp.never_back.go(Rp.trace.go(rest, Some{Rp.after.put(Rp.verdict(c, b, k), c, b)}), Rp.after.put(Rp.verdict(c, b, k), c, b) <> (b <> S)), pr.next.put(Rp.verdict(c, b, k), c, b, k, S, {==}, inv), pr.rising(rest, Rp.after.put(Rp.verdict(c, b, k), c, b), b <> S, pr.next.put(Rp.verdict(c, b, k), c, b, k, S, {==}, inv)))

def pr.replace_never_downgrades(ss: List<&2, Rp.Start>) -> {Rp.never_back(Rp.daemons(ss)) == True{} : Bool}:
  match ss:
    case Nil{}:
      {==}
    case s <> rest:
      match s:
        case Rp.Start{+c, k}:
          pr.rising(rest, c, Nil{}, {==})

def Laws.replace_never_downgrades(ss):
  pr.replace_never_downgrades(ss)
