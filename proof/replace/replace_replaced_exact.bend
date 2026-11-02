# eukhe: the proof of LAW replace_replaced_exact

import Base
import ../../bend/replace.bend as Rp
import ../../laws/replace.bend as Replace
import ./base.bend as LA

# (D1) replace_replaced_exact: by induction on the starts, from any daemon:
# each start counts as rp_replaces counts it, and leaves rp_after's daemon
# (LA.st.after_exact)

def st.bump_put(r: Rp.Rel, k: Rp.Caller) -> {Rp.replaces.put(Rp.verdict.put(r, k)) == Replace.rp_bump(Replace.verdict_spec(r, k)) : Nat}:
  match r k:
    case Rp.Same{} Rp.Interactive{}:
      {==}
    case Rp.Same{} Rp.Background{}:
      {==}
    case Rp.Older{} Rp.Interactive{}:
      {==}
    case Rp.Older{} Rp.Background{}:
      {==}
    case Rp.Newer{} Rp.Interactive{}:
      {==}
    case Rp.Newer{} Rp.Background{}:
      {==}
    case Rp.Other{} Rp.Interactive{}:
      {==}
    case Rp.Other{} Rp.Background{}:
      {==}

def st.replaces_exact(s: Rp.Start, d: Maybe<&2, Rp.Build>) -> {Rp.replaces(s, d) == Replace.rp_replaces(s, d) : Nat}:
  match s:
    case Rp.Start{+c, +k}:
      match d:
        case None{}:
          {==}
        case Some{+b}:
          %LA.rk.relation_exact(c, b) : {Rp.replaces.put(Rp.verdict.put(Rp.relation(c, b), k)) == Replace.rp_bump(Replace.verdict_spec(_, k)) : Nat}
          st.bump_put(Rp.relation(c, b), k)

def st.count_go(ss: List<&2, Rp.Start>, +d: Maybe<&2, Rp.Build>) -> {Rp.replaced.go(ss, d) == Replace.rp_count.go(ss, d) : Nat}:
  match ss:
    case Nil{}:
      {==}
    case +s <> rest:
      %st.replaces_exact(s, d) : {Nat.add(Rp.replaces(s, d), Rp.replaced.go(rest, Some{Rp.after(s, d)})) == Nat.add(_, Replace.rp_count.go(rest, Some{Replace.rp_after(s, d)})) : Nat}
      %LA.st.after_exact(s, d) : {Nat.add(Rp.replaces(s, d), Rp.replaced.go(rest, Some{Rp.after(s, d)})) == Nat.add(Rp.replaces(s, d), Replace.rp_count.go(rest, Some{_})) : Nat}
      %st.count_go(rest, Some{Rp.after(s, d)}) : {Nat.add(Rp.replaces(s, d), Rp.replaced.go(rest, Some{Rp.after(s, d)})) == Nat.add(Rp.replaces(s, d), _) : Nat}
      {==}

def Replace.replace_replaced_exact(ss):
  st.count_go(ss, None{})
