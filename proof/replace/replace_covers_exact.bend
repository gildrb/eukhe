# eukhe: the proof of LAW replace_covers_exact

import Base
import ../../bend/replace.bend as Rp
import ../../laws/replace.bend as Replace
import ./base.bend as LA

# (D1) replace_covers_exact: by induction on the ranks, the builds of bs
# and the starts

def st.ranks_eq(xs: List<&2, Nat>, ys: List<&2, Nat>) -> {Rp.ranks_eq(xs, ys) == Replace.rp_ranks_eq(xs, ys) : Bool}:
  match xs ys:
    case Nil{} Nil{}:
      {==}
    case Nil{} y <> yr:
      {==}
    case x <> xr Nil{}:
      {==}
    case +x <> +xr +y <> +yr:
      %st.ranks_eq(xr, yr) : {Bool.and(Nat.is_eq(x, y), Rp.ranks_eq(xr, yr)) == Bool.and(Nat.is_eq(x, y), _) : Bool}
      {==}

def st.build_eq(a: Rp.Build, b: Rp.Build) -> {Rp.build_eq(a, b) == Replace.rp_same_build(a, b) : Bool}:
  match a b:
    case Rp.Build{+ra, +ia} Rp.Build{+rb, +ib}:
      %st.ranks_eq(ra, rb) : {Bool.and(String.eq(ia, ib), Rp.ranks_eq(ra, rb)) == Bool.and(String.eq(ia, ib), _) : Bool}
      {==}

def st.has(bs: List<&2, Rp.Build>, +b: Rp.Build) -> {Rp.has(bs, b) == Replace.rp_has(bs, b) : Bool}:
  match bs:
    case Nil{}:
      {==}
    case +e <> t:
      %st.build_eq(e, b) : {Bool.or(Rp.build_eq(e, b), Rp.has(t, b)) == Bool.or(_, Replace.rp_has(t, b)) : Bool}
      %st.has(t, b) : {Bool.or(Rp.build_eq(e, b), Rp.has(t, b)) == Bool.or(Rp.build_eq(e, b), _) : Bool}
      {==}

def st.covers(+bs: List<&2, Rp.Build>, ss: List<&2, Rp.Start>) -> {Rp.covers(bs, ss) == Replace.rp_covers(bs, ss) : Bool}:
  match ss:
    case Nil{}:
      {==}
    case s <> rest:
      match s:
        case Rp.Start{+c, k}:
          %st.has(bs, c) : {Bool.and(Rp.has(bs, c), Rp.covers(bs, rest)) == Bool.and(_, Replace.rp_covers(bs, rest)) : Bool}
          %st.covers(bs, rest) : {Bool.and(Rp.has(bs, c), Rp.covers(bs, rest)) == Bool.and(Rp.has(bs, c), _) : Bool}
          {==}

def Replace.replace_covers_exact(bs, ss):
  st.covers(bs, ss)
