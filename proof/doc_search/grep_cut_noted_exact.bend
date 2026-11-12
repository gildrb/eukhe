# eukhe: the proof of LAW grep_cut_noted_exact
#
# PROOF: by induction on os. No entry, no notice. An entry that is not a
# shown cut file puts no notice: i is noted in the rest (the entry put
# before pre). A shown cut file j puts j first: i is j (pre empty, post
# the rest) or is noted in the rest.

import Base
import ../../bend/doc_search.bend as Sr
import ../../laws/doc_search.bend as DocSearch

def cne.BF(b: Bool, A: Type) -> Type:
  match b:
    case True{}:
      A
    case False{}:
      Unit

# False is not True: anything follows
def cne.ft(-A: Type, e: {False{} == True{} : Bool}) -> A:
  %e : cne.BF(_, A)
  Unit{}

def cne.eq_true(a: Nat, b: Nat, h: {Nat.is_eq(a, b) == True{} : Bool}) -> {a == b : Nat}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      cne.ft({0n == 1n+q : Nat}, h)
    case 1n+p 0n:
      cne.ft({1n+p == 0n : Nat}, h)
    case 1n+p 1n+q:
      %cne.eq_true(p, q, h) : {1n+p == 1n+_ : Nat}
      {==}

# os holds the shown cut file i where it says
def cne.Ex(i: Nat, os: List<&2, Sr.Out>) -> Type:
  &pre: List<&2, Sr.Out> -> &pa: Bool -> &post: List<&2, Sr.Out> -> {os == List.append(&2, Sr.Out, pre, Sr.Out{i, Sr.Shown{}, True{}, pa} <> post) : List<&2, Sr.Out>}

# noted in the rest: the entry goes before pre
def cne.cons(+o: Sr.Out, -i: Nat, -t: List<&2, Sr.Out>, r: cne.Ex(i, t)) -> cne.Ex(i, o <> t):
  (pre, r1) = r
  (pa, r2) = r1
  (post, pf) = r2
  (o <> pre, (pa, (post, Equal.cong(List<&2, Sr.Out>, List<&2, Sr.Out>, z => o <> z, t, List.append(&2, Sr.Out, pre, Sr.Out{i, Sr.Shown{}, True{}, pa} <> post), pf))))

# the shown cut file at the head is i
def cne.hit(-j: Nat, -i: Nat, -qa: Bool, -t: List<&2, Sr.Out>, e: {j == i : Nat}) -> {Sr.Out{j, Sr.Shown{}, True{}, qa} <> t == List.append(&2, Sr.Out, Nil{}, Sr.Out{i, Sr.Shown{}, True{}, qa} <> t) : List<&2, Sr.Out>}:
  %e : {Sr.Out{j, Sr.Shown{}, True{}, qa} <> t == List.append(&2, Sr.Out, Nil{}, Sr.Out{_, Sr.Shown{}, True{}, qa} <> t) : List<&2, Sr.Out>}
  {==}

def cne.step(+j: Nat, +i: Nat, +qa: Bool, q: Bool, eq: {Nat.is_eq(j, i) == q : Bool}, +t: List<&2, Sr.Out>, h: {Bool.or(q, Sr.mem(i, Sr.cuts(t))) == True{} : Bool}, ih: {Sr.mem(i, Sr.cuts(t)) == True{} : Bool} -> cne.Ex(i, t)) -> cne.Ex(i, Sr.Out{j, Sr.Shown{}, True{}, qa} <> t):
  match q:
    case True{}:
      (Nil{}, (qa, (t, cne.hit(j, i, qa, t, cne.eq_true(j, i, eq)))))
    case False{}:
      cne.cons(Sr.Out{j, Sr.Shown{}, True{}, qa}, i, t, ih(h))

def cne.go(+i: Nat, os: List<&2, Sr.Out>, h: {Sr.mem(i, Sr.cuts(os)) == True{} : Bool}) -> cne.Ex(i, os):
  match os:
    case Nil{}:
      cne.ft(cne.Ex(i, Nil{}), h)
    case o <> +t:
      match o:
        case Sr.Out{+j, c, +b, +qa}:
          match c:
            case Sr.NoMatch{}:
              cne.cons(Sr.Out{j, Sr.NoMatch{}, b, qa}, i, t, cne.go(i, t, h))
            case Sr.Shown{}:
              match b:
                case True{}:
                  cne.step(j, i, qa, Nat.is_eq(j, i), {==}, t, h, hh => cne.go(i, t, hh))
                case False{}:
                  cne.cons(Sr.Out{j, Sr.Shown{}, False{}, qa}, i, t, cne.go(i, t, h))
            case Sr.PagedOut{}:
              cne.cons(Sr.Out{j, Sr.PagedOut{}, b, qa}, i, t, cne.go(i, t, h))
            case Sr.Unsearched{}:
              cne.cons(Sr.Out{j, Sr.Unsearched{}, b, qa}, i, t, cne.go(i, t, h))
            case Sr.Skipped{+w}:
              cne.cons(Sr.Out{j, Sr.Skipped{w}, b, qa}, i, t, cne.go(i, t, h))

def DocSearch.grep_cut_noted_exact(i, os, h):
  cne.go(i, os, h)
