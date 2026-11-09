# eukhe: the proof of LAW path_real_chain_past
#
# PROOF: in a chain of K links, the first link at /1+i (i < K) is the one
# to /i (pch.find_some); from /f+1+j with f links left, each link is
# followed with one link fewer (pcp.walk, by induction on f), until no
# link is left at /1+j: the link there is kept as a name and the path
# loops. 41 + j is 40 + (1 + j).

import Base
import ../../bend/path_policy.bend as Pp
import ../../bend/tools.bend as Tl
import ../../laws/path_policy/policy.bend as PathPolicy
import ./path_real_chain_within.bend as PPathRealChainWithin

# from /f+1+j with f links left, a chain of K >= f+1+j links loops at /1+j
def pcp.walk(f: Nat, +j: Nat, +K: Nat, +le: {Nat.is_le(Nat.add(f, 1n+j), K) == True{} : Bool}) -> {Pp.go(f, [Tl.Name{Nat.add(f, 1n+j)}], PathPolicy.pp_chain(K), Nil{}, False{}, Pp.link.find(PathPolicy.pp_chain(K), [Nat.add(f, 1n+j)])) == Pp.Res{[1n+j], True{}} : Pp.Res}:
  match f:
    case 0n:
      +ea = Equal.sym(Maybe<&2, Pp.Link>, Pp.link.find(PathPolicy.pp_chain(K), [1n+j]), Some{Pp.Link{[1n+j], True{}, [Tl.Name{j}]}}, PPathRealChainWithin.pch.find_some(K, j)(le))
      %ea : {Pp.go(0n, [Tl.Name{1n+j}], PathPolicy.pp_chain(K), Nil{}, False{}, _) == Pp.Res{[1n+j], True{}} : Pp.Res}
      {==}
    case 1n++g:
      +ea = Equal.sym(Maybe<&2, Pp.Link>, Pp.link.find(PathPolicy.pp_chain(K), [1n+Nat.add(g, 1n+j)]), Some{Pp.Link{[1n+Nat.add(g, 1n+j)], True{}, [Tl.Name{Nat.add(g, 1n+j)}]}}, PPathRealChainWithin.pch.find_some(K, Nat.add(g, 1n+j))(le))
      %ea : {Pp.go(1n+g, [Tl.Name{1n+Nat.add(g, 1n+j)}], PathPolicy.pp_chain(K), Nil{}, False{}, _) == Pp.Res{[1n+j], True{}} : Pp.Res}
      pcp.walk(g, j, K, PPathRealChainWithin.pch.le_pred(Nat.add(g, 1n+j), K, le))

def PathPolicy.path_real_chain_past(j):
  pcp.walk(40n, j, Nat.add(41n, j), PPathRealChainWithin.pch.le_refl(Nat.add(41n, j)))
